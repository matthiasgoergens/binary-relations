(* Automatic failure database: save the tape of a failing run, replay it
   first next time.

   Ported from Hypothesis's ExampleDatabase / Phase.reuse. Matthias
   named this as the feature that mattered most to him in practice with
   Hypothesis -- "makes subsequent runs automatically very quick" --
   which is not something reading the source tells you. That is the
   reason it jumped the queue ahead of the other mining targets, and it
   is worth recording, because the source makes it look like a
   convenience rather than the thing users notice.

   The mechanism behind "very quick": on a re-run the saved failing tape
   is replayed BEFORE generating anything. If the bug is still there it
   reproduces on call one instead of after a search. If it has been
   fixed, the entry is deleted, so a fixed bug costs one replay once and
   nothing thereafter. Both halves matter -- a database that only ever
   grows would slow runs down instead.

   On the size of the win, which is easy to understate. Measured here:

     easy bug   (sum >= 100)   107 -> 84 calls   1.3x
     harder bug (|m - n| = 1)   41 ->  2 calls  20.5x

   Neither ratio is the real number, because the ratio is not a
   constant. Replay is O(1) -- two calls, regardless -- while the search
   it replaces costs however long the bug took to find. The 20.5x came
   from a bug found in 41 calls, which is not a hard bug at all; a bug
   that surfaces after ten thousand cases gives thousands of times. So
   this is the unusual optimisation that pays MORE the worse your
   situation is, and the honest way to describe it is not a speedup
   factor but "you stop paying for the search you already did".

   tapecheck already had every piece except the plumbing: Tape has a
   versioned [serialize_image] / [deserialize_image], and the engine has
   [resume] taking an image. What was missing was doing it without the
   user pasting a tape by hand. *)


open! Base

(* What to do when a write fails -- a read-only filesystem, a full disk,
   a permissions problem.

   [Warn] is the default, deliberately. Swallowing the error silently is
   how this feature quietly stops working: the run still passes, nothing
   is persisted, and the next run is mysteriously slow again with no
   indication why. A database that is silently not saving is worse than
   no database, because you believe you have one. *)
type on_write_error =
  | Warn (* default: proceed, but say so on stderr *)
  | Silent (* proceed quietly -- for when you already know writes fail *)
  | Raise (* treat it as a hard error, e.g. in CI that expects a writable dir *)

type t =
  { dir : string
  ; replay : bool
        (* Read stored tapes and try them first. Turn off to force a
           fresh search -- e.g. to check that a bug is still findable
           from scratch, which a database otherwise hides. *)
  ; record : bool
        (* Whether to attempt writes at all. Off means not even trying,
           which is distinct from trying and failing quietly: on a
           known-read-only filesystem there is nothing to warn about. *)
  ; on_write_error : on_write_error
  ; mutable warned : bool
        (* Warn once per database, not once per failing write. A test
           suite writing on every property would otherwise produce one
           line per test. *)
  }

let create ~dir ?(replay = true) ?(record = true) ?(on_write_error = Warn) () =
  { dir; replay; record; on_write_error; warned = false }

let report_write_error t ~key (e : exn) =
  match t.on_write_error with
  | Silent -> ()
  | Raise ->
    Stdlib.failwith
      (Printf.sprintf "tapecheck: could not write failure tape for %S in %S: %s"
         key t.dir (Stdlib.Printexc.to_string e))
  | Warn ->
    if not t.warned then begin
      t.warned <- true;
      Stdlib.prerr_endline
        (Printf.sprintf
           "tapecheck: could not save the failure tape for %S in %S (%s).\n\
           \  Re-runs will not be able to replay this failure, so they stay \
            slow.\n\
           \  Pass ~record:false if that directory is intentionally \
            unwritable, or\n\
           \  ~on_write_error:Silent to suppress this."
           key t.dir (Stdlib.Printexc.to_string e));
      Stdlib.flush Stdlib.stderr
    end

(* Keys are caller-supplied test names. Sanitised because they end up as
   filenames and a test name is arbitrary text. *)
let key_to_filename (key : string) : string =
  (* Readable prefix for browsability, plus a digest of the ORIGINAL key
     for correctness. The sanitiser alone collides -- "a/b" and "a?b"
     both reduce to "a_b" -- which let one property replay, overwrite or
     delete another's failure tape.

     The digest is [Digest] (MD5, 128 bits, stdlib, no dependency), NOT
     [Hashtbl.hash]. A first attempt used [Hashtbl.hash key land
     0xFFFFFFF]: 28 bits, where a birthday collision among
     similarly-prefixed keys becomes likely around ~19k keys, and
     deliberate collisions are easy. That version reduced the collision
     probability without eliminating it, and its comment claimed to have
     made it correct, which was overclaiming. Flagged in review.

     MD5 is broken for adversarial use; test names are not an adversarial
     input, and 128 bits makes accidental collision not a practical
     concern. If that assumption ever stops holding, swap in SHA-256 --
     the shape of the code does not change. *)
  let readable =
    String.map key ~f:(fun c ->
      if Char.is_alphanum c || Char.equal c '-' || Char.equal c '_' then c
      else '_')
  in
  let readable =
    if String.length readable > 80 then String.prefix readable 80 else readable
  in
  Printf.sprintf "%s-%s" readable (Stdlib.Digest.to_hex (Stdlib.Digest.string key))

let path t ~key = Stdlib.Filename.concat t.dir (key_to_filename key)

let ensure_dir t =
  try if not (Stdlib.Sys.file_exists t.dir) then Unix.mkdir t.dir 0o755
  with Unix.Unix_error (Unix.EEXIST, _, _) -> ()

(* Read the stored tape for [key], if any. A file that fails to parse is
   treated as absent rather than fatal: the database is a cache, and a
   format change or a truncated write must never break a test run. *)
(* Entries are "<size>\n<serialized image>". The size matters: a failure
   found at generator size 40 can replay differently at size 0, and the
   caller then deletes the entry as stale. Regression files have always
   persisted "@size" for exactly this reason; the database did not, and
   replayed everything at sizes.(0).

   Entries written before this change have no header. They are still
   readable -- [None] size, and the caller falls back to its own
   default -- so an existing database keeps working rather than being
   silently discarded. *)
let split_header (s : string) : int option * string =
  match String.lsplit2 s ~on:'\n' with
  | Some (head, rest) -> (
    match Int.of_string_opt (String.strip head) with
    | Some n -> (Some n, rest)
    | None -> (None, s))
  | None -> (None, s)

let load_sized t ~key : (Tape.image * int option) option =
  if not t.replay then None
  else
  let file = path t ~key in
  if not (Stdlib.Sys.file_exists file) then None
  else begin
    (* [with_open_bin] closes on the exceptional path too. The previous
       form closed only on success, so a truncated file -- exactly the
       case the [with _ -> None] below exists to tolerate -- leaked the
       channel every time it happened. *)
    try
      Stdlib.In_channel.with_open_bin file (fun ic ->
        let n = Stdlib.in_channel_length ic in
        let raw = Stdlib.really_input_string ic n in
        let size, body = split_header raw in
        Option.map (Tape.deserialize_image body) ~f:(fun img -> (img, size)))
    with _ -> None
  end

let load t ~key : Tape.image option =
  Option.map (load_sized t ~key) ~f:fst

(* Written via a temporary file and renamed, so a crash mid-write cannot
   leave a half-written tape that the next run would silently treat as
   absent. *)
let save t ~key ?size (img : Tape.image) : unit =
  if not t.record then ()
  else
    let tmp_path = ref None in
    try
      ensure_dir t;
      let file = path t ~key in
      (* The temporary must be unique as well as same-directory.  A fixed
         [file ^ ".tmp"] let two test processes writing the same property
         truncate or rename each other's temporary file.  Same-directory
         keeps the final rename atomic without assuming [/tmp] shares a
         filesystem with the database. *)
      let tmp, oc =
        Stdlib.Filename.open_temp_file ~mode:[ Open_binary ] ~temp_dir:t.dir
          (key_to_filename key ^ ".") ".tmp"
      in
      tmp_path := Some tmp;
      (* Same reason as [load]: a disk-full or quota error during
         [output_string] or the implicit flush used to skip [close_out]
         entirely, leaking the channel into the error path. *)
      (match
         Stdlib.Out_channel.output_string oc
           (Printf.sprintf "%d\n" (Option.value size ~default:(-1)));
         Stdlib.Out_channel.output_string oc (Tape.serialize_image img);
         (* [close_out] flushes and can report a disk-full/quota error.  It
            must succeed before the rename, or a partial temporary could
            replace the last good entry. *)
         Stdlib.close_out oc
       with
       | () -> ()
       | exception e ->
         Stdlib.close_out_noerr oc;
         raise e);
      Stdlib.Sys.rename tmp file;
      tmp_path := None
    with e ->
      (* Do not leave the partial temporary behind either. *)
      Option.iter !tmp_path ~f:(fun tmp ->
        try if Stdlib.Sys.file_exists tmp then Stdlib.Sys.remove tmp
        with _ -> ());
      report_write_error t ~key e

let remove t ~key : unit =
  if not t.record then ()
  else
    try
      let file = path t ~key in
      if Stdlib.Sys.file_exists file then Stdlib.Sys.remove file
    with e -> report_write_error t ~key e
