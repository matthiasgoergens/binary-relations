(** Layer 4: a surface with points.

    The brief's premise is "keep the points" — point-free is theory, backend and
    proofs, not the user interface. Everything above this layer is point-free,
    and writing an org-chart question in it reads like

    {[ converse (of_relation above) >> of_relation department ]}

    which is not what anyone wants to write. This layer restores the variables
    without giving up anything below it: a query written here {e compiles to a
    term in the algebra}, so the planner, the fusion rewrite and every
    interpreter still apply. The points are surface syntax; the point-free
    calculus stays the normal form underneath. That is exactly the arrangement
    the brief argues for, and the reason it is available is that a conjunctive
    query with variables and the categorical term are the same object.

    {[
      let reachable_dept =
        Query.compile (fun person ->
          let open Query in
          let* boss = step manages person in
          let* dept = step department boss in
          ret dept)
    ]}

    {2 What it supports, and what it refuses}

    A query is a set of {e atoms} — a relation between two variables — plus the
    two variables the answer is about. That is a graph, and compiling it is
    variable elimination, with one rule per operation of the algebra:

    - a non-answer variable of degree one is {b dangling}: its atom constrains
      only its neighbour, to lie in that atom's domain, so it becomes a
      coreflexive there. This is a {e semi-join}, and it is what makes the
      compilation Yannakakis-shaped rather than nested-loop.
    - a non-answer variable of degree two is a {b waypoint}: its two atoms
      contract into one by {e composition}.
    - two atoms between the same pair of variables are {b parallel} and merge
      by {e meet} — which is how a cycle finally resolves, producing precisely
      the shape {!Rel.Plan} learned to fuse.

    Repeating these reduces any series-parallel query graph to a single edge
    between the answer variables. What survives is a core in which every
    non-answer variable has degree three or more; that genuinely needs
    tabulation ([fork]) and raises {!Unsupported} rather than being guessed at.
    A disconnected query does too, since a cross product is not representable
    without a universal relation.

    {2 One element type}

    Atoms are [('e, 'e) Relation.t]: a query ranges over a single element type.
    That covers the confirmed business case — graphs, org charts,
    reachability — and keeps variables monomorphic, which is what makes the
    binding operators readable. A heterogeneous version needs the variables to
    carry their own types, and with them the type-level machinery the binary
    framing exists to avoid; it is not obviously worth it. *)

open! Base

exception Unsupported of string

type var = V of int

type 'e atom = {
  src : int;
  rel : ('e, 'e) Relation.t;
  dst : int;
  converse_ok : bool;
      (** whether this atom may be traversed backwards; always true here, kept
          explicit because a directed-only atom is the obvious next feature *)
}

type 'e state = { next : int; atoms : 'e atom list }
type ('e, 'a) t = 'e state -> 'a * 'e state

let return x st = (x, st)
let ( let* ) m f st = let x, st = m st in f x st
let ( >>= ) m f = ( let* ) m f
let map m ~f = ( let* ) m (fun x -> return (f x))
let ret v = return v

let fresh st = (V st.next, { st with next = st.next + 1 })

let atom rel (V s) (V d) st =
  ((), { st with atoms = { src = s; rel; dst = d; converse_ok = true } :: st.atoms })

(** Follow a relation from a variable to a fresh one. The workhorse. *)
let step rel v =
  let* w = fresh in
  let* () = atom rel v w in
  return w

(** Follow a relation backwards. [converse] is free at a leaf, so this costs
    nothing that the forward direction does not. *)
let back rel v =
  let* w = fresh in
  let* () = atom rel w v in
  return w

(** Constrain two already-bound variables to be related. This is how a cycle is
    written, and it is what compiles to a meet. *)
let constrain rel a b = atom rel a b

(* ------------------------------------------------------------------ *)

let leaf r = Symbolic.of_relation r

(* ------------------------------------------------------------------ *)
(* Compilation: variable elimination over the query graph               *)
(* ------------------------------------------------------------------ *)

(* A query over binary atoms is a graph: vertices are variables, edges are
   relations, and the answer is a pair of vertices. Compiling it to the algebra
   is variable elimination, and for binary atoms three rules suffice, each of
   which is one operation of the algebra:

     - a variable of degree 1 that is not an answer variable is DANGLING. Its
       one atom constrains only its neighbour, to lie in that atom's domain, so
       it becomes a coreflexive there and disappears. This is a semi-join, and
       it is what makes the compilation Yannakakis-shaped rather than
       nested-loop.
     - a variable of degree 2 that is not an answer variable is a WAYPOINT.
       Its two atoms contract into one by COMPOSITION.
     - two atoms between the same pair of variables are PARALLEL, and merge by
       MEET — which is how a cycle finally resolves.

   Repeating these reduces every series-parallel query graph to a single edge
   between the two answer variables. What survives is a core in which every
   non-answer variable has degree three or more; that genuinely needs
   tabulation ([fork]) and is reported rather than guessed at. *)

type 'e edge = { u : int; v : int; term : ('e, 'e) Symbolic.t }

let flip e = { u = e.v; v = e.u; term = Symbolic.converse e.term }

(* The coreflexive on a relation's domain: [meet id (r >> r°)] keeps the
   diagonal on exactly those elements the relation relates to something. *)
let dom_ t = Symbolic.(meet id (t >> converse t))

let compile (f : var -> ('e, var) t) : ('e, 'e) Symbolic.t =
  let source = V 0 in
  let V target, st = f source { next = 1; atoms = [] } in
  let edges =
    List.rev_map st.atoms ~f:(fun a -> { u = a.src; v = a.dst; term = leaf a.rel })
  in
  (* Coreflexive constraints accumulated at a variable by elimination. *)
  let guards : (int, ('e, 'e) Symbolic.t, Int.comparator_witness) Map.t ref =
    ref (Map.empty (module Int))
  in
  let add_guard x t =
    guards :=
      Map.update !guards x ~f:(function None -> t | Some prev -> Symbolic.meet prev t)
  in
  let guard_of x = Map.find !guards x in
  let apply_guard x t =
    match guard_of x with None -> t | Some g -> Symbolic.(g >> t)
  in
  let is_answer x = x = 0 || x = target in
  let incident edges x = List.filter edges ~f:(fun e -> e.u = x || e.v = x) in
  let vertices edges =
    List.dedup_and_sort ~compare:Int.compare (List.concat_map edges ~f:(fun e -> [ e.u; e.v ]))
  in
  (* Every rule below removes at least one edge — parallel merges two into
     one, dangling drops one, waypoint replaces two with one — so the
     reduction terminates in at most one step per edge. This counter is not a
     safeguard against a hard query but an invariant check on that argument,
     and it earns its keep: two of the three rules originally reported success
     while removing nothing, because they filtered on a freshly allocated
     re-oriented copy instead of the edge actually in the list. That spins
     silently and forever. *)
  let budget = ref (List.length edges + 8) in
  let rec reduce edges =
    Int.decr budget;
    if !budget <= 0 then
      failwith
        (Printf.sprintf
           "Query.compile: reduction failed to make progress, %d edges left [%s]. This is a bug \
            in the elimination rules, not an unsupported query."
           (List.length edges)
           (String.concat ~sep:"; " (List.map edges ~f:(fun e -> Printf.sprintf "%d->%d" e.u e.v))));
    (* 1. Parallel edges merge by meet. Do this first: it can only shrink the
       graph and it lowers degrees, which may unlock the other two rules. *)
    let parallel =
      List.find_map edges ~f:(fun e1 ->
        List.find_map edges ~f:(fun e2 ->
          if phys_equal e1 e2 then None
          else if e1.u = e2.u && e1.v = e2.v then Some (e1, e2, false)
          else if e1.u = e2.v && e1.v = e2.u then Some (e1, e2, true)
          else None))
    in
    match parallel with
    | Some (e1, e2, needs_flip) ->
      (* [oriented] is a fresh record when it is flipped, so the removal below
         must test against [e2] itself. Testing the flipped copy leaves the
         original in the list and [reduce] spins forever. *)
      let oriented = if needs_flip then flip e2 else e2 in
      let merged = { e1 with term = Symbolic.meet e1.term oriented.term } in
      reduce (merged :: List.filter edges ~f:(fun e -> not (phys_equal e e1 || phys_equal e e2)))
    | None -> (
      (* 2. A dangling variable becomes a coreflexive on its neighbour. *)
      let dangling =
        List.find (vertices edges) ~f:(fun x ->
          (not (is_answer x)) && List.length (incident edges x) = 1)
      in
      match dangling with
      | Some x ->
        let original = List.hd_exn (incident edges x) in
        (* Same trap as in the waypoint rule: orient into a fresh record if
           needed, but remove the original. *)
        let e = if original.v = x then original else flip original in
        (* [e] now runs neighbour -> x, so the neighbour must lie in its
           domain, after whatever constraint x already carried. *)
        add_guard e.u (dom_ (apply_guard x e.term));
        reduce (List.filter edges ~f:(fun g -> not (phys_equal g original)))
      | None -> (
        (* 3. A waypoint contracts by composition. *)
        let waypoint =
          List.find (vertices edges) ~f:(fun x ->
            (not (is_answer x)) && List.length (incident edges x) = 2)
        in
        match waypoint with
        | Some x ->
          let orig_a, orig_b =
            match incident edges x with [ p; q ] -> (p, q) | _ -> assert false
          in
          (* Orient into fresh records where needed, but remove the ORIGINALS:
             [flip] allocates, so filtering on an oriented copy removes nothing
             and the reduction spins. *)
          let a = if orig_a.v = x then orig_a else flip orig_a in
          let b = if orig_b.u = x then orig_b else flip orig_b in
          let joined =
            { u = a.u; v = b.v; term = Symbolic.(a.term >> apply_guard x b.term) }
          in
          guards := Map.remove !guards x;
          reduce
            (joined
            :: List.filter edges ~f:(fun g ->
                 not (phys_equal g orig_a || phys_equal g orig_b)))
        | None -> edges))
  in
  let edges = reduce edges in
  let leftover_vars =
    List.filter (vertices edges) ~f:(fun x -> not (is_answer x))
  in
  if not (List.is_empty leftover_vars) then
    raise
      (Unsupported
         (Printf.sprintf
            "query graph does not reduce: variable(s) %s have degree 3 or more. A core like that              needs tabulation (fork), which this compiler does not do yet."
            (String.concat ~sep:", " (List.map leftover_vars ~f:Int.to_string))));
  if Poly.equal source (V target) then
    (* The answer is a single variable: everything collapsed into guards. *)
    match guard_of 0 with Some g -> g | None -> Symbolic.id
  else
    match edges with
    | [] ->
      raise
        (Unsupported
           "the answer variables are not connected by any atom; a cross product is not \
            representable without a universal relation.")
    | first :: rest ->
      let orient e = if e.u = 0 then e else flip e in
      let combined =
        List.fold rest ~init:(orient first).term ~f:(fun acc e ->
          Symbolic.meet acc (orient e).term)
      in
      (* Guards on the answer variables themselves still have to be applied. *)
      let combined = apply_guard 0 combined in
      (match guard_of target with
       | None -> combined
       | Some g -> Symbolic.(combined >> g))

let run f = Symbolic.run (Plan.optimise (compile f))
let to_string f = Symbolic.to_string (compile f)
