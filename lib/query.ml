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
    two variables the answer is about. Compilation walks a path from the source
    variable to the target, composing as it goes, and any atom left over whose
    two ends are the answer's own endpoints becomes a {!Rel.Algebra.ALLEGORY.meet}.

    That second case is the interesting one, because it is how a {e cycle} gets
    written, and it produces precisely the shape {!Rel.Plan} learned to fuse:
    [meet (a >> b) c] evaluated without materialising [a >> b].

    Shapes outside that fragment — a variable of degree three, two disconnected
    components — raise {!Unsupported} with the reason. That is a real
    restriction and it is deliberately loud rather than silently producing a
    cross product. Lifting it is general conjunctive-query compilation, which
    is the natural next piece of work here.

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

let compile (f : var -> ('e, var) t) : ('e, 'e) Symbolic.t =
  let source = V 0 in
  let V target, st = f source { next = 1; atoms = [] } in
  let atoms = List.rev st.atoms in
  (* Walk from the source, consuming one atom at a time, until the target is
     reached. Each step is a composition; traversing an atom backwards is a
     converse, which the planner then pushes down to the leaf for free. *)
  let rec walk ~cur ~visited ~remaining ~term =
    if cur = target then (term, remaining)
    else
      let forward = List.find remaining ~f:(fun a -> a.src = cur && not (Set.mem visited a.dst)) in
      let backward =
        List.find remaining ~f:(fun a ->
          a.converse_ok && a.dst = cur && not (Set.mem visited a.src))
      in
      match (forward, backward) with
      | Some a, _ ->
        walk ~cur:a.dst
          ~visited:(Set.add visited a.dst)
          ~remaining:(List.filter remaining ~f:(fun b -> not (phys_equal a b)))
          ~term:Symbolic.(term >> leaf a.rel)
      | None, Some a ->
        walk ~cur:a.src
          ~visited:(Set.add visited a.src)
          ~remaining:(List.filter remaining ~f:(fun b -> not (phys_equal a b)))
          ~term:Symbolic.(term >> converse (leaf a.rel))
      | None, None ->
        raise
          (Unsupported
             (Printf.sprintf
                "no path from the source to the answer variable: variable %d has no unvisited \
                 neighbour. Disconnected queries are not supported."
                cur))
  in
  let term, leftover =
    walk ~cur:0 ~visited:(Set.singleton (module Int) 0) ~remaining:atoms ~term:Symbolic.id
  in
  (* Anything left must connect the answer's own two endpoints: that is a
     cycle, and it becomes a meet. Any other leftover is out of the fragment. *)
  List.fold leftover ~init:term ~f:(fun acc a ->
    if a.src = 0 && a.dst = target then Symbolic.meet acc (leaf a.rel)
    else if a.dst = 0 && a.src = target then Symbolic.meet acc (Symbolic.converse (leaf a.rel))
    else
      raise
        (Unsupported
           (Printf.sprintf
              "atom between variables %d and %d is neither on the path nor closing a cycle on the \
               answer; this needs general conjunctive-query compilation."
              a.src a.dst)))

let run f = Symbolic.run (Plan.optimise (compile f))
let to_string f = Symbolic.to_string (compile f)
