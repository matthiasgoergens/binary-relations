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
    between the answer variables.

    What survives is a {e core} in which every non-answer variable has degree
    three or more. The textbook remedy is tabulation — build a relation
    carrying pairs — which needs pair-typed relations and so variables that
    carry their own types, the type-level machinery this design exists to
    avoid. So the core is handled the other way: pick such a variable, work out
    the finite set of values it can take, and solve once per value, joining the
    results. Substituting a value turns every atom at that variable into a
    coreflexive on its neighbour, so the variable disappears and elimination
    resumes. That is variable-at-a-time evaluation, what a generic join does,
    and it stays monomorphic.

    Its cost is that the compiled term grows with the candidate set, so it is
    guarded by [?max_candidates] and still refuses beyond that rather than
    emitting something enormous. Finding the candidates also means evaluating
    the atoms at that variable, which is why branching is a last resort and not
    a first move.

    A query whose answer variables end up unconnected is fine as long as both
    are constrained — the answer is then the cross product of two finite sets.
    Only a genuinely unconstrained answer variable is refused, since that would
    need a universal relation.

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

(* When elimination stalls, branch on a variable's value.

   A core in which every non-answer variable has degree three or more cannot be
   contracted by the three rules, and the textbook remedy is tabulation: build a
   relation carrying pairs. That needs pair-typed relations, and with them
   variables that carry their own types — the type-level machinery this design
   exists to avoid.

   The alternative keeps everything monomorphic: pick such a variable, work out
   the finite set of values it could take, and solve the query once per value,
   joining the results. Substituting a value turns every atom at that variable
   into a coreflexive on its neighbour, so the variable and all its edges
   disappear and elimination proceeds. This is variable-at-a-time evaluation,
   which is what a generic join does.

   The cost is that the compiled term grows with the candidate set, so it is
   guarded: past [max_candidates] the compiler still refuses rather than
   emitting something enormous. *)

let default_max_candidates = 64

(* Evaluating a partially compiled edge to find candidates is real work, and
   it is the reason branching is a last resort rather than a first move. *)
let eval_term t = Symbolic.run t

let cross xs ys =
  Relation.of_pairs
    (Set.fold xs ~init:Set.Poly.empty ~f:(fun acc a ->
       Set.fold ys ~init:acc ~f:(fun acc b -> Set.add acc (a, b))))

let compile ?(max_candidates = default_max_candidates) (f : var -> ('e, var) t) :
    ('e, 'e) Symbolic.t =
  let source = V 0 in
  let (V target), st = f source { next = 1; atoms = [] } in
  let edges0 =
    List.rev_map st.atoms ~f:(fun a -> { u = a.src; v = a.dst; term = leaf a.rel })
  in
  let is_answer x = x = 0 || x = target in
  let incident edges x = List.filter edges ~f:(fun e -> e.u = x || e.v = x) in
  let vertices edges =
    List.dedup_and_sort ~compare:Int.compare (List.concat_map edges ~f:(fun e -> [ e.u; e.v ]))
  in
  let add_guard gs x t =
    Map.update gs x ~f:(function None -> t | Some prev -> Symbolic.meet prev t)
  in
  let apply_guard gs x t = match Map.find gs x with None -> t | Some g -> Symbolic.(g >> t) in
  (* Every rule removes at least one edge, so the reduction terminates in at
     most one step per edge. The budget is an invariant check on that argument,
     not a safeguard against a hard query: two of the three rules once reported
     progress while removing nothing, because they filtered the edge list by
     [phys_equal] against a freshly allocated re-oriented copy. That spins
     silently and forever. *)
  let rec reduce edges gs budget =
    if budget <= 0 then
      failwith
        (Printf.sprintf
           "Query.compile: reduction failed to make progress, %d edges left. This is a bug in \
            the elimination rules, not an unsupported query."
           (List.length edges));
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
      let oriented = if needs_flip then flip e2 else e2 in
      let merged = { e1 with term = Symbolic.meet e1.term oriented.term } in
      reduce
        (merged :: List.filter edges ~f:(fun e -> not (phys_equal e e1 || phys_equal e e2)))
        gs (budget - 1)
    | None -> (
      let dangling =
        List.find (vertices edges) ~f:(fun x ->
          (not (is_answer x)) && List.length (incident edges x) = 1)
      in
      match dangling with
      | Some x ->
        let original = List.hd_exn (incident edges x) in
        let e = if original.v = x then original else flip original in
        let gs = add_guard gs e.u (dom_ (apply_guard gs x e.term)) in
        reduce (List.filter edges ~f:(fun g -> not (phys_equal g original))) gs (budget - 1)
      | None -> (
        let waypoint =
          List.find (vertices edges) ~f:(fun x ->
            (not (is_answer x)) && List.length (incident edges x) = 2)
        in
        match waypoint with
        | Some x ->
          let orig_a, orig_b =
            match incident edges x with [ p; q ] -> (p, q) | _ -> assert false
          in
          let a = if orig_a.v = x then orig_a else flip orig_a in
          let b = if orig_b.u = x then orig_b else flip orig_b in
          let joined =
            { u = a.u; v = b.v; term = Symbolic.(a.term >> apply_guard gs x b.term) }
          in
          reduce
            (joined
            :: List.filter edges ~f:(fun g ->
                 not (phys_equal g orig_a || phys_equal g orig_b)))
            (Map.remove gs x) (budget - 1)
        | None -> (edges, gs)))
  in
  (* The values a variable could take, from the atoms touching it. Correctness
     needs only a superset; tightness is what keeps the branching factor down. *)
  let candidates edges gs x =
    let from_edge e =
      let r = eval_term e.term in
      if e.u = x && e.v = x then Set.inter (Relation.dom r) (Relation.rng r)
      else if e.v = x then Relation.rng r
      else Relation.dom r
    in
    let sets = List.map (incident edges x) ~f:from_edge in
    let sets =
      match Map.find gs x with
      | None -> sets
      | Some g -> Relation.dom (eval_term g) :: sets
    in
    match sets with
    | [] -> None
    | first :: rest -> Some (List.fold rest ~init:first ~f:Set.inter)
  in
  let rec solve edges gs =
    let edges, gs = reduce edges gs (List.length edges + 8) in
    let leftover = List.filter (vertices edges) ~f:(fun x -> not (is_answer x)) in
    if List.is_empty leftover then finish edges gs else branch edges gs leftover
  and branch edges gs leftover =
    let scored =
      List.filter_map leftover ~f:(fun x ->
        Option.map (candidates edges gs x) ~f:(fun cs -> (x, cs)))
    in
    match
      List.min_elt scored ~compare:(fun (_, a) (_, b) ->
        Int.compare (Set.length a) (Set.length b))
    with
    | None ->
      raise (Unsupported "a variable in the irreducible core has no atoms to bound it")
    | Some (x, cs) ->
      if Set.length cs > max_candidates then
        raise
          (Unsupported
             (Printf.sprintf
                "the query has an irreducible core and branching on variable %d would need %d \
                 cases (limit %d). Raise ?max_candidates, or wait for tabulation."
                x (Set.length cs) max_candidates));
      let per_candidate =
        Set.fold cs ~init:[] ~f:(fun acc c ->
          (* Substituting a value turns each atom at [x] into a coreflexive on
             its neighbour; [x] and its edges then vanish. *)
          let ok = ref true in
          let gs' = ref (Map.remove gs x) in
          List.iter (incident edges x) ~f:(fun e ->
            let r = eval_term e.term in
            if e.u = x && e.v = x then (if not (Relation.mem r c c) then ok := false)
            else if e.v = x then
              gs' :=
                add_guard !gs' e.u
                  (Symbolic.of_relation (Relation.identity_on (Relation.preimage r c)))
            else
              gs' :=
                add_guard !gs' e.v
                  (Symbolic.of_relation (Relation.identity_on (Relation.image r c))));
          if not !ok then acc
          else
            let rest = List.filter edges ~f:(fun e -> not (e.u = x || e.v = x)) in
            solve rest !gs' :: acc)
      in
      List.fold per_candidate ~init:Symbolic.bot ~f:Symbolic.join
  and finish edges gs =
    if Poly.equal source (V target) then
      match Map.find gs 0 with Some g -> g | None -> Symbolic.id
    else
      match edges with
      | [] -> (
        (* No atom connects the answers. That is only unrepresentable if an
           answer variable is unconstrained; if both carry guards, the answer
           is the cross product of two finite sets, which is an ordinary
           relation. *)
        match (Map.find gs 0, Map.find gs target) with
        | Some g0, Some gt ->
          Symbolic.of_relation
            (cross (Relation.dom (eval_term g0)) (Relation.dom (eval_term gt)))
        | _ ->
          raise
            (Unsupported
               "the answer variables are not connected and at least one is unconstrained; that \
                is a cross product over an unbounded type."))
      | first :: rest ->
        let orient e = if e.u = 0 then e else flip e in
        let combined =
          List.fold rest ~init:(orient first).term ~f:(fun acc e ->
            Symbolic.meet acc (orient e).term)
        in
        let combined = apply_guard gs 0 combined in
        (match Map.find gs target with
         | None -> combined
         | Some g -> Symbolic.(combined >> g))
  in
  solve edges0 (Map.empty (module Int))

let run f = Symbolic.run (Plan.optimise (compile f))
let to_string f = Symbolic.to_string (compile f)

(* ------------------------------------------------------------------ *)
(* The four-parameter surface                                          *)
(* ------------------------------------------------------------------ *)

(* The same surface over {!Relation.General} atoms. One element type, one
   comparator: [compile] takes it explicitly, because the two places the
   compiler must mint a value from nothing — an [id] when source and target
   coincide, a [bot] to seed the join over branches — have no atom to read
   one from. Everything else is recovered from the trees via
   {!Symbolic.General.ca_of}. *)
module General = struct
  module S = Symbolic.General
  module R = Relation.General

  type var = V of int

  type ('e, 'ecmp) atom = {
    src : int;
    rel : ('e, 'ecmp, 'e, 'ecmp) R.t;
    dst : int;
    converse_ok : bool;
  }

  type ('e, 'ecmp) state = { next : int; atoms : ('e, 'ecmp) atom list }
  type ('e, 'ecmp, 'a) t = ('e, 'ecmp) state -> 'a * ('e, 'ecmp) state

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

  (** Follow a relation backwards. *)
  let back rel v =
    let* w = fresh in
    let* () = atom rel w v in
    return w

  (** Constrain two already-bound variables to be related. This is how a cycle
      is written, and it is what compiles to a meet. *)
  let constrain rel a b = atom rel a b

  (* ------------------------------------------------------------------ *)

  let leaf r = S.of_relation r

  (* ------------------------------------------------------------------ *)
  (* Compilation: variable elimination over the query graph             *)
  (* ------------------------------------------------------------------ *)

  type ('e, 'ecmp) edge = { u : int; v : int; term : ('e, 'ecmp, 'e, 'ecmp) S.t }

  let flip e = { u = e.v; v = e.u; term = S.converse e.term }

  (* The coreflexive on a relation's domain. *)
  let dom_ t = S.(meet (id (S.ca_of t)) (t >> converse t))

  let default_max_candidates = 64

  let eval_term t = S.run t

  let cross cmp xs ys =
    let pcmp = R.pair_comparator cmp cmp in
    R.of_pairs cmp cmp
      (Set.fold xs ~init:(Set.Using_comparator.empty ~comparator:pcmp) ~f:(fun acc a ->
         Set.fold ys ~init:acc ~f:(fun acc b -> Set.add acc (a, b))))

  let compile ~cmp ?(max_candidates = default_max_candidates)
      (f : var -> ('e, 'ecmp, var) t) : ('e, 'ecmp, 'e, 'ecmp) S.t =
    let source = V 0 in
    let (V target), st = f source { next = 1; atoms = [] } in
    let edges0 =
      List.rev_map st.atoms ~f:(fun a -> { u = a.src; v = a.dst; term = leaf a.rel })
    in
    let is_answer x = x = 0 || x = target in
    let incident edges x = List.filter edges ~f:(fun e -> e.u = x || e.v = x) in
    let vertices edges =
      List.dedup_and_sort ~compare:Int.compare (List.concat_map edges ~f:(fun e -> [ e.u; e.v ]))
    in
    let add_guard gs x t =
      Map.update gs x ~f:(function None -> t | Some prev -> S.meet prev t)
    in
    let apply_guard gs x t = match Map.find gs x with None -> t | Some g -> S.(g >> t) in
    (* Every rule removes at least one edge, so the reduction terminates. The
       budget is an invariant check on that argument, not a safeguard against
       a hard query — see the two-parameter [compile] for the bug that taught
       this. *)
    let rec reduce edges gs budget =
      if budget <= 0 then
        failwith
          (Printf.sprintf
             "Query.General.compile: reduction failed to make progress, %d edges left. This is a \
              bug in the elimination rules, not an unsupported query."
             (List.length edges));
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
        let oriented = if needs_flip then flip e2 else e2 in
        let merged = { e1 with term = S.meet e1.term oriented.term } in
        reduce
          (merged :: List.filter edges ~f:(fun e -> not (phys_equal e e1 || phys_equal e e2)))
          gs (budget - 1)
      | None -> (
        let dangling =
          List.find (vertices edges) ~f:(fun x ->
            (not (is_answer x)) && List.length (incident edges x) = 1)
        in
        match dangling with
        | Some x ->
          let original = List.hd_exn (incident edges x) in
          let e = if original.v = x then original else flip original in
          let gs = add_guard gs e.u (dom_ (apply_guard gs x e.term)) in
          reduce (List.filter edges ~f:(fun g -> not (phys_equal g original))) gs (budget - 1)
        | None -> (
          let waypoint =
            List.find (vertices edges) ~f:(fun x ->
              (not (is_answer x)) && List.length (incident edges x) = 2)
          in
          match waypoint with
          | Some x ->
            let orig_a, orig_b =
              match incident edges x with [ p; q ] -> (p, q) | _ -> assert false
            in
            let a = if orig_a.v = x then orig_a else flip orig_a in
            let b = if orig_b.u = x then orig_b else flip orig_b in
            let joined =
              { u = a.u; v = b.v; term = S.(a.term >> apply_guard gs x b.term) }
            in
            reduce
              (joined
              :: List.filter edges ~f:(fun g ->
                   not (phys_equal g orig_a || phys_equal g orig_b)))
              (Map.remove gs x) (budget - 1)
          | None -> (edges, gs)))
    in
    (* The values a variable could take, from the atoms touching it. *)
    let candidates edges gs x =
      let from_edge e =
        let r = eval_term e.term in
        if e.u = x && e.v = x then Set.inter (R.dom r) (R.rng r)
        else if e.v = x then R.rng r
        else R.dom r
      in
      let sets = List.map (incident edges x) ~f:from_edge in
      let sets =
        match Map.find gs x with
        | None -> sets
        | Some g -> R.dom (eval_term g) :: sets
      in
      match sets with
      | [] -> None
      | first :: rest -> Some (List.fold rest ~init:first ~f:Set.inter)
    in
    let rec solve edges gs =
      let edges, gs = reduce edges gs (List.length edges + 8) in
      let leftover = List.filter (vertices edges) ~f:(fun x -> not (is_answer x)) in
      if List.is_empty leftover then finish edges gs else branch edges gs leftover
    and branch edges gs leftover =
      let scored =
        List.filter_map leftover ~f:(fun x ->
          Option.map (candidates edges gs x) ~f:(fun cs -> (x, cs)))
      in
      match
        List.min_elt scored ~compare:(fun (_, a) (_, b) ->
          Int.compare (Set.length a) (Set.length b))
      with
      | None ->
        raise (Unsupported "a variable in the irreducible core has no atoms to bound it")
      | Some (x, cs) ->
        if Set.length cs > max_candidates then
          raise
            (Unsupported
               (Printf.sprintf
                  "the query has an irreducible core and branching on variable %d would need %d \
                   cases (limit %d). Raise ?max_candidates, or wait for tabulation."
                  x (Set.length cs) max_candidates));
        let per_candidate =
          Set.fold cs ~init:[] ~f:(fun acc c ->
            (* Substituting a value turns each atom at [x] into a coreflexive
               on its neighbour; [x] and its edges then vanish. *)
            let ok = ref true in
            let gs' = ref (Map.remove gs x) in
            List.iter (incident edges x) ~f:(fun e ->
              let r = eval_term e.term in
              if e.u = x && e.v = x then (if not (R.mem r c c) then ok := false)
              else if e.v = x then
                gs' :=
                  add_guard !gs' e.u
                    (S.of_relation (R.identity_on (R.preimage r c)))
              else
                gs' :=
                  add_guard !gs' e.v
                    (S.of_relation (R.identity_on (R.image r c))));
            if not !ok then acc
            else
              let rest = List.filter edges ~f:(fun e -> not (e.u = x || e.v = x)) in
              solve rest !gs' :: acc)
        in
        List.fold per_candidate ~init:(S.bot cmp cmp) ~f:S.join
    and finish edges gs =
      if Poly.equal source (V target) then
        match Map.find gs 0 with Some g -> g | None -> S.id cmp
      else
        match edges with
        | [] -> (
          (* No atom connects the answers. Fine if both are constrained — the
             answer is the cross product of two finite sets. *)
          match (Map.find gs 0, Map.find gs target) with
          | Some g0, Some gt ->
            S.of_relation
              (cross cmp (R.dom (eval_term g0)) (R.dom (eval_term gt)))
          | _ ->
            raise
              (Unsupported
                 "the answer variables are not connected and at least one is unconstrained; that \
                  is a cross product over an unbounded type."))
        | first :: rest ->
          let orient e = if e.u = 0 then e else flip e in
          let combined =
            List.fold rest ~init:(orient first).term ~f:(fun acc e ->
              S.meet acc (orient e).term)
          in
          let combined = apply_guard gs 0 combined in
          (match Map.find gs target with
           | None -> combined
           | Some g -> S.(combined >> g))
    in
    solve edges0 (Map.empty (module Int))

  let run ~cmp f = S.run (Plan.General.optimise (compile ~cmp f))
  let to_string ~cmp f = S.to_string (compile ~cmp f)
end
