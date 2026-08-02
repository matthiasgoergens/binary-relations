(** Layer 3, interpreter 1: naive set-at-a-time evaluation over {!Relation}
    values. This is the correctness baseline — every other interpreter is
    tested against it.

    {2 Why there are three constructors and not one}

    A relation value is finite, but three of the operations in {!Algebra} are
    not: [id] is the diagonal of an unbounded type, [fn f] is the graph of a
    host function, and [where_ p] is a sub-identity carved out by a predicate.
    None of them can be enumerated, and refusing to have them would gut the
    algebra.

    So an evaluated relation is one of three things: a materialised finite
    relation, a coreflexive given by a predicate, or a partial function given
    by host code. The operations keep results in the smallest representation
    that can hold them, and the finite one absorbs the others on contact —
    composing a finite relation with a coreflexive is a filter, composing it
    with a function is a map. Every combination that {e would} produce an
    infinite value raises {!Unbounded} with a message naming the operation,
    rather than diverging or silently returning something wrong.

    That is not a wart to apologise for; it is the honest shape of the domain.
    [converse (fn f)] really is "run this function backwards", and the library
    should say it cannot, rather than pretend. {!materialise} is the answer:
    give the unbounded value a finite carrier and it becomes an ordinary
    relation, at which point converse is free. *)

open! Base

exception Unbounded of string

let unbounded fmt = Printf.ksprintf (fun s -> raise (Unbounded s)) fmt

module Impl = struct
  type ('a, 'b) t =
    | Fin : ('a, 'b) Relation.t -> ('a, 'b) t
        (** materialised; the only case that can be enumerated *)
    | Corefl : ('a -> bool) -> ('a, 'a) t  (** sub-identity; self-converse *)
    | Pfun : ('a -> 'b option) -> ('a, 'b) t  (** graph of a partial function *)
    | Pset : ('a -> 'b Set.Poly.t) -> ('a, 'b) t
        (** pointwise set-valued: [fst_ >> finite] is not a function graph and
            not finite, but it {e is} decidable at each point, and that is
            enough for anything that later supplies a carrier. Without this
            case such a composition had to raise, which threw away information
            the very next combinator would have used. *)

  module V = struct
    (* For the evaluator the scalar language is the host: a term [ 'a v ] is
       just an ['a]. The abstraction costs nothing here and is what lets
       [Symbolic] see the structure instead. *)
    type 'a v = 'a

    let lit x = x
    let int_ x = x
    let str x = x
    let bool_ x = x
    let ( =. ) a b = Poly.equal a b
    let ( <>. ) a b = not (Poly.equal a b)
    let ( <. ) a b = Poly.( < ) a b
    let ( <=. ) a b = Poly.( <= ) a b
    let ( >. ) a b = Poly.( > ) a b
    let ( >=. ) a b = Poly.( >= ) a b
    let ( &&. ) a b = a && b
    let ( ||. ) a b = a || b
    let not_ a = not a
    let add = ( + )
    let sub = ( - )
    let mul = ( * )
    let fst_v = fst
    let snd_v = snd
    let is_prefix s ~prefix = String.is_prefix s ~prefix
    let field ~name:_ f x = f x
    let opaque ~name:_ f x = f x
  end

  let of_relation r = Fin r
  let of_list l = Fin (Relation.of_list l)
  let bot = Fin Relation.empty
  let id = Corefl (fun _ -> true)
  let where_ p = Corefl p
  let fn f = Pfun (fun x -> Some (f x))
  let fst_ = Pfun (fun (a, _) -> Some a)
  let snd_ = Pfun (fun (_, b) -> Some b)

  let is_bot : type a b. (a, b) t -> bool = function
    | Fin r -> Relation.is_empty r
    | Corefl _ | Pfun _ | Pset _ -> false

  (* Give an unbounded value a finite carrier. This is how "run the function
     backwards" is actually done: materialise on the inputs you care about,
     then take the converse, which then costs nothing. *)
  let materialise : type a b. dom:a list -> (a, b) t -> (a, b) t =
   fun ~dom t ->
    match t with
    | Fin _ -> t
    | Corefl p -> Fin (Relation.of_list (List.filter_map dom ~f:(fun x -> if p x then Some (x, x) else None)))
    | Pfun f ->
      Fin (Relation.of_list (List.filter_map dom ~f:(fun x -> Option.map (f x) ~f:(fun y -> (x, y)))))
    | Pset g ->
      Fin
        (Relation.of_list
           (List.concat_map dom ~f:(fun x -> List.map (Set.to_list (g x)) ~f:(fun y -> (x, y)))))

  let to_relation : type a b. (a, b) t -> (a, b) Relation.t = function
    | Fin r -> r
    | Corefl _ -> unbounded "to_relation: coreflexive over an unbounded domain (use materialise)"
    | Pfun _ -> unbounded "to_relation: function graph over an unbounded domain (use materialise)"
    | Pset _ ->
      unbounded "to_relation: pointwise relation over an unbounded domain (use materialise)"

  let to_list t = Relation.to_list (to_relation t)

  (* Coreflexives and partial functions share a shape: both are decided
     pointwise on the left element. Several operations only care about that. *)
  (* Everything except [Fin] is decidable at a point, which is what the
     combinators that supply a carrier need. *)
  let setwise : type a b. (a, b) t -> (a -> b Set.Poly.t) option = function
    | Fin _ -> None
    | Corefl p -> Some (fun x -> if p x then Set.Poly.singleton x else Set.Poly.empty)
    | Pfun f -> Some (fun x -> match f x with Some y -> Set.Poly.singleton y | None -> Set.Poly.empty)
    | Pset g -> Some g

  let ( >> ) : type a b c. (a, b) t -> (b, c) t -> (a, c) t =
   fun x y ->
    match (x, y) with
    | Fin a, Fin b -> Fin (Relation.compose a b)
    | Fin a, Corefl p -> Fin (Relation.filter_rng a ~f:p)
    | Fin a, Pfun f ->
      Fin
        (Relation.of_list
           (List.filter_map (Relation.to_list a) ~f:(fun (u, v) ->
              Option.map (f v) ~f:(fun w -> (u, w)))))
    | Corefl p, Fin b -> Fin (Relation.filter_dom b ~f:p)
    | Corefl p, Corefl q -> Corefl (fun v -> p v && q v)
    | Corefl p, Pfun f -> Pfun (fun v -> if p v then f v else None)
    | Pfun f, Corefl q -> Pfun (fun v -> match f v with Some w when q w -> Some w | _ -> None)
    | Pfun f, Pfun g -> Pfun (fun v -> Option.bind (f v) ~f:g)
    (* Was: raise. The result is not finite, but it is decidable at a point,
       and whatever consumes it usually supplies a carrier. *)
    | Pfun f, Fin b ->
      Pset (fun v -> match f v with Some w -> Relation.image b w | None -> Set.Poly.empty)
    | Pset g, Fin b ->
      Pset
        (fun v ->
          Set.fold (g v) ~init:Set.Poly.empty ~f:(fun acc w ->
            Set.union acc (Relation.image b w)))
    | Fin a, Pset g ->
      Fin
        (Relation.of_list
           (List.concat_map (Relation.to_list a) ~f:(fun (u, v) ->
              List.map (Set.to_list (g v)) ~f:(fun w -> (u, w)))))
    | Corefl p, Pset g -> Pset (fun v -> if p v then g v else Set.Poly.empty)
    | Pset g, Corefl q -> Pset (fun v -> Set.filter (g v) ~f:q)
    | Pfun f, Pset g -> Pset (fun v -> match f v with Some w -> g w | None -> Set.Poly.empty)
    | Pset g, Pfun f ->
      Pset
        (fun v ->
          Set.fold (g v) ~init:Set.Poly.empty ~f:(fun acc w ->
            match f w with Some z -> Set.add acc z | None -> acc))
    | Pset g, Pset h ->
      Pset
        (fun v ->
          Set.fold (g v) ~init:Set.Poly.empty ~f:(fun acc w -> Set.union acc (h w)))

  let converse : type a b. (a, b) t -> (b, a) t = function
    | Fin r -> Fin (Relation.converse r)
    | Corefl p -> Corefl p
    | Pfun _ ->
      unbounded "converse: of a function graph over an unbounded domain (use materialise first)"
    | Pset _ ->
      unbounded "converse: of a pointwise relation over an unbounded domain (use materialise first)"

  let meet : type a b. (a, b) t -> (a, b) t -> (a, b) t =
   fun x y ->
    match (x, y) with
    | Fin a, Fin b -> Fin (Relation.inter a b)
    | Fin a, Corefl p -> Fin (Relation.filter a ~f:(fun u v -> Poly.equal u v && p u))
    | Corefl p, Fin b -> Fin (Relation.filter b ~f:(fun u v -> Poly.equal u v && p u))
    | Fin a, Pfun f ->
      Fin (Relation.filter a ~f:(fun u v -> match f u with Some w -> Poly.equal v w | None -> false))
    | Pfun f, Fin b ->
      Fin (Relation.filter b ~f:(fun u v -> match f u with Some w -> Poly.equal v w | None -> false))
    | Corefl p, Corefl q -> Corefl (fun v -> p v && q v)
    | Corefl p, Pfun f ->
      Corefl (fun v -> p v && (match f v with Some w -> Poly.equal v w | None -> false))
    | Pfun f, Corefl q ->
      Corefl (fun v -> q v && (match f v with Some w -> Poly.equal v w | None -> false))
    | Pfun f, Pfun g ->
      Pfun
        (fun v ->
          match (f v, g v) with
          | Some u, Some w when Poly.equal u w -> Some u
          | _ -> None)
    | Fin a, Pset g -> Fin (Relation.filter a ~f:(fun u v -> Set.mem (g u) v))
    | Pset g, Fin b -> Fin (Relation.filter b ~f:(fun u v -> Set.mem (g u) v))
    | Corefl p, Pset g -> Corefl (fun v -> p v && Set.mem (g v) v)
    | Pset g, Corefl q -> Corefl (fun v -> q v && Set.mem (g v) v)
    | Pfun f, Pset g ->
      Pfun (fun v -> match f v with Some w when Set.mem (g v) w -> Some w | _ -> None)
    | Pset g, Pfun f ->
      Pfun (fun v -> match f v with Some w when Set.mem (g v) w -> Some w | _ -> None)
    | Pset g, Pset h -> Pset (fun v -> Set.inter (g v) (h v))

  let join : type a b. (a, b) t -> (a, b) t -> (a, b) t =
   fun x y ->
    match (x, y) with
    | Fin a, Fin b -> Fin (Relation.union a b)
    | _ ->
      if is_bot x then y
      else if is_bot y then x
      else
        unbounded
          "join: the union of an unbounded relation with anything is not a finite value \
           (materialise first)"

  let plus : type a. (a, a) t -> (a, a) t = function
    | Fin r -> Fin (Relation.plus r)
    | Corefl p -> Corefl p (* already transitive *)
    | Pfun _ -> unbounded "plus: of a function graph over an unbounded domain (materialise first)"
    | Pset _ -> unbounded "plus: of a pointwise relation over an unbounded domain (materialise first)"

  (* [star] on a finite relation is reflexive only on the elements that occur
     in it. Full reflexivity would be [id], which is not a finite value; the
     carrier restriction is what keeps the result one. This is a documented
     departure from the textbook [star] and the laws in {!Laws} state the
     restricted version. *)
  let star : type a. (a, a) t -> (a, a) t = function
    | Fin r -> Fin (Relation.star_on_carrier r)
    | Corefl _ -> id
    | Pfun _ -> unbounded "star: of a function graph over an unbounded domain (materialise first)"
    | Pset _ -> unbounded "star: of a pointwise relation over an unbounded domain (materialise first)"

  let fork : type a b c. (a, b) t -> (a, c) t -> (a, b * c) t =
   fun x y ->
    match (x, y) with
    | Fin a, Fin b -> Fin (Relation.fork a b)
    (* A finite branch supplies the carrier the other branch needs. *)
    | Fin a, _ ->
      let g = Option.value_exn (setwise y) in
      Fin
        (Relation.of_list
           (List.concat_map (Relation.to_list a) ~f:(fun (u, v) ->
              List.map (Set.to_list (g u)) ~f:(fun w -> (u, (v, w))))))
    | _, Fin b ->
      let f = Option.value_exn (setwise x) in
      Fin
        (Relation.of_list
           (List.concat_map (Relation.to_list b) ~f:(fun (u, w) ->
              List.map (Set.to_list (f u)) ~f:(fun v -> (u, (v, w))))))
    | _, _ ->
      let f = Option.value_exn (setwise x) and g = Option.value_exn (setwise y) in
      Pset
        (fun u ->
          Set.fold (f u) ~init:Set.Poly.empty ~f:(fun acc v ->
            Set.fold (g u) ~init:acc ~f:(fun acc w -> Set.add acc (v, w))))

  let group : type a b. (a, b) t -> (a, b list) t = function
    | Fin r -> Fin (Relation.group r)
    | Corefl _ | Pfun _ | Pset _ ->
      unbounded "group: needs a finite relation to transpose (materialise first)"

  let rdiv : type a b c. (a, c) t -> (b, c) t -> (a, b) t =
   fun x y ->
    match (x, y) with
    | Fin a, Fin b -> Fin (Relation.rdiv a b)
    | _ -> unbounded "rdiv: both operands must be finite (materialise first)"

  (* [ldiv] is [rdiv] seen in a mirror; deriving it rather than writing it
     twice is the sort of thing the equational presentation is for. *)
  let ldiv : type a b c. (a, b) t -> (a, c) t -> (b, c) t =
   fun x y -> converse (rdiv (converse y) (converse x))

  (* Fused [(x >> y) ∧ z]. Only the all-finite case can be fused; anything
     else falls back to the ordinary meaning, which keeps this a pure
     optimisation with no new partiality. *)
  let meet_compose : type a b c. (a, b) t -> (b, c) t -> (a, c) t -> (a, c) t =
   fun x y z ->
    match (x, y, z) with
    | Fin a, Fin b, Fin c -> Fin (Relation.meet_compose a b c)
    | _ -> meet (x >> y) z

  let equal : type a b. (a, b) t -> (a, b) t -> bool =
   fun x y ->
    match (x, y) with
    | Fin a, Fin b -> Relation.equal a b
    | _ -> unbounded "equal: needs two finite relations (materialise first)"

  let subset : type a b. (a, b) t -> (a, b) t -> bool =
   fun x y ->
    match (x, y) with
    | Fin a, Fin b -> Relation.subset a b
    | _ -> unbounded "subset: needs two finite relations (materialise first)"
end

include Impl

(* Compile-time proof that the evaluator really implements the whole
   signature, checked here rather than in the tests so that it cannot be
   skipped. *)
module _ : Algebra.EQ_RELATIONS = Impl
