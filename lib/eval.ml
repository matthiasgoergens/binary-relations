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

open! Core

exception Unbounded of string

let unbounded fmt = Printf.ksprintf (fun s -> raise (Unbounded s)) fmt

module Impl = struct
  type ('a, 'b) t =
    | Fin : ('a, 'b) Relation.t -> ('a, 'b) t
        (** materialised; the only case that can be enumerated *)
    | Corefl : ('a -> bool) -> ('a, 'a) t  (** sub-identity; self-converse *)
    | Pfun : ('a -> 'b option) -> ('a, 'b) t  (** graph of a partial function *)

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
    | Corefl _ | Pfun _ -> false

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

  let to_relation : type a b. (a, b) t -> (a, b) Relation.t = function
    | Fin r -> r
    | Corefl _ -> unbounded "to_relation: coreflexive over an unbounded domain (use materialise)"
    | Pfun _ -> unbounded "to_relation: function graph over an unbounded domain (use materialise)"

  let to_list t = Relation.to_list (to_relation t)

  (* Coreflexives and partial functions share a shape: both are decided
     pointwise on the left element. Several operations only care about that. *)
  let pointwise : type a b. (a, b) t -> (a -> b option) option = function
    | Fin _ -> None
    | Corefl p -> Some (fun x -> if p x then Some x else None)
    | Pfun f -> Some f

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
    | Pfun _, Fin b ->
      if Relation.is_empty b then bot
      else
        unbounded
          ">>: a function graph on the left needs a preimage over an unbounded domain (materialise \
           the left operand first)"

  let converse : type a b. (a, b) t -> (b, a) t = function
    | Fin r -> Fin (Relation.converse r)
    | Corefl p -> Corefl p
    | Pfun _ ->
      unbounded "converse: of a function graph over an unbounded domain (use materialise first)"

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

  (* [star] on a finite relation is reflexive only on the elements that occur
     in it. Full reflexivity would be [id], which is not a finite value; the
     carrier restriction is what keeps the result one. This is a documented
     departure from the textbook [star] and the laws in {!Laws} state the
     restricted version. *)
  let star : type a. (a, a) t -> (a, a) t = function
    | Fin r -> Fin (Relation.star_on_carrier r)
    | Corefl _ -> id
    | Pfun _ -> unbounded "star: of a function graph over an unbounded domain (materialise first)"

  let fork : type a b c. (a, b) t -> (a, c) t -> (a, b * c) t =
   fun x y ->
    match (x, y) with
    | Fin a, Fin b -> Fin (Relation.fork a b)
    | Fin a, _ ->
      let g = Option.value_exn (pointwise y) in
      Fin
        (Relation.of_list
           (List.filter_map (Relation.to_list a) ~f:(fun (u, v) ->
              Option.map (g u) ~f:(fun w -> (u, (v, w))))))
    | _, Fin b ->
      let f = Option.value_exn (pointwise x) in
      Fin
        (Relation.of_list
           (List.filter_map (Relation.to_list b) ~f:(fun (u, w) ->
              Option.map (f u) ~f:(fun v -> (u, (v, w))))))
    | _, _ ->
      let f = Option.value_exn (pointwise x) and g = Option.value_exn (pointwise y) in
      Pfun
        (fun u ->
          match (f u, g u) with
          | Some v, Some w -> Some (v, w)
          | _ -> None)

  let group : type a b. (a, b) t -> (a, b list) t = function
    | Fin r -> Fin (Relation.group r)
    | Corefl _ | Pfun _ ->
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
