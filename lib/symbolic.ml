(** Layer 3, interpreter 2: build the program instead of running it.

    The same functor body that {!Eval} turns into a set of pairs, this turns
    into a typed syntax tree — for printing, for planning, and for testing an
    optimiser by re-running the rewritten program and comparing.

    {2 Reading a predicate back}

    [where_] receives a host function [('a V.v -> bool V.v)]. Applying it to a
    {e fresh variable} recovers the predicate's structure, which is the whole
    reason the scalar layer is an object language rather than plain [('a ->
    bool)]: a planner can see [age >. 40] and push it down, where it could see
    nothing at all in a closure.

    But the symbolic interpreter must still be able to {e run} what it read
    back, or the AST would be an evaluation dead end. So a scalar term carries
    both a printable node and a closure, and the fresh variable is a projection
    out of a universal type created per [where_] call. The result is that
    [Symbolic] loses nothing: the tree prints, and it also evaluates.

    {2 Phantom parameters}

    Relations are a genuinely typed GADT, so a malformed tree cannot be built.
    Scalar terms are typed on the outside and untyped within, which is enough:
    the signature is what the user's program is checked against, and nothing
    can construct a scalar term except through it. *)

open! Core

(* The universal type, by way of an exception constructor generated per call.
   Standard, and unlike [Obj.magic] it cannot be got wrong: a projection that
   is handed the wrong injection simply does not match. *)
module Univ : sig
  type t

  val create : unit -> ('a -> t) * (t -> 'a option)
end = struct
  type t = exn

  let create (type a) () =
    let module M = struct
      exception E of a
    end in
    ((fun x -> M.E x), function M.E x -> Some x | _ -> None)
end

type node =
  | Var
  | Lit of string
  | Un of string * node
  | Bin of string * node * node
  | Opaque of string * node

module Scalar = struct
  type 'a v = { node : node; ev : Univ.t -> 'a }

  let un op f x = { node = Un (op, x.node); ev = (fun u -> f (x.ev u)) }
  let bin op f x y = { node = Bin (op, x.node, y.node); ev = (fun u -> f (x.ev u) (y.ev u)) }
  let lit x = { node = Lit "#lit"; ev = (fun _ -> x) }
  let int_ x = { node = Lit (Int.to_string x); ev = (fun _ -> x) }
  let str x = { node = Lit (Printf.sprintf "%S" x); ev = (fun _ -> x) }
  let bool_ x = { node = Lit (Bool.to_string x); ev = (fun _ -> x) }
  let ( =. ) x y = bin "=" Poly.equal x y
  let ( <>. ) x y = bin "<>" (fun a b -> not (Poly.equal a b)) x y
  let ( <. ) x y = bin "<" Poly.( < ) x y
  let ( <=. ) x y = bin "<=" Poly.( <= ) x y
  let ( >. ) x y = bin ">" Poly.( > ) x y
  let ( >=. ) x y = bin ">=" Poly.( >= ) x y
  let ( &&. ) x y = bin "&&" ( && ) x y
  let ( ||. ) x y = bin "||" ( || ) x y
  let not_ x = un "not" not x
  let add x y = bin "+" ( + ) x y
  let sub x y = bin "-" ( - ) x y
  let mul x y = bin "*" ( * ) x y
  let fst_v x = un "fst" fst x
  let snd_v x = un "snd" snd x
  let is_prefix s ~prefix = bin "is_prefix" (fun s p -> String.is_prefix s ~prefix:p) s prefix
  let field ~name f x = { node = Un ("." ^ name, x.node); ev = (fun u -> f (x.ev u)) }
  let opaque ~name f x = { node = Opaque (name, x.node); ev = (fun u -> f (x.ev u)) }
end

module Impl = struct
  module V = Scalar

  type ('a, 'b) t =
    | Id : ('a, 'a) t
    | Bot : ('a, 'b) t
    | Comp : ('a, 'b) t * ('b, 'c) t -> ('a, 'c) t
    | Conv : ('a, 'b) t -> ('b, 'a) t
    | Meet : ('a, 'b) t * ('a, 'b) t -> ('a, 'b) t
    | Join : ('a, 'b) t * ('a, 'b) t -> ('a, 'b) t
    | Rdiv : ('a, 'c) t * ('b, 'c) t -> ('a, 'b) t
    | Ldiv : ('a, 'b) t * ('a, 'c) t -> ('b, 'c) t
    | Plus : ('a, 'a) t -> ('a, 'a) t
    | Star : ('a, 'a) t -> ('a, 'a) t
    | Fst : ('a * 'b, 'a) t
    | Snd : ('a * 'b, 'b) t
    | Fork : ('a, 'b) t * ('a, 'c) t -> ('a, 'b * 'c) t
    | Where : node * ('a -> bool) -> ('a, 'a) t
    | Fn : ('a -> 'b) -> ('a, 'b) t
    | Group : ('a, 'b) t -> ('a, 'b list) t
    | Leaf : ('a, 'b) Relation.t -> ('a, 'b) t

  let id = Id
  let bot = Bot
  let ( >> ) x y = Comp (x, y)
  let converse x = Conv x
  let meet x y = Meet (x, y)
  let join x y = Join (x, y)
  let rdiv x y = Rdiv (x, y)
  let ldiv x y = Ldiv (x, y)
  let plus x = Plus x
  let star x = Star x
  let fst_ = Fst
  let snd_ = Snd
  let fork x y = Fork (x, y)
  let fn f = Fn f
  let group x = Group x
  let of_relation r = Leaf r
  let of_list l = Leaf (Relation.of_list l)

  (* Apply the user's predicate to a fresh variable: the node that comes back
     is the structure, and the closure that comes back is how to run it. *)
  let where_ f =
    let inject, project = Univ.create () in
    let var = { Scalar.node = Var; ev = (fun u -> Option.value_exn (project u)) } in
    let body = f var in
    Where (body.Scalar.node, fun x -> body.Scalar.ev (inject x))
end

include Impl

module _ : Algebra.RELATIONS = Impl

(** {2 Printing} *)

let rec string_of_node = function
  | Var -> "x"
  | Lit s -> s
  | Un (op, a) when String.is_prefix op ~prefix:"." -> string_of_node a ^ op
  | Un (op, a) -> Printf.sprintf "%s(%s)" op (string_of_node a)
  | Bin ("is_prefix", a, b) ->
    Printf.sprintf "is_prefix(%s, %s)" (string_of_node a) (string_of_node b)
  | Bin (op, a, b) -> Printf.sprintf "(%s %s %s)" (string_of_node a) op (string_of_node b)
  | Opaque (name, a) -> Printf.sprintf "opaque:%s(%s)" name (string_of_node a)

(* Whether a predicate contains a host escape hatch. This is exactly the
   question "does the cost model have a hole here?", so it is worth being able
   to ask it of a program. *)
let rec node_is_opaque = function
  | Opaque _ -> true
  | Var | Lit _ -> false
  | Un (_, a) -> node_is_opaque a
  | Bin (_, a, b) -> node_is_opaque a || node_is_opaque b

let rec to_string : type a b. (a, b) t -> string = function
  | Id -> "id"
  | Bot -> "bot"
  | Comp (x, y) -> Printf.sprintf "(%s >> %s)" (to_string x) (to_string y)
  | Conv x -> Printf.sprintf "%s°" (to_string x)
  | Meet (x, y) -> Printf.sprintf "(%s ∧ %s)" (to_string x) (to_string y)
  | Join (x, y) -> Printf.sprintf "(%s ∨ %s)" (to_string x) (to_string y)
  | Rdiv (x, y) -> Printf.sprintf "(%s / %s)" (to_string x) (to_string y)
  | Ldiv (x, y) -> Printf.sprintf "(%s \\ %s)" (to_string x) (to_string y)
  | Plus x -> Printf.sprintf "%s⁺" (to_string x)
  | Star x -> Printf.sprintf "%s*" (to_string x)
  | Fst -> "fst"
  | Snd -> "snd"
  | Fork (x, y) -> Printf.sprintf "⟨%s, %s⟩" (to_string x) (to_string y)
  | Where (n, _) -> Printf.sprintf "where(%s)" (string_of_node n)
  | Fn _ -> "fn"
  | Group x -> Printf.sprintf "group(%s)" (to_string x)
  | Leaf r -> Printf.sprintf "«%d»" (Relation.card r)

(** {2 Interpretation}

    A tree is not an evaluation dead end: it runs through {!Eval}, which is
    what makes an optimiser testable — rewrite the tree, run both, compare. *)

let rec to_eval : type a b. (a, b) t -> (a, b) Eval.t = function
  | Id -> Eval.id
  | Bot -> Eval.bot
  | Comp (x, y) -> Eval.( >> ) (to_eval x) (to_eval y)
  | Conv x -> Eval.converse (to_eval x)
  | Meet (x, y) -> Eval.meet (to_eval x) (to_eval y)
  | Join (x, y) -> Eval.join (to_eval x) (to_eval y)
  | Rdiv (x, y) -> Eval.rdiv (to_eval x) (to_eval y)
  | Ldiv (x, y) -> Eval.ldiv (to_eval x) (to_eval y)
  | Plus x -> Eval.plus (to_eval x)
  | Star x -> Eval.star (to_eval x)
  | Fst -> Eval.fst_
  | Snd -> Eval.snd_
  | Fork (x, y) -> Eval.fork (to_eval x) (to_eval y)
  | Where (_, p) -> Eval.where_ p
  | Fn f -> Eval.fn f
  | Group x -> Eval.group (to_eval x)
  | Leaf r -> Eval.of_relation r

let run t = Eval.to_relation (to_eval t)

(** Does this program contain anything the cost model cannot see through? *)
let rec has_opaque : type a b. (a, b) t -> bool = function
  | Id | Bot | Fst | Snd | Leaf _ -> false
  | Fn _ -> true (* a host function is opaque by construction *)
  | Where (n, _) -> node_is_opaque n
  | Conv x -> has_opaque x
  | Plus x -> has_opaque x
  | Star x -> has_opaque x
  | Group x -> has_opaque x
  | Comp (x, y) -> has_opaque x || has_opaque y
  | Meet (x, y) -> has_opaque x || has_opaque y
  | Join (x, y) -> has_opaque x || has_opaque y
  | Fork (x, y) -> has_opaque x || has_opaque y
  | Rdiv (x, y) -> has_opaque x || has_opaque y
  | Ldiv (x, y) -> has_opaque x || has_opaque y
