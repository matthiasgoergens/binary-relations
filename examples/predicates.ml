(** Spike 4 — how big must the scalar language be?

    The brief budgets half a day for this and states the question as: take a
    dozen realistic business predicates, count how many need only comparison
    and arithmetic and how many need {!Rel.Algebra.SCALAR.opaque}. It matters
    because an opaque predicate is a hole in the {e cost model}, not merely in
    the optimiser, so the frequency of [opaque] is the frequency with which the
    planner is flying blind.

    Each predicate is written in the scalar object language if it can be, and
    through the host escape hatch if it cannot. Every one is then run through
    both interpreters — {!Rel.Eval} to check it selects the right rows,
    {!Rel.Symbolic} to print it and to ask whether the planner can see through
    it. The verdict at the bottom is counted, not estimated.

    Written against the four-parameter ladder, like the other examples: the
    only place it shows is that [where_] takes the filtered type's comparator,
    which is what a real consumer would carry anyway.

    Run with [dune exec examples/predicates.exe]. *)

open! Core
open Rel
module G = Relation.General

type order = {
  id : int;
  customer : string;
  status : string;
  country : string;
  qty : int;
  unit_price : int;  (** in cents, because the scalar language has no floats *)
  discount : int;  (** per cent *)
  due_day : int;  (** day number, because it has no dates either *)
  shipped_day : int;
  email : string;
}

let orders =
  [
    { id = 1; customer = "Acme"; status = "open"; country = "SG"; qty = 3; unit_price = 450;
      discount = 0; due_day = 100; shipped_day = 98; email = "ops@acme.example" };
    { id = 2; customer = "Ajax"; status = "closed"; country = "DE"; qty = 500; unit_price = 2100;
      discount = 15; due_day = 101; shipped_day = 140; email = "billing@ajax.test" };
    { id = 3; customer = "Borel"; status = "open"; country = "SG"; qty = 1; unit_price = 99900;
      discount = 0; due_day = 90; shipped_day = 90; email = "a.borel@borel.example" };
    { id = 4; customer = "Cauchy"; status = "hold"; country = "FR"; qty = 40; unit_price = 1250;
      discount = 5; due_day = 120; shipped_day = 119; email = "cauchy@limits.test" };
    { id = 5; customer = "Abel"; status = "open"; country = "NO"; qty = 12; unit_price = 300;
      discount = 60; due_day = 80; shipped_day = 130; email = "n.abel@abel.example" };
  ]

(* The comparator the example carries, the way a real consumer would. [id] is
   unique per order, so it stands in for the whole row — exactly the shape of
   merlin's [Lid.compare], and the opposite of the structural comparison the
   Poly façade would apply. *)
module Order_cmp = struct
  module T = struct
    type t = order

    let compare a b = Int.compare a.id b.id
    let sexp_of_t o = Sexp.List [ Int.sexp_of_t o.id; String.sexp_of_t o.customer ]
  end

  include T
  include Comparator.Make (T)
end

(* The relation under test: order id to the order. Nothing below depends on
   that shape — a coreflexive filters whatever it is composed with. *)
let rel = G.of_list (module Int) (module Order_cmp) (List.map orders ~f:(fun o -> (o.id, o)))

(* A predicate is a functor so that one of them can be handed to two
   interpreters. That is the whole point of the tagless-final presentation:
   the predicate is written once and means two different things. *)
module type PRED = functor (R : Algebra.General.RELATIONS) -> sig
  val p : order R.V.v -> bool R.V.v
end

(* ------------------------------------------------------------------ *)
(* Expressible in the scalar language                                  *)
(* ------------------------------------------------------------------ *)

module Status_open (R : Algebra.General.RELATIONS) = struct
  open R.V

  let p o = field ~name:"status" (fun o -> o.status) o =. str "open"
end

module Big_quantity (R : Algebra.General.RELATIONS) = struct
  open R.V

  let p o = field ~name:"qty" (fun o -> o.qty) o >. int_ 10
end

module Line_total (R : Algebra.General.RELATIONS) = struct
  open R.V

  let p o =
    mul (field ~name:"qty" (fun o -> o.qty) o) (field ~name:"unit_price" (fun o -> o.unit_price) o)
    >. int_ 10000
end

module Not_singapore (R : Algebra.General.RELATIONS) = struct
  open R.V

  let p o = field ~name:"country" (fun o -> o.country) o <>. str "SG"
end

module Shipped_late (R : Algebra.General.RELATIONS) = struct
  open R.V

  let p o =
    field ~name:"shipped_day" (fun o -> o.shipped_day) o
    >. field ~name:"due_day" (fun o -> o.due_day) o
end

module Open_and_discounted (R : Algebra.General.RELATIONS) = struct
  open R.V

  let p o =
    field ~name:"status" (fun o -> o.status) o
    =. str "open"
    &&. (field ~name:"discount" (fun o -> o.discount) o >=. int_ 50)
end

module Large_or_held (R : Algebra.General.RELATIONS) = struct
  open R.V

  let p o =
    field ~name:"qty" (fun o -> o.qty) o
    >. int_ 100
    ||. (field ~name:"status" (fun o -> o.status) o =. str "hold")
end

module Name_starts_with_a (R : Algebra.General.RELATIONS) = struct
  open R.V

  let p o = is_prefix (field ~name:"customer" (fun o -> o.customer) o) ~prefix:(str "A")
end

module Undiscounted (R : Algebra.General.RELATIONS) = struct
  open R.V

  let p o = not_ (field ~name:"discount" (fun o -> o.discount) o >. int_ 0)
end

module Due_in_window (R : Algebra.General.RELATIONS) = struct
  open R.V

  let p o =
    let d = field ~name:"due_day" (fun o -> o.due_day) o in
    d >=. int_ 95 &&. (d <=. int_ 105)
end

(* ------------------------------------------------------------------ *)
(* Not expressible: the escape hatch, and why in each case             *)
(* ------------------------------------------------------------------ *)

module Example_domain (R : Algebra.General.RELATIONS) = struct
  open R.V

  (* [is_prefix] is the only string operation in [v]; a suffix or substring
     test has nowhere to go but the host. *)
  let p o =
    opaque ~name:"email_domain"
      (fun e -> String.is_suffix e ~suffix:".example")
      (field ~name:"email" (fun o -> o.email) o)
end

module Round_dollars (R : Algebra.General.RELATIONS) = struct
  open R.V

  (* Integer division and modulo are not in [v]. They could be; this is the
     cheapest of the four to close. *)
  let p o =
    opaque ~name:"round_dollars"
      (fun price -> price % 100 = 0)
      (field ~name:"unit_price" (fun o -> o.unit_price) o)
end

module Taxed_price (R : Algebra.General.RELATIONS) = struct
  open R.V

  (* Floating point is not in [v] at all. Fixed-point integer arithmetic would
     express this, at the cost of the caller doing the scaling by hand. *)
  let p o =
    opaque ~name:"taxed_price"
      (fun o ->
        Float.( > ) (Float.of_int (o.unit_price * (100 - o.discount) / 100) *. 1.15) 2000.)
      o
end

module Name_pattern (R : Algebra.General.RELATIONS) = struct
  open R.V

  (* Regular expressions are not going into a scalar language whose point is
     that a planner can reason about it. This one belongs behind the hatch by
     right rather than by omission. *)
  let p o =
    opaque ~name:"name_pattern"
      (fun c -> String.length c = 5)
      (field ~name:"customer" (fun o -> o.customer) o)
end

(* ------------------------------------------------------------------ *)

type case = { description : string; expected : int list; pred : (module PRED) }

let cases =
  [
    { description = "status is open"; expected = [ 1; 3; 5 ]; pred = (module Status_open) };
    { description = "quantity above 10"; expected = [ 2; 4; 5 ]; pred = (module Big_quantity) };
    { description = "line total over $100"; expected = [ 2; 3; 4 ]; pred = (module Line_total) };
    { description = "not in Singapore"; expected = [ 2; 4; 5 ]; pred = (module Not_singapore) };
    { description = "shipped late"; expected = [ 2; 5 ]; pred = (module Shipped_late) };
    { description = "open and heavily discounted"; expected = [ 5 ];
      pred = (module Open_and_discounted) };
    { description = "large order or on hold"; expected = [ 2; 4 ]; pred = (module Large_or_held) };
    { description = "customer name starts with A"; expected = [ 1; 2; 5 ];
      pred = (module Name_starts_with_a) };
    { description = "not discounted"; expected = [ 1; 3 ]; pred = (module Undiscounted) };
    { description = "due within a ten-day window"; expected = [ 1; 2 ];
      pred = (module Due_in_window) };
    { description = "email at an .example domain"; expected = [ 1; 3; 5 ];
      pred = (module Example_domain) };
    { description = "unit price a round number of dollars"; expected = [ 2; 3; 5 ];
      pred = (module Round_dollars) };
    { description = "discounted price over $20 after tax"; expected = [ 2; 3 ];
      pred = (module Taxed_price) };
    { description = "customer name matches a pattern"; expected = [ 3 ];
      pred = (module Name_pattern) };
  ]

let () =
  let total = List.length cases in
  let blind = ref 0 and wrong = ref 0 in
  printf "\nSpike 4 — how big must the scalar language be?\n\n";
  printf "%-38s  %-13s  %s\n" "predicate" "cost model" "reads back as";
  printf "%s\n" (String.make 108 '-');
  List.iter cases ~f:(fun { description; expected; pred } ->
    let module P = (val pred : PRED) in
    let module Pe = P (Eval.General) in
    let module Ps = P (Symbolic.General) in
    let selected =
      List.map (Eval.General.to_list Eval.General.(of_relation rel >> where_ Order_cmp.comparator Pe.p))
        ~f:fst
    in
    if not (List.equal Int.equal selected expected) then (
      incr wrong;
      printf "  MISMATCH on %s: selected %s, expected %s\n" description
        (List.to_string selected ~f:Int.to_string)
        (List.to_string expected ~f:Int.to_string));
    let q = Symbolic.General.(of_relation rel >> where_ Order_cmp.comparator Ps.p) in
    let opaque = Symbolic.General.has_opaque q in
    if opaque then incr blind;
    let printed = Symbolic.General.to_string q in
    let printed =
      match String.substr_index printed ~pattern:"where(" with
      | Some i -> String.sub printed ~pos:i ~len:(String.length printed - i - 1)
      | None -> printed
    in
    printf "%-38s  %-13s  %s\n" description (if opaque then "BLIND" else "sees through") printed);
  printf "\n";
  if !wrong > 0 then printf "%d predicates selected the wrong rows\n" !wrong;
  printf "%d of %d predicates need the escape hatch (%.0f%%).\n\n" !blind total
    (100. *. Float.of_int !blind /. Float.of_int total);
  print_string
    "Reading. The four that need it are not exotic, and none needs it for an\n\
     interesting reason: a string suffix test, integer modulo, floating point,\n\
     and a pattern match. Three of the four close by adding ordinary operations\n\
     to the scalar language. The fourth is one a planner could not reason about\n\
     anyway, so it belongs behind the hatch by right rather than by omission.\n\n\
     The finding that cost the most was not on the list. Without a projection,\n\
     every predicate over a record had to go through the escape hatch, because\n\
     there was no way to say \"the qty field\" — which would have made the\n\
     answer 14 of 14 and the design look unworkable on a measurement that was\n\
     really about a missing combinator. A projection is not an opaque\n\
     predicate: it decides nothing, it is total, and the comparison wrapped\n\
     around it stays visible to the planner. Separating the two is what makes\n\
     the count above mean anything, and SCALAR.field was added for it.\n\n\
     What is left is verbosity: field ~name:\"qty\" (fun o -> o.qty) o names the\n\
     field twice, and is the obvious thing for a ppx to generate.\n"
