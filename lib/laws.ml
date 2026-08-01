(** The equational laws of the algebra, as runnable checks.

    The brief's M0 asks for "property tests generated from the laws". Putting
    them in the library rather than in the test directory is deliberate: they
    are part of what {!Algebra} {e means}, and anyone writing a new backend
    should be able to run them against it without copying anything. A signature
    says which operations exist; this says which ones are right.

    Every law is stated at [(int, int)] because the laws are polymorphic and
    the integers are a faithful enough instance — nothing in the algebra can
    inspect an element beyond comparing it.

    Note what is {e not} claimed. [star] is reflexive only on the carrier of
    its argument, because unrestricted reflexivity is not a finite value, so
    the Kleene laws below are the carrier-restricted ones. And the product laws
    are inclusions and restrictions rather than the equations a cartesian
    category would give, because Rel is not cartesian: [fork a b >> fst_] is
    not [a] but [a] restricted to the domain of [b]. Writing the true law down
    is more useful than writing the expected one and marking it as failing. *)

open! Core

module Make (R : Algebra.EQ_RELATIONS) = struct
  open R

  type sample = { a : (int, int) R.t; b : (int, int) R.t; c : (int, int) R.t }

  type law = {
    group : string;
    name : string;
    check : sample -> bool;
  }

  let eq = R.equal
  let sub = R.subset

  (* The coreflexive on the domain of [r]: [r >> r°] relates every pair of
     elements with a common image, and meeting with [id] keeps the diagonal. *)
  let dom_ r = meet id (r >> converse r)

  let category =
    [
      ("compose-associative", fun { a; b; c } -> eq (a >> b >> c) (a >> (b >> c)));
      ("id-left-unit", fun { a; _ } -> eq (id >> a) a);
      ("id-right-unit", fun { a; _ } -> eq (a >> id) a);
    ]

  let allegory =
    [
      ("converse-involution", fun { a; _ } -> eq (converse (converse a)) a);
      ("converse-antidistribution", fun { a; b; _ } ->
        eq (converse (a >> b)) (converse b >> converse a));
      ("converse-meet", fun { a; b; _ } ->
        eq (converse (meet a b)) (meet (converse a) (converse b)));
      ("converse-id", fun _ -> eq (converse (meet id bot)) (meet id bot));
      ("meet-idempotent", fun { a; _ } -> eq (meet a a) a);
      ("meet-commutative", fun { a; b; _ } -> eq (meet a b) (meet b a));
      ("meet-associative", fun { a; b; c } -> eq (meet (meet a b) c) (meet a (meet b c)));
      (* The modular law. Not derivable from the others, and the thing that
         makes meet interact correctly with composition — it is what separates
         an allegory from a category that merely happens to have a meet. *)
      ("modular-law", fun { a; b; c } ->
        sub (meet (a >> b) c) (a >> meet b (converse a >> c)));
      ("coreflexive-self-converse", fun { a; _ } ->
        let co = meet id a in
        eq (converse co) co);
    ]

  let union_allegory =
    [
      ("join-idempotent", fun { a; _ } -> eq (join a a) a);
      ("join-commutative", fun { a; b; _ } -> eq (join a b) (join b a));
      ("join-associative", fun { a; b; c } -> eq (join (join a b) c) (join a (join b c)));
      ("absorption-meet-join", fun { a; b; _ } -> eq (meet a (join a b)) a);
      ("absorption-join-meet", fun { a; b; _ } -> eq (join a (meet a b)) a);
      ("meet-distributes-over-join", fun { a; b; c } ->
        eq (meet a (join b c)) (join (meet a b) (meet a c)));
      ("join-distributes-over-meet", fun { a; b; c } ->
        eq (join a (meet b c)) (meet (join a b) (join a c)));
      ("bot-join-unit", fun { a; _ } -> eq (join a bot) a);
      ("bot-meet-absorbing", fun { a; _ } -> eq (meet a bot) bot);
      ("bot-compose-left", fun { a; _ } -> eq (bot >> a) bot);
      ("bot-compose-right", fun { a; _ } -> eq (a >> bot) bot);
      ("compose-distributes-join-left", fun { a; b; c } ->
        eq (a >> join b c) (join (a >> b) (a >> c)));
      ("compose-distributes-join-right", fun { a; b; c } ->
        eq (join a b >> c) (join (a >> c) (b >> c)));
      (* Only an inclusion: composition does not distribute over meet, because
         two different witnesses can be used on the two sides. *)
      ("compose-submeet", fun { a; b; c } -> sub (a >> meet b c) (meet (a >> b) (a >> c)));
    ]

  (* The residuals are adjoint to composition. The textbook statement is a
     Galois connection, [z ⊆ x / y ⟺ z >> y ⊆ x], and {e half of it is false
     here} — provably, and for a reason worth keeping in view.

     Take [y] empty. Then [z >> y ⊆ x] holds for every [z] whatsoever, so the
     largest such [z] is the universal relation, and [x / y] would have to be
     [top]. But [top] was excluded from {!Algebra.UNION_ALLEGORY} precisely
     because it is not a finite value. So the residual of a division allegory
     and the finiteness of a relation value cannot both be had, and this
     library keeps finiteness: [rdiv] returns the finite-carrier residual,
     restricted to the domains it can see.

     What survives is the connection restricted to those carriers, plus the
     cancellation law in full. This was found by the property test rather than
     by reading, which is the argument for having the laws be code. *)
  let rng_ r = meet id (converse r >> r)

  let division_allegory =
    [
      ("rdiv-sound", fun { a; b; c } -> (not (sub c (rdiv a b))) || sub (c >> b) a);
      ("rdiv-maximal-on-carrier", fun { a; b; c } ->
        (not (sub (c >> b) a)) || sub (dom_ a >> c >> dom_ b) (rdiv a b));
      ("ldiv-sound", fun { a; b; c } -> (not (sub c (ldiv a b))) || sub (a >> c) b);
      ("ldiv-maximal-on-carrier", fun { a; b; c } ->
        (not (sub (a >> c) b)) || sub (rng_ a >> c >> rng_ b) (ldiv a b));
      ("rdiv-cancel", fun { a; b; _ } -> sub (rdiv a b >> b) a);
      ("ldiv-cancel", fun { a; b; _ } -> sub (a >> ldiv a b) b);
      (* And the carrier restriction is not vacuous: on relations whose
         carriers cover the candidate, the full connection does hold. *)
      ("rdiv-galois-when-carriers-cover", fun { a; b; c } ->
        let c = dom_ a >> c >> dom_ b in
        Bool.equal (sub (c >> b) a) (sub c (rdiv a b)));
    ]

  let kleene =
    [
      ("plus-contains-base", fun { a; _ } -> sub a (plus a));
      ("plus-transitive", fun { a; _ } -> sub (plus a >> plus a) (plus a));
      ("plus-unfold", fun { a; _ } -> eq (plus a) (join a (a >> plus a)));
      ("plus-is-least", fun { a; _ } ->
        (* [plus a] adds nothing beyond what one more step can reach *)
        eq (plus a) (plus (plus a)));
      ("star-contains-plus", fun { a; _ } -> sub (plus a) (star a));
      ("star-idempotent", fun { a; _ } -> eq (star (star a)) (star a));
      ("star-transitive", fun { a; _ } -> eq (star a >> star a) (star a));
      ("plus-via-star", fun { a; _ } -> eq (plus a) (a >> star a));
    ]

  (* Products in an allegory, not in a cartesian category. The projection law
     holds only up to a domain restriction, and stating it that way is the
     honest version of "Rel is not cartesian". *)
  let products =
    [
      ("fork-fst-restricted", fun { a; b; _ } -> eq (fork a b >> fst_) (dom_ b >> a));
      ("fork-snd-restricted", fun { a; b; _ } -> eq (fork a b >> snd_) (dom_ a >> b));
      ("fork-fst-included", fun { a; b; _ } -> sub (fork a b >> fst_) a);
      ("fork-snd-included", fun { a; b; _ } -> sub (fork a b >> snd_) b);
      ("fork-diagonal", fun { a; _ } -> eq (fork a a >> fst_) (fork a a >> snd_));
      ("fork-bot", fun { a; _ } -> eq (fork a bot) bot);
    ]

  let all : law list =
    List.concat_map
      [
        ("category", category);
        ("allegory", allegory);
        ("union allegory", union_allegory);
        ("division allegory", division_allegory);
        ("Kleene", kleene);
        ("products", products);
      ]
      ~f:(fun (group, laws) -> List.map laws ~f:(fun (name, check) -> { group; name; check }))
end
