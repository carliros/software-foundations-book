
Basics _Functional Programming in Coq_
======================================

## Introduction {.section}

The functional programming style brings programming closer to simple,
everyday mathematics: If a procedure or method has no side effects, then
pretty much all you need to understand about it is how it maps inputs to
outputs — that is, you can think of it as just a concrete method for
computing a mathematical function. This is one sense of the word
"functional" in "functional programming." The direct connection between
programs and simple mathematical objects supports both formal proofs of
correctness and sound informal reasoning about program behavior.


The other sense in which functional programming is "functional" is that
it emphasizes the use of functions (or methods) as *first-class* values
— i.e., values that can be passed as arguments to other functions,
returned as results, stored in data structures, etc. The recognition
that functions can be treated as data in this way enables a host of
useful and powerful idioms.


Other common features of functional languages include *algebraic data
types* and *pattern matching*, which make it easy to construct and
manipulate rich data structures, and sophisticated *polymorphic type
systems* that support abstraction and code reuse. Coq shares all of
these features.


The first half of this chapter introduces the most essential elements of
Coq's functional programming language. The second half introduces some
basic *tactics* that can be used to prove simple properties of Coq
programs.

## Enumerated Types {.section}

One unusual aspect of Coq is that its set of built-in features is
*extremely* small. For example, instead of providing the usual palette
of atomic data types (booleans, integers, strings, etc.), Coq offers an
extremely powerful mechanism for defining new data types from scratch —
so powerful that all these familiar types arise as instances.


Naturally, the Coq distribution comes with an extensive standard library
providing definitions of booleans, numbers, and many common data
structures like lists and hash tables. But there is nothing magic or
primitive about these library definitions: they are ordinary user code.
To illustrate this, we will explicitly recapitulate all the definitions
we need in this course, rather than just getting them implicitly from
the library.


To see how this mechanism works, let's start with a very simple example.

### Days of the Week {.section}

The following declaration tells Coq that we are defining a new set of
data values — a *type*.

~~~~
Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.
~~~~

The type is called __day__, and its members are __monday__,
__tuesday__, etc. The second and following lines of
the definition can be read "__monday__ is a __day__, 
__tuesday__ is a __day__, etc."


Having defined __day__, we can write functions that operate on
days.

~~~~
Definition next_weekday (d:day) : day :=
  match d with
  | monday ⇒ tuesday
  | tuesday ⇒ wednesday
  | wednesday ⇒ thursday
  | thursday ⇒ friday
  | friday ⇒ monday
  | saturday ⇒ monday
  | sunday ⇒ monday
  end.
~~~~

One thing to note is that the argument and return types of this function
are explicitly declared. Like most functional programming languages, Coq
can often figure out these types for itself when they are not given
explicitly — i.e., it performs some *type inference* — but we'll always
include them to make reading easier.

Having defined a function, we should check that it works on some
examples. There are actually three different ways to do this in Coq.

First, we can use the command __Eval compute__ to evaluate a compound
expression involving __next\_weekday__.

~~~~
Eval compute in (next_weekday friday).
   (* ==> monday : day *)
Eval compute in (next_weekday (next_weekday saturday)).
   (* ==> tuesday : day *)
~~~~

If you have a computer handy, this would be an excellent moment to fire
up the Coq interpreter under your favorite IDE — either CoqIde or Proof
General — and try this for yourself. Load this file (__Basics.v__)
from the book's accompanying Coq sources, find the above example, submit
it to Coq, and observe the result.

The keyword __compute__ tells Coq precisely how to evaluate
the expression we give it. For the moment, __compute__
is the only one we'll need; later on we'll see some alternatives that
are sometimes useful.

Second, we can record what we *expect* the result to be in the form of a
Coq example:

~~~~
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
~~~~

This declaration does two things: it makes an assertion (that the second
weekday after __saturday__ is __tuesday__), and it gives the assertion
a name that can be used to refer to it later. Having made the assertion,
we can also ask Coq to verify it, like this:

~~~~
Proof. simpl. reflexivity. Qed.
~~~~

The details are not important for now (we'll come back to them in a
bit), but essentially this can be read as "The assertion we've just made
can be proved by observing that both sides of the equality evaluate to
the same thing, after some simplification."

Third, we can ask Coq to *extract*, from our __Definition__, 
a program in some other, more
conventional, programming language (OCaml, Scheme, or Haskell) with a
high-performance compiler. This facility is very interesting, since it
gives us a way to construct *fully certified* programs in mainstream
languages. Indeed, this is one of the main uses for which Coq was
developed. We'll come back to this topic in later chapters. More
information can also be found in the Coq'Art book by Bertot and
Casteran, as well as the Coq reference manual.


### Booleans {.section}

In a similar way, we can define the standard type __bool__ of
booleans, with members __true__ and __false__.

~~~~
Inductive bool : Type :=
  | true : bool
  | false : bool.
~~~~

Although we are rolling our own booleans here for the sake of building
up everything from scratch, Coq does, of course, provide a default
implementation of the booleans in its standard library, together with a
multitude of useful functions and lemmas. (Take a look at __Coq.Init.Datatypes__ in the Coq library
documentation if you're interested.) Whenever possible, we'll name our
own definitions and theorems so that they exactly coincide with the ones
in the standard library.

Functions over booleans can be defined in the same way as above:

~~~~
Definition negb (b:bool) : bool := 
  match b with
  | true ⇒ false
  | false ⇒ true
  end.

Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true ⇒ b2 
  | false ⇒ false
  end.

Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true ⇒ true
  | false ⇒ b2
  end.
~~~~

The last two illustrate the syntax for multi-argument function
definitions.

The following four "unit tests" constitute a complete specification — a
truth table — for the __orb__ function:

~~~~
Example test_orb1: (orb true false) = true.
Proof. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.
~~~~

(Note that we've dropped the __simpl__ in the proofs. It's not actually
needed because __reflexivity__ automatically performs
simplification.)

*A note on notation*: In .v files, we use square brackets to delimit
fragments of Coq code within comments; this convention, also used by the
__coqdoc__ documentation tool, keeps them visually
separate from the surrounding text. In the html version of the files,
these pieces of text appear in a __different__ __font__.

The values __Admitted__ and __admit__ can be used to fill a hole in
an incomplete definition or proof. We'll use them in the following
exercises. In general, your job in the exercises is to replace __admit__ or
__Admitted__ with real definitions or proofs.

#### Exercise: 1 star (nandb) {.section}

Complete the definition of the following function, then make sure that
the __Example__ assertions below can each be
verified by Coq.


This function should return __true__ if either or both of its inputs are __false__.

~~~~
Definition nandb (b1:bool) (b2:bool) : bool :=
  (* FILL IN HERE *) admit.
~~~~


Remove __"Admitted."__ and fill in each proof with "`Proof. reflexivity. Qed.`"

~~~~
Example test_nandb1: (nandb true false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb2: (nandb false false) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb3: (nandb false true) = true.
(* FILL IN HERE *) Admitted.
Example test_nandb4: (nandb true true) = false.
(* FILL IN HERE *) Admitted.
~~~~

☐


#### Exercise: 1 star (andb3) {.section}

Do the same for the __andb3__ function below. This function should
return __true__ when all of its inputs are __true__, and
__false__
otherwise.

~~~~
Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  (* FILL IN HERE *) admit.

Example test_andb31: (andb3 true true true) = true.
(* FILL IN HERE *) Admitted.
Example test_andb32: (andb3 false true true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb33: (andb3 true false true) = false.
(* FILL IN HERE *) Admitted.
Example test_andb34: (andb3 true true false) = false.
(* FILL IN HERE *) Admitted.
~~~~

☐


### Function Types {.section}

The __Check__ command causes Coq to print the type
of an expression. For example, the type of __negb__ __true__ is
__bool__.

~~~~
Check true.
(* ===> true : bool *)
Check (negb true).
(* ===> negb true : bool *)
~~~~

Functions like __negb__ itself are also data values, just like
__true__ and __false__. Their types are called *function types*,
and they are written with arrows.

~~~~
Check negb.
(* ===> negb : bool -> bool *)
~~~~

The type of __negb__, written `bool → bool` and
pronounced "__bool__ arrow __bool__," can be read, "Given an input
of type __bool__, this function produces an output of type
__bool__." Similarly, the type of __andb__,
written `bool → bool → bool`,
can be read, "Given two inputs, both of type __bool__, this
function produces an output of type __bool__."

### Numbers {.section}

*Technical digression*: Coq provides a fairly sophisticated *module
system*, to aid in organizing large developments. In this course we
won't need most of its features, but one is useful: If we enclose a
collection of declarations between __Module__ __X__ and __End__
__X__
markers, then, in the remainder of the file after the __End__,
these definitions will be referred to by names like __X.foo__
instead of just __foo__. Here, we use this feature to introduce the
definition of the type __nat__ in an inner module so that it does not
shadow the one from the standard library.

~~~~
Module Playground1.
~~~~

The types we have defined so far are examples of "enumerated types":
their definitions explicitly enumerate a finite set of elements. A more
interesting way of defining a type is to give a collection of "inductive
rules" describing its elements. For example, we can define the natural
numbers as follows:

~~~~
Inductive nat : Type :=
  | O : nat
  | S : nat → nat.
~~~~

The clauses of this definition can be read:

-   __O__
    is a natural number (note that this is the letter "__O__," not
    the numeral "__0__").
-   __S__
    is a "constructor" that takes a natural number and yields another
    one — that is, if __n__ is a natural number, then __S n__ is
    too.

Let's look at this in a little more detail.


Every inductively defined set (__day__, __nat__, __bool__, etc.) is actually a set of *expressions*.
The definition of __nat__ says how expressions in the set __nat__ can be
constructed:

-   the expression __O__ belongs to the set __nat__;
-   if __n__ is an expression belonging to the set
    __nat__, then __S n__ is also an expression
    belonging to the set __nat__; and
-   expressions formed in these two ways are the only ones belonging to
    the set __nat__.

The same rules apply for our definitions of __day__ and
__bool__.
The annotations we used for their constructors are analogous to the one
for the __O__ constructor, and indicate that each of those
constructors doesn't take any arguments.


These three conditions are the precise force of the __Inductive__ declaration. They imply that the
expression __O__, the expression __S O__, the
expression __S (S O)__, the expression __S ( S (S O))__, and so
on all belong to the set __nat__, while other expressions like __true__, 
__andb true false__, and __S ( S false)__ do not.

We can write simple functions that pattern match on natural numbers just
as we did above — for example, the predecessor function:

~~~~
Definition pred (n : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ n'
  end.
~~~~

The second branch can be read: "if __n__ has the form __S n'__ for some
__n'__, then return __n'__."

~~~~
End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O ⇒ O
    | S O ⇒ O
    | S (S n') ⇒ n'
  end.
~~~~

Because natural numbers are such a pervasive form of data, Coq provides
a tiny bit of built-in magic for parsing and printing them: ordinary
arabic numerals can be used as an alternative to the "unary" notation
defined by the constructors __S__ and __O__. Coq prints numbers in arabic form by
default:

~~~~
Check (S (S (S (S O)))).
Eval compute in (minustwo 4).
~~~~

The constructor __S__ has the type `nat → nat`, just
like the functions __minustwo__ and __pred__:

~~~~
Check S.
Check pred.
Check minustwo.
~~~~

These are all things that can be applied to a number to yield a number.
However, there is a fundamental difference: functions like __pred__ and
__minustwo__ come with *computation rules* — e.g.,
the definition of __pred__ says that __pred 2__ can be simplified to 
__1__ — while the definition of __S__ has no
such behavior attached. Although it is like a function in the sense that
it can be applied to an argument, it does not *do* anything at all!

For most function definitions over numbers, pure pattern matching is not
enough: we also need recursion. For example, to check that a number
__n__ is
even, we may need to recursively check whether `n - 2` is
even. To write such functions, we use the keyword __Fixpoint__.

~~~~
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O ⇒ true
  | S O ⇒ false
  | S (S n') ⇒ evenb n'
  end.
~~~~

We can define __oddb__ by a similar __Fixpoint__ declaration, but here is a simpler
definition that will be a bit easier to work with:

~~~~
Definition oddb (n:nat) : bool := negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. reflexivity. Qed.
~~~~

Naturally, we can also define multi-argument functions by recursion.
(Once again, we use a module to avoid polluting the namespace.)

~~~~
Module Playground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O ⇒ m
    | S n' ⇒ S (plus n' m)
  end.
~~~~

Adding three to two now gives us five, as we'd expect.

~~~~
Eval compute in (plus (S (S (S O))) (S (S O))).
~~~~

The simplification that Coq performs to reach this conclusion can be
visualized as follows:

~~~~
(*  plus (S (S (S O))) (S (S O))
==> S (plus (S (S O)) (S (S O))) by the second clause of the match
==> S (S (plus (S O) (S (S O)))) by the second clause of the match
==> S (S (S (plus O (S (S O))))) by the second clause of the match
==> S (S (S (S (S O))))          by the first clause of the match
*)
~~~~

As a notational convenience, if two or more arguments have the same
type, they can be written together. In the following definition, 
`(n m : nat)` means just the same as if we had written
`(n : nat) (m : nat)`.

~~~~
Fixpoint mult (n m : nat) : nat :=
  match n with
    | O ⇒ O
    | S n' ⇒ plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.
~~~~

You can match two expressions at once by putting a comma between them:

~~~~
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ ⇒ O
  | S _ , O ⇒ n
  | S n', S m' ⇒ minus n' m'
  end.
~~~~

The \_ in the first line is a *wildcard pattern*. Writing \_ in a
pattern is the same as writing some variable that doesn't get used on
the right-hand side. This avoids the need to invent a bogus variable
name.

~~~~
End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O ⇒ S O
    | S p ⇒ mult base (exp base p)
  end.
~~~~

#### Exercise: 1 star (factorial) {.section}

Recall the standard factorial function:

~~~~
factorial(0)  =  1
factorial(n)  =  n * factorial(n-1)     (if n>0)
~~~~

Translate this into Coq.

~~~~
Fixpoint factorial (n:nat) : nat :=
(* FILL IN HERE *) admit.

Example test_factorial1: (factorial 3) = 6.
(* FILL IN HERE *) Admitted.
Example test_factorial2: (factorial 5) = (mult 10 12).
(* FILL IN HERE *) Admitted.
~~~~

☐


We can make numerical expressions a little easier to read and write by
introducing "notations" for addition, multiplication, and subtraction.

~~~~
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x × y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1).
~~~~

(The __level__, __associativity__, and __nat\_scope__
annotations control how these notations are treated by Coq's parser. The
details are not important, but interested readers can refer to the "More
on Notation" subsection in the "Advanced Material" section at the end of
this chapter.)


Note that these do not change the definitions we've already made: they
are simply instructions to the Coq parser to accept `x + y` in place 
of `plus x y` and, conversely, to the Coq
pretty-printer to display `plus x y` as `x + y`.

When we say that Coq comes with nothing built-in, we really mean it:
even equality testing for numbers is a user-defined operation! The __beq\_nat__
function tests **nat**ural numbers for **eq**uality,
yielding a **b**oolean. Note the use of nested **match**es
(we could also have used a simultaneous match, as we did in __minus__.)

~~~~
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O ⇒ match m with
         | O ⇒ true
         | S m' ⇒ false
         end
  | S n' ⇒ match m with
            | O ⇒ false
            | S m' ⇒ beq_nat n' m'
            end
  end.
~~~~

Similarly, the __ble\_nat__ function tests **nat**ural
numbers for **l**ess-or-**e**qual, yielding a **b**oolean.

~~~~
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O ⇒ true
  | S n' ⇒
      match m with
      | O ⇒ false
      | S m' ⇒ ble_nat n' m'
      end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.
~~~~

#### Exercise: 2 stars (blt\_nat) {.section}

The __blt\_nat__ function tests **nat**ural
numbers for **l**ess-**t**han, yielding a **b**oolean. Instead of making up a new
__Fixpoint__ for this one, define it in terms
of a previously defined function.

~~~~
Definition blt_nat (n m : nat) : bool :=
  (* FILL IN HERE *) admit.

Example test_blt_nat1: (blt_nat 2 2) = false.
(* FILL IN HERE *) Admitted.
Example test_blt_nat2: (blt_nat 2 4) = true.
(* FILL IN HERE *) Admitted.
Example test_blt_nat3: (blt_nat 4 2) = false.
(* FILL IN HERE *) Admitted.
~~~~

☐

## Proof by Simplification {.section}


Now that we've defined a few datatypes and functions, let's turn to the
question of how to state and prove properties of their behavior.
Actually, in a sense, we've already started doing this: each __Example__
in the previous sections makes a precise claim about the behavior of
some function on some particular inputs. The proofs of these claims were
always the same: use __reflexivity__ to check that both sides of the
`=` simplify to identical values.


(By the way, it will be useful later to know that __reflexivity__ actually 
does somewhat more 
simplification than __simpl__ does — for example, it tries
"unfolding" defined terms, replacing them with their right-hand sides.
The reason for this difference is that, when reflexivity succeeds, the
whole goal is finished and we don't need to look at whatever expanded
expressions __reflexivity__ has found; by contrast, __simpl__ is
used in situations where we may have to read and understand the new
goal, so we would not want it blindly expanding definitions.)


The same sort of "proof by simplification" can be used to prove more
interesting properties as well. For example, the fact that __0__ 
is a "neutral element" for `+` on the left can be proved just by observing
that `0 + n` reduces to __n__ no matter what __n__ is, a fact that can be read
directly off the definition of __plus__.

~~~~
Theorem plus_O_n : ∀n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.
~~~~

(*Note*: You may notice that the above statement looks different in the
original source file and the final html output. In Coq files, we write
the __`∀`__ universal quantifier using
the "*forall*" reserved identifier. This gets printed as an upside-down
"A", the familiar symbol used in logic.)

The form of this theorem and proof are almost exactly the same as the
examples above; there are just a few differences.

First, we've used the keyword __Theorem__ instead of __Example__. Indeed, the difference is purely a
matter of style; the keywords __Example__ and __Theorem__ (and a few others,
including __Lemma__, __Fact__, and __Remark__)
mean exactly the same thing to Coq.

Secondly, we've added the quantifier __`∀ n : nat`__, so that our theorem talks about *all*
natural numbers __n__. In order to prove theorems of this form, we
need to to be able to reason by *assuming* the existence of an arbitrary
natural number __n__. This is achieved in the proof by __intros n__,
which moves the quantifier from the goal to a "context" of current
assumptions. In effect, we start the proof by saying "OK, suppose __n__ is some
arbitrary number."


The keywords __intros__, __simpl__, and __reflexivity__ are examples of *tactics*. A
tactic is a command that is used between __Proof__ and __Qed__ to
tell Coq how it should check the correctness of some claim we are
making. We will see several more tactics in the rest of this lecture,
and yet more in future lectures.

We could try to prove a similar theorem about __plus__

~~~~
Theorem plus_n_O : ∀n, n + 0 = n.
~~~~

However, unlike the previous proof, __simpl__ doesn't do anything in this
case

~~~~
Proof.
  simpl. (* Doesn't do anything! *)
Abort.
~~~~

(Can you explain why this happens? Step through both proofs with Coq and
notice how the goal and context change.)

~~~~
Theorem plus_1_l : ∀n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem mult_0_l : ∀n:nat, 0 × n = 0.
Proof.
  intros n. reflexivity. Qed.
~~~~

The __\_l__ suffix in the names of these theorems is
pronounced "on the left."


## Proof by Rewriting {.section}

Here is a slightly more interesting theorem:

~~~~
Theorem plus_id_example : ∀n m:nat,
  n = m →
  n + n = m + m.
~~~~

Instead of making a completely universal claim about all numbers __n__ and __m__, this
theorem talks about a more specialized property that only holds when
__`n = m`__. The arrow symbol is pronounced "implies."


As before, we need to be able to reason by assuming the existence of
some numbers __n__ and __m__. We also need to assume the hypothesis __`n = m`__. 
The __intros__ tactic will serve to move
all three of these from the goal into assumptions in the current
context.

Since __n__ and __m__ are arbitrary numbers, we can't just use
simplification to prove this theorem. Instead, we prove it by observing
that, if we are assuming __`n = m`__, then we
can replace __n__ with __m__ in the goal statement and obtain
an equality with the same expression on both sides. The tactic that
tells Coq to perform this replacement is called __rewrite__.

~~~~
Proof.
  intros n m. (* move both quantifiers into the context *)
  intros H. (* move the hypothesis into the context *)
  rewrite → H. (* Rewrite the goal using the hypothesis *)
  reflexivity. Qed.
~~~~

The first line of the proof moves the universally quantified variables
__n__ and __m__ into the context. 
The second moves the hypothesis __`n = m`__ into the context and gives it the (arbitrary)
name __H__. The third tells Coq to rewrite the current
goal (`n + n = m + m`) by
replacing the left side of the equality hypothesis __H__ with the
right side.

(The arrow symbol in the __rewrite__ has nothing to do with implication:
it tells Coq to apply the rewrite from left to right. To rewrite from
right to left, you can use __`rewrite ←`__. Try making this change in
the above proof and see what difference it makes in Coq's behavior.)

#### Exercise: 1 star (plus\_id\_exercise) {.section}

Remove __"Admitted."__ and fill in the proof.

~~~~
Theorem plus_id_exercise : ∀n m o : nat,
  n = m → m = o → n + m = m + o.
Proof.
  (* FILL IN HERE *) Admitted.
~~~~

☐


As we've seen in earlier examples, the __Admitted__ command tells Coq that we
want to skip trying to prove this theorem and just accept it as a given.
This can be useful for developing longer proofs, since we can state
subsidiary facts that we believe will be useful for making some larger
argument, use __Admitted__ to accept them on faith for the
moment, and continue thinking about the larger argument until we are
sure it makes sense; then we can go back and fill in the proofs we
skipped. Be careful, though: every time you say __Admitted__
(or __admit__) you are leaving a door open for total
nonsense to enter Coq's nice, rigorous, formally checked world!

We can also use the __rewrite__ tactic with a previously proved
theorem instead of a hypothesis from the context.

~~~~
Theorem mult_0_plus : ∀n m : nat,
  (0 + n) × m = n × m.
Proof.
  intros n m.
  rewrite → plus_O_n.
  reflexivity. Qed.
~~~~

#### Exercise: 2 stars (mult\_S\_1) {.section}

~~~~
Theorem mult_S_1 : ∀n m : nat,
  m = S n →
  m × (1 + n) = m × m.
Proof.
  (* FILL IN HERE *) Admitted.
~~~~

☐

## Proof by Case Analysis {.section}

Of course, not everything can be proved by simple calculation: In
general, unknown, hypothetical values (arbitrary numbers, booleans,
lists, etc.) can block the calculation. For example, if we try to prove
the following fact using the __simpl__ tactic as above, we get stuck.

~~~~
Theorem plus_1_neq_0_firsttry : ∀n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  simpl. (* does nothing! *)
Abort.
~~~~

The reason for this is that the definitions of both __beq\_nat__
and `+` begin by performing a __match__
on their first argument. But here, the first argument to `+` 
is the unknown number __n__ and the
argument to __beq\_nat__ is the compound expression __`n + 1`__; neither
can be simplified.

What we need is to be able to consider the possible forms of __n__
separately. If __n__ is __O__, then we can calculate the final result of
`beq_nat (n + 1) 0` and check that it is, indeed, __false__. 
And if `n = S n'` for some __n'__, then, although we don't know exactly what
number `n + 1` yields, we can calculate that, at least, it
will begin with one __S__, and this is enough to calculate that, again,
`beq_nat (n + 1) 0` will yield __false__.

The tactic that tells Coq to consider, separately, the cases where `n = O` 
and where `n = S n'` is called __destruct__.

~~~~
Theorem plus_1_neq_0 : ∀n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n. destruct n as [| n'].
    reflexivity.
    reflexivity. Qed.
~~~~

The __destruct__ generates *two* subgoals, which we
must then prove, separately, in order to get Coq to accept the theorem
as proved. (No special command is needed for moving from one subgoal to
the other. When the first subgoal has been proved, it just disappears
and we are left with the other "in focus.") In this proof, each of the
subgoals is easily proved by a single use of __reflexivity__.


The annotation "`as [| n']`" is
called an *intro pattern*. It tells Coq what variable names to introduce
in each subgoal. In general, what goes between the square brackets is a
*list* of lists of names, separated by `|`. Here, the first component is empty, since
the __O__
constructor is nullary (it doesn't carry any data). The second component
gives a single name, __n'__, since __S__ is a unary constructor.


The __destruct__ tactic can be used with any
inductively defined datatype. For example, we use it here to prove that
boolean negation is involutive — i.e., that negation is its own inverse.

~~~~
Theorem negb_involutive : ∀b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
    reflexivity.
    reflexivity. Qed.
~~~~

Note that the __destruct__ here has no __as__
clause because none of the subcases of the __destruct__
need to bind any variables, so there is no need to specify any names.
(We could also have written `as [|]`, or `as []`.) In
fact, we can omit the __as__ clause from *any* __destruct__
and Coq will fill in variable names automatically. Although this is
convenient, it is arguably bad style, since Coq often makes confusing
choices of names when left to its own devices.


#### Exercise: 1 star (zero\_nbeq\_plus\_1) {.section}

~~~~
Theorem zero_nbeq_plus_1 : ∀n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  (* FILL IN HERE *) Admitted.
~~~~

☐

## More Exercises {.section}


#### Exercise: 2 stars (boolean\_functions) {.section}

Use the tactics you have learned so far to prove the following theorem
about boolean functions.

~~~~
Theorem identity_fn_applied_twice :
  ∀(f : bool → bool),
  (∀(x : bool), f x = x) →
  ∀(b : bool), f (f b) = b.
Proof.
  (* FILL IN HERE *) Admitted.
~~~~

Now state and prove a theorem __negation\_fn\_applied\_twice__ similar to the
previous one but where the second hypothesis says that the function
__f__ has
the property that `f x = negb x`.

~~~~
(* FILL IN HERE *)
~~~~

☐


#### Exercise: 2 stars (andb\_eq\_orb) {.section}

Prove the following theorem. (You may want to first prove a subsidiary
lemma or two. Alternatively, remember that you do not have to introduce
all hypotheses at the same time.)

~~~~
Theorem andb_eq_orb :
  ∀(b c : bool),
  (andb b c = orb b c) →
  b = c.
Proof.
  (* FILL IN HERE *) Admitted.
~~~~

☐


#### Exercise: 3 stars (binary) {.section}

Consider a different, more efficient representation of natural numbers
using a binary rather than unary system. That is, instead of saying that
each natural number is either zero or the successor of a natural number,
we can say that each binary number is either

-   zero,
-   twice a binary number, or
-   one more than twice a binary number.

\(a) First, write an inductive definition of the type __bin__
corresponding to this description of binary numbers.

(Hint: Recall that the definition of __nat__ from class,

~~~~
Inductive nat : Type :=
      | O : nat
      | S : nat → nat.
~~~~

says nothing about what __O__ and __S__ "mean." It just says "__O__ is in the
set called __nat__, and if __n__ is in the set then so is __S__ __n__." The
interpretation of __O__ as zero and __S__ as successor/plus one comes from
the way that we *use* __nat__ values, by writing functions to do things
with them, proving things about them, and so on. Your definition of
__bin__
should be correspondingly simple; it is the functions you will write
next that will give it mathematical meaning.)


\(b) Next, write an increment function __incr__ for binary numbers, and a
function __bin\_to\_nat__ to convert binary numbers to unary
numbers.


\(c) Write five unit tests __test\_bin\_incr1__, __test\_bin\_incr2__, etc. for your increment and
binary-to-unary functions. Notice that incrementing a binary number and
then converting it to unary should yield the same result as first
converting it to unary and then incrementing.

~~~~
(* FILL IN HERE *)
~~~~

☐


## More on Notation (Advanced) {.section}

In general, sections marked Advanced are not needed to follow the rest
of the book, except possibly other Advanced sections. On a first
reading, you might want to skim these sections so that you know what's
there for future reference.

~~~~
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x × y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
~~~~

For each notation-symbol in Coq we can specify its *precedence level*
and its *associativity*. The precedence level n can be specified by the
keywords __at__ __level__ __n__ and it is helpful to disambiguate expressions
containing different symbols. The associativity is helpful to
disambiguate expressions containing more occurrences of the same symbol.
For example, the parameters specified above for `+` and `×` say
that the expression `1+2×3×4 ` is a
shorthand for the expression `(1+((2×3)×4))`. Coq uses precedence levels from
0 to 100, and *left*, *right*, or *no* associativity.


Each notation-symbol in Coq is also active in a *notation scope*. Coq
tries to guess what scope you mean, so when you write `S(O×O)` it
guesses __nat\_scope__, but when you write the cartesian
product (tuple) type `bool×bool` it
guesses __type\_scope__. Occasionally you have to help it
out with percent-notation by writing `(x×y)%nat`, and
sometimes in Coq's feedback to you it will use `%nat` to
indicate what scope a notation is in.


Notation scopes also apply to numeral notation (3,4,5, etc.), so you may
sometimes see `0%nat` which means __O__, or `0%Z` which
means the Integer zero.

## _Fixpoint_ and Structural Recursion (Advanced) {.section}

~~~~
Fixpoint plus' (n : nat) (m : nat) : nat :=
  match n with
    | O ⇒ m
    | S n' ⇒ S (plus' n' m)
  end.
~~~~

When Coq checks this definition, it notes that __plus'__ is
"decreasing on 1st argument." What this means is that we are performing
a *structural recursion* over the argument __n__ — i.e.,
that we make recursive calls only on strictly smaller values of __n__. This
implies that all calls to __plus'__ will eventually terminate. Coq demands
that some argument of *every* __Fixpoint__ definition is "decreasing".

This requirement is a fundamental feature of Coq's design: In
particular, it guarantees that every function that can be defined in Coq
will terminate on all inputs. However, because Coq's "decreasing
analysis" is not very sophisticated, it is sometimes necessary to write
functions in slightly unnatural ways.

#### Exercise: 2 stars, optional (decreasing) {.section}

To get a concrete sense of this, find a way to write a sensible __Fixpoint__ definition (of a simple function
on numbers, say) that *does* terminate on all inputs, but that Coq will
reject because of this restriction.

~~~~
(* FILL IN HERE *)
~~~~ 

☐
