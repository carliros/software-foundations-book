<div id="page">

<div id="header">

</div>

<div id="main">

MoreStlc<span class="subtitle">More on the Simply Typed Lambda-Calculus</span> {.libtitle}
==============================================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">Stlc</span>.\
\

</div>

<div class="doc">

Simple Extensions to STLC {.section}
=========================

<div class="paragraph">

</div>

The simply typed lambda-calculus has enough structure to make its
theoretical properties interesting, but it is not much of a programming
language. In this chapter, we begin to close the gap with real-world
languages by introducing a number of familiar features that have
straightforward treatments at the level of typing.
<div class="paragraph">

</div>

Numbers {.section}
-------

<div class="paragraph">

</div>

Adding types, constants, and primitive operations for numbers is easy —
just a matter of combining the <span class="inlinecode"><span class="id"
type="keyword">Types</span></span> and <span class="inlinecode"><span
class="id" type="var">Stlc</span></span> chapters.
<div class="paragraph">

</div>

<span class="inlinecode"><span class="id" type="keyword">let</span></span>-bindings {.section}
-----------------------------------------------------------------------------------

<div class="paragraph">

</div>

When writing a complex expression, it is often useful to give names to
some of its subexpressions: this avoids repetition and often increases
readability. Most languages provide one or more ways of doing this. In
OCaml (and Coq), for example, we can write <span
class="inlinecode"><span class="id" type="keyword">let</span></span>
<span class="inlinecode"><span class="id" type="var">x</span>=<span
class="id" type="var">t~1~</span></span> <span class="inlinecode"><span
class="id" type="keyword">in</span></span> <span
class="inlinecode"><span class="id" type="var">t~2~</span></span> to
mean \`\`evaluate the expression <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> and bind the name <span
class="inlinecode"><span class="id" type="var">x</span></span> to the
resulting value while evaluating <span class="inlinecode"><span
class="id" type="var">t~2~</span></span>.''
<div class="paragraph">

</div>

Our <span class="inlinecode"><span class="id"
type="keyword">let</span></span>-binder follows OCaml's in choosing a
call-by-value evaluation order, where the <span class="inlinecode"><span
class="id" type="keyword">let</span></span>-bound term must be fully
evaluated before evaluation of the <span class="inlinecode"><span
class="id" type="keyword">let</span></span>-body can begin. The typing
rule <span class="inlinecode"><span class="id"
type="var">T\_Let</span></span> tells us that the type of a <span
class="inlinecode"><span class="id" type="keyword">let</span></span> can
be calculated by calculating the type of the <span
class="inlinecode"><span class="id"
type="keyword">let</span></span>-bound term, extending the context with
a binding with this type, and in this enriched context calculating the
type of the body, which is then the type of the whole <span
class="inlinecode"><span class="id" type="keyword">let</span></span>
expression.
<div class="paragraph">

</div>

At this point in the course, it's probably easier simply to look at the
rules defining this new feature as to wade through a lot of english text
conveying the same information. Here they are:
<div class="paragraph">

</div>

Syntax:
           t ::=                Terms
               | ...               (other terms same as before)
               | let x=t in t      let-binding

<div class="paragraph">

</div>

<div class="paragraph">

</div>

Reduction:
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Let1)  

------------------------------------------------------------------------

let x=t~1~ in t~2~ <span
style="font-family: arial;">⇒</span> let x=t~1~' in t~2~
  
(ST\_LetValue)  

------------------------------------------------------------------------

let x=v~1~ in t~2~ <span
style="font-family: arial;">⇒</span> [x:=v~1~]t~2~
Typing:
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : T~1~      <span
style="font-family: serif; font-size:85%;">Γ</span> , x:T~1~ <span
style="font-family: arial;">⊢</span> t~2~ : T~2~
(T\_Let)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> let x=t~1~ in t~2~ : T~2~
<div class="paragraph">

</div>

Pairs {.section}
-----

<div class="paragraph">

</div>

Our functional programming examples in Coq have made frequent use of
*pairs* of values. The type of such pairs is called a *product type*.
<div class="paragraph">

</div>

The formalization of pairs is almost too simple to be worth discussing.
However, let's look briefly at the various parts of the definition to
emphasize the common pattern.
<div class="paragraph">

</div>

In Coq, the primitive way of extracting the components of a pair is
*pattern matching*. An alternative style is to take <span
class="inlinecode"><span class="id" type="var">fst</span></span> and
<span class="inlinecode"><span class="id" type="var">snd</span></span> —
the first- and second-projection operators — as primitives. Just for
fun, let's do our products this way. For example, here's how we'd write
a function that takes a pair of numbers and returns the pair of their
sum and difference:
           λx:Nat*Nat. 
              let sum = x.fst + x.snd in
              let diff = x.fst - x.snd in
              (sum,diff)

<div class="paragraph">

</div>

Adding pairs to the simply typed lambda-calculus, then, involves adding
two new forms of term — pairing, written <span class="inlinecode">(<span
class="id" type="var">t~1~</span>,<span class="id"
type="var">t~2~</span>)</span>, and projection, written <span
class="inlinecode"><span class="id" type="var">t.fst</span></span> for
the first projection from <span class="inlinecode"><span class="id"
type="var">t</span></span> and <span class="inlinecode"><span class="id"
type="var">t.snd</span></span> for the second projection — plus one new
type constructor, <span class="inlinecode"><span class="id"
type="var">T~1~</span>×<span class="id" type="var">T~2~</span></span>,
called the *product* of <span class="inlinecode"><span class="id"
type="var">T~1~</span></span> and <span class="inlinecode"><span
class="id" type="var">T~2~</span></span>.
<div class="paragraph">

</div>

Syntax:
           t ::=                Terms
               | ...               
               | (t,t)             pair
               | t.fst             first projection
               | t.snd             second projection

           v ::=                Values
               | ...
               | (v,v)             pair value

           T ::=                Types
               | ...
               | T * T             product type

<div class="paragraph">

</div>

For evaluation, we need several new rules specifying how pairs and
projection behave.
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Pair1)  

------------------------------------------------------------------------

(t~1~,t~2~) <span style="font-family: arial;">⇒</span> (t~1~',t~2~)
t~2~ <span style="font-family: arial;">⇒</span> t~2~'
(ST\_Pair2)  

------------------------------------------------------------------------

(v~1~,t~2~) <span style="font-family: arial;">⇒</span> (v~1~,t~2~')
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Fst1)  

------------------------------------------------------------------------

t~1~.fst <span style="font-family: arial;">⇒</span> t~1~'.fst
  
(ST\_FstPair)  

------------------------------------------------------------------------

(v~1~,v~2~).fst <span style="font-family: arial;">⇒</span> v~1~
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Snd1)  

------------------------------------------------------------------------

t~1~.snd <span style="font-family: arial;">⇒</span> t~1~'.snd
  
(ST\_SndPair)  

------------------------------------------------------------------------

(v~1~,v~2~).snd <span style="font-family: arial;">⇒</span> v~2~
<div class="paragraph">

</div>

<div class="paragraph">

</div>

Rules <span class="inlinecode"><span class="id"
type="var">ST\_FstPair</span></span> and <span class="inlinecode"><span
class="id" type="var">ST\_SndPair</span></span> specify that, when a
fully evaluated pair meets a first or second projection, the result is
the appropriate component. The congruence rules <span
class="inlinecode"><span class="id" type="var">ST\_Fst1</span></span>
and <span class="inlinecode"><span class="id"
type="var">ST\_Snd1</span></span> allow reduction to proceed under
projections, when the term being projected from has not yet been fully
evaluated. <span class="inlinecode"><span class="id"
type="var">ST\_Pair1</span></span> and <span class="inlinecode"><span
class="id" type="var">ST\_Pair2</span></span> evaluate the parts of
pairs: first the left part, and then — when a value appears on the left
— the right part. The ordering arising from the use of the metavariables
<span class="inlinecode"><span class="id" type="var">v</span></span> and
<span class="inlinecode"><span class="id" type="var">t</span></span> in
these rules enforces a left-to-right evaluation strategy for pairs.
(Note the implicit convention that metavariables like <span
class="inlinecode"><span class="id" type="var">v</span></span> and <span
class="inlinecode"><span class="id" type="var">v~1~</span></span> can
only denote values.) We've also added a clause to the definition of
values, above, specifying that <span class="inlinecode">(<span
class="id" type="var">v~1~</span>,<span class="id"
type="var">v~2~</span>)</span> is a value. The fact that the components
of a pair value must themselves be values ensures that a pair passed as
an argument to a function will be fully evaluated before the function
body starts executing.
<div class="paragraph">

</div>

The typing rules for pairs and projections are straightforward.
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : T~1~       <span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~2~ : T~2~
(T\_Pair)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (t~1~,t~2~) : T~1~\*T~2~
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : T~11~\*T~12~
(T\_Fst)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~.fst : T~11~
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : T~11~\*T~12~
(T\_Snd)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~.snd : T~12~
<div class="paragraph">

</div>

The rule <span class="inlinecode"><span class="id"
type="var">T\_Pair</span></span> says that <span
class="inlinecode">(<span class="id" type="var">t~1~</span>,<span
class="id" type="var">t~2~</span>)</span> has type <span
class="inlinecode"><span class="id" type="var">T~1~</span>×<span
class="id" type="var">T~2~</span></span> if <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> has
type <span class="inlinecode"><span class="id"
type="var">T~1~</span></span> and <span class="inlinecode"><span
class="id" type="var">t~2~</span></span> has type <span
class="inlinecode"><span class="id" type="var">T~2~</span></span>.
Conversely, the rules <span class="inlinecode"><span class="id"
type="var">T\_Fst</span></span> and <span class="inlinecode"><span
class="id" type="var">T\_Snd</span></span> tell us that, if <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> has a
product type <span class="inlinecode"><span class="id"
type="var">T~11~</span>×<span class="id" type="var">T~12~</span></span>
(i.e., if it will evaluate to a pair), then the types of the projections
from this pair are <span class="inlinecode"><span class="id"
type="var">T~11~</span></span> and <span class="inlinecode"><span
class="id" type="var">T~12~</span></span>.
<div class="paragraph">

</div>

Unit {.section}
----

<div class="paragraph">

</div>

Another handy base type, found especially in languages in the ML family,
is the singleton type <span class="inlinecode"><span class="id"
type="var">Unit</span></span>. It has a single element — the term
constant <span class="inlinecode"><span class="id"
type="var">unit</span></span> (with a small <span
class="inlinecode"><span class="id" type="var">u</span></span>) — and a
typing rule making <span class="inlinecode"><span class="id"
type="var">unit</span></span> an element of <span
class="inlinecode"><span class="id" type="var">Unit</span></span>. We
also add <span class="inlinecode"><span class="id"
type="var">unit</span></span> to the set of possible result values of
computations — indeed, <span class="inlinecode"><span class="id"
type="var">unit</span></span> is the *only* possible result of
evaluating an expression of type <span class="inlinecode"><span
class="id" type="var">Unit</span></span>.
<div class="paragraph">

</div>

Syntax:
           t ::=                Terms
               | ...               
               | unit              unit value

           v ::=                Values
               | ...     
               | unit              unit

           T ::=                Types
               | ...
               | Unit              Unit type

Typing:
  
(T\_Unit)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> unit : Unit
<div class="paragraph">

</div>

It may seem a little strange to bother defining a type that has just one
element — after all, wouldn't every computation living in such a type be
trivial?
<div class="paragraph">

</div>

This is a fair question, and indeed in the STLC the <span
class="inlinecode"><span class="id" type="var">Unit</span></span> type
is not especially critical (though we'll see two uses for it below).
Where <span class="inlinecode"><span class="id"
type="var">Unit</span></span> really comes in handy is in richer
languages with various sorts of *side effects* — e.g., assignment
statements that mutate variables or pointers, exceptions and other sorts
of nonlocal control structures, etc. In such languages, it is convenient
to have a type for the (trivial) result of an expression that is
evaluated only for its effect.
<div class="paragraph">

</div>

Sums {.section}
----

<div class="paragraph">

</div>

Many programs need to deal with values that can take two distinct forms.
For example, we might identify employees in an accounting application
using using *either* their name *or* their id number. A search function
might return *either* a matching value *or* an error code.
<div class="paragraph">

</div>

These are specific examples of a binary *sum type*, which describes a
set of values drawn from exactly two given types, e.g.
           Nat + Bool

<div class="paragraph">

</div>

We create elements of these types by *tagging* elements of the component
types. For example, if <span class="inlinecode"><span class="id"
type="var">n</span></span> is a <span class="inlinecode"><span
class="id" type="var">Nat</span></span> then <span
class="inlinecode"><span class="id" type="var">inl</span></span> <span
class="inlinecode"><span class="id" type="var">v</span></span> is an
element of <span class="inlinecode"><span class="id"
type="var">Nat</span>+<span class="id" type="var">Bool</span></span>;
similarly, if <span class="inlinecode"><span class="id"
type="var">b</span></span> is a <span class="inlinecode"><span
class="id" type="var">Bool</span></span> then <span
class="inlinecode"><span class="id" type="var">inr</span></span> <span
class="inlinecode"><span class="id" type="var">b</span></span> is a
<span class="inlinecode"><span class="id" type="var">Nat</span>+<span
class="id" type="var">Bool</span></span>. The names of the tags <span
class="inlinecode"><span class="id" type="var">inl</span></span> and
<span class="inlinecode"><span class="id" type="var">inr</span></span>
arise from thinking of them as functions
<div class="paragraph">

</div>

       inl : Nat -> Nat + Bool
       inr : Bool -> Nat + Bool

<div class="paragraph">

</div>

that "inject" elements of <span class="inlinecode"><span class="id"
type="var">Nat</span></span> or <span class="inlinecode"><span
class="id" type="var">Bool</span></span> into the left and right
components of the sum type <span class="inlinecode"><span class="id"
type="var">Nat</span>+<span class="id" type="var">Bool</span></span>.
(But note that we don't actually treat them as functions in the way we
formalize them: <span class="inlinecode"><span class="id"
type="var">inl</span></span> and <span class="inlinecode"><span
class="id" type="var">inr</span></span> are keywords, and <span
class="inlinecode"><span class="id" type="var">inl</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> and <span
class="inlinecode"><span class="id" type="var">inr</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> are
primitive syntactic forms, not function applications. This allows us to
give them their own special typing rules.)
<div class="paragraph">

</div>

In general, the elements of a type <span class="inlinecode"><span
class="id" type="var">T~1~</span></span> <span
class="inlinecode">+</span> <span class="inlinecode"><span class="id"
type="var">T~2~</span></span> consist of the elements of <span
class="inlinecode"><span class="id" type="var">T~1~</span></span> tagged
with the token <span class="inlinecode"><span class="id"
type="var">inl</span></span>, plus the elements of <span
class="inlinecode"><span class="id" type="var">T~2~</span></span> tagged
with <span class="inlinecode"><span class="id"
type="var">inr</span></span>.
<div class="paragraph">

</div>

One important usage of sums is signaling errors:
        div : Nat -> Nat -> (Nat + Unit) =
        div =
          λx:Nat. λy:Nat.
            if iszero y then
              inr unit
            else
              inl ...

The type <span class="inlinecode"><span class="id"
type="var">Nat</span></span> <span class="inlinecode">+</span> <span
class="inlinecode"><span class="id" type="var">Unit</span></span> above
is in fact isomorphic to <span class="inlinecode"><span class="id"
type="var">option</span></span> <span class="inlinecode"><span
class="id" type="var">nat</span></span> in Coq, and we've already seen
how to signal errors with options.
<div class="paragraph">

</div>

To *use* elements of sum types, we introduce a <span
class="inlinecode"><span class="id" type="tactic">case</span></span>
construct (a very simplified form of Coq's <span
class="inlinecode"><span class="id" type="keyword">match</span></span>)
to destruct them. For example, the following procedure converts a <span
class="inlinecode"><span class="id" type="var">Nat</span>+<span
class="id" type="var">Bool</span></span> into a <span
class="inlinecode"><span class="id" type="var">Nat</span></span>:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

        getNat = 
          λx:Nat+Bool.
            case x of
              inl n => n
            | inr b => if b then 1 else 0

<div class="paragraph">

</div>

More formally...
<div class="paragraph">

</div>

Syntax:
           t ::=                Terms
               | ...               
               | inl T t           tagging (left)
               | inr T t           tagging (right)
               | case t of         case
                   inl x => t
                 | inr x => t 

           v ::=                Values
               | ...
               | inl T v           tagged value (left)
               | inr T v           tagged value (right)

           T ::=                Types
               | ...
               | T + T             sum type

<div class="paragraph">

</div>

Evaluation:
<div class="paragraph">

</div>

t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Inl)  

------------------------------------------------------------------------

inl T t~1~ <span style="font-family: arial;">⇒</span> inl T t~1~'
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Inr)  

------------------------------------------------------------------------

inr T t~1~ <span style="font-family: arial;">⇒</span> inr T t~1~'
t0 <span style="font-family: arial;">⇒</span> t0'
(ST\_Case)  

------------------------------------------------------------------------

case t0 of inl x1 ⇒ t~1~ | inr x2 ⇒ t~2~ <span
style="font-family: arial;">⇒</span>
case t0' of inl x1 ⇒ t~1~ | inr x2 ⇒ t~2~
  
(ST\_CaseInl)  

------------------------------------------------------------------------

case (inl T v0) of inl x1 ⇒ t~1~ | inr x2 ⇒ t~2~
<span style="font-family: arial;">⇒</span>  [x1:=v0]t~1~
  
(ST\_CaseInr)  

------------------------------------------------------------------------

case (inr T v0) of inl x1 ⇒ t~1~ | inr x2 ⇒ t~2~
<span style="font-family: arial;">⇒</span>  [x2:=v0]t~2~
<div class="paragraph">

</div>

Typing:
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ :  T~1~
(T\_Inl)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> inl T~2~ t~1~ : T~1~ + T~2~
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : T~2~
(T\_Inr)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> inr T~1~ t~1~ : T~1~ + T~2~
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t0 : T~1~+T~2~
<span
style="font-family: serif; font-size:85%;">Γ</span> , x1:T~1~ <span
style="font-family: arial;">⊢</span> t~1~ : T
<span
style="font-family: serif; font-size:85%;">Γ</span> , x2:T~2~ <span
style="font-family: arial;">⊢</span> t~2~ : T
(T\_Case)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> case t0 of inl x1 ⇒ t~1~ | inr x2 ⇒ t~2~ : T
<div class="paragraph">

</div>

We use the type annotation in <span class="inlinecode"><span class="id"
type="var">inl</span></span> and <span class="inlinecode"><span
class="id" type="var">inr</span></span> to make the typing simpler,
similarly to what we did for functions. Without this extra information,
the typing rule <span class="inlinecode"><span class="id"
type="var">T\_Inl</span></span>, for example, would have to say that,
once we have shown that <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> is an element of type <span
class="inlinecode"><span class="id" type="var">T~1~</span></span>, we
can derive that <span class="inlinecode"><span class="id"
type="var">inl</span></span> <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> is an element of <span
class="inlinecode"><span class="id" type="var">T~1~</span></span> <span
class="inlinecode">+</span> <span class="inlinecode"><span class="id"
type="var">T~2~</span></span> for *any* type T~2~. For example, we could
derive both <span class="inlinecode"><span class="id"
type="var">inl</span></span> <span class="inlinecode">5</span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">Nat</span></span> <span class="inlinecode">+</span> <span
class="inlinecode"><span class="id" type="var">Nat</span></span> and
<span class="inlinecode"><span class="id" type="var">inl</span></span>
<span class="inlinecode">5</span> <span class="inlinecode">:</span>
<span class="inlinecode"><span class="id" type="var">Nat</span></span>
<span class="inlinecode">+</span> <span class="inlinecode"><span
class="id" type="var">Bool</span></span> (and infinitely many other
types). This failure of uniqueness of types would mean that we cannot
build a typechecking algorithm simply by "reading the rules from bottom
to top" as we could for all the other features seen so far.
<div class="paragraph">

</div>

There are various ways to deal with this difficulty. One simple one —
which we've adopted here — forces the programmer to explicitly annotate
the "other side" of a sum type when performing an injection. This is
rather heavyweight for programmers (and so real languages adopt other
solutions), but it is easy to understand and formalize.
<div class="paragraph">

</div>

Lists {.section}
-----

<div class="paragraph">

</div>

The typing features we have seen can be classified into *base types*
like <span class="inlinecode"><span class="id"
type="var">Bool</span></span>, and *type constructors* like <span
class="inlinecode"><span style="font-family: arial;">→</span></span> and
<span class="inlinecode">×</span> that build new types from old ones.
Another useful type constructor is <span class="inlinecode"><span
class="id" type="var">List</span></span>. For every type <span
class="inlinecode"><span class="id" type="var">T</span></span>, the type
<span class="inlinecode"><span class="id" type="var">List</span></span>
<span class="inlinecode"><span class="id" type="var">T</span></span>
describes finite-length lists whose elements are drawn from <span
class="inlinecode"><span class="id" type="var">T</span></span>.
<div class="paragraph">

</div>

In principle, we could encode lists using pairs, sums and *recursive*
types. But giving semantics to recursive types is non-trivial. Instead,
we'll just discuss the special case of lists directly.
<div class="paragraph">

</div>

Below we give the syntax, semantics, and typing rules for lists. Except
for the fact that explicit type annotations are mandatory on <span
class="inlinecode"><span class="id" type="var">nil</span></span> and
cannot appear on <span class="inlinecode"><span class="id"
type="var">cons</span></span>, these lists are essentially identical to
those we built in Coq. We use <span class="inlinecode"><span class="id"
type="var">lcase</span></span> to destruct lists, to avoid dealing with
questions like "what is the <span class="inlinecode"><span class="id"
type="var">head</span></span> of the empty list?"
<div class="paragraph">

</div>

For example, here is a function that calculates the sum of the first two
elements of a list of numbers:
        λx:List Nat.  
        lcase x of nil -> 0 
           | a::x' -> lcase x' of nil -> a
                         | b::x'' -> a+b 

<div class="paragraph">

</div>

<div class="paragraph">

</div>

Syntax:
           t ::=                Terms
               | ...
               | nil T
               | cons t t
               | lcase t of nil -> t | x::x -> t

           v ::=                Values
               | ...
               | nil T             nil value
               | cons v v          cons value

           T ::=                Types
               | ...
               | List T            list of Ts

<div class="paragraph">

</div>

Reduction:
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Cons1)  

------------------------------------------------------------------------

cons t~1~ t~2~ <span
style="font-family: arial;">⇒</span> cons t~1~' t~2~
t~2~ <span style="font-family: arial;">⇒</span> t~2~'
(ST\_Cons2)  

------------------------------------------------------------------------

cons v~1~ t~2~ <span
style="font-family: arial;">⇒</span> cons v~1~ t~2~'
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Lcase1)  

------------------------------------------------------------------------

(lcase t~1~ of nil <span
style="font-family: arial;">→</span> t~2~ | xh::xt <span
style="font-family: arial;">→</span> t~3~) <span
style="font-family: arial;">⇒</span>
(lcase t~1~' of nil <span
style="font-family: arial;">→</span> t~2~ | xh::xt <span
style="font-family: arial;">→</span> t~3~)
  
(ST\_LcaseNil)  

------------------------------------------------------------------------

(lcase nil T of nil <span
style="font-family: arial;">→</span> t~2~ | xh::xt <span
style="font-family: arial;">→</span> t~3~)
<span style="font-family: arial;">⇒</span> t~2~
  
(ST\_LcaseCons)  

------------------------------------------------------------------------

(lcase (cons vh vt) of nil <span
style="font-family: arial;">→</span> t~2~ | xh::xt <span
style="font-family: arial;">→</span> t~3~)
<span style="font-family: arial;">⇒</span> [xh:=vh,xt:=vt]t~3~
<div class="paragraph">

</div>

Typing:
  
(T\_Nil)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> nil T : List T
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : T      <span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~2~ : List T
(T\_Cons)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> cons t~1~ t~2~: List T
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : List T~1~
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~2~ : T
<span
style="font-family: serif; font-size:85%;">Γ</span> , h:T~1~, t:List T~1~ <span
style="font-family: arial;">⊢</span> t~3~ : T
(T\_Lcase)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (lcase t~1~ of nil <span
style="font-family: arial;">→</span> t~2~ | h::t <span
style="font-family: arial;">→</span> t~3~) : T
<div class="paragraph">

</div>

General Recursion {.section}
-----------------

<div class="paragraph">

</div>

Another facility found in most programming languages (including Coq) is
the ability to define recursive functions. For example, we might like to
be able to define the factorial function like this:
       fact = λx:Nat. 
                 if x=0 then 1 else x * (fact (pred x)))    

But this would require quite a bit of work to formalize: we'd have to
introduce a notion of "function definitions" and carry around an
"environment" of such definitions in the definition of the <span
class="inlinecode"><span class="id" type="var">step</span></span>
relation.
<div class="paragraph">

</div>

Here is another way that is straightforward to formalize: instead of
writing recursive definitions where the right-hand side can contain the
identifier being defined, we can define a *fixed-point operator* that
performs the "unfolding" of the recursive definition in the right-hand
side lazily during reduction.
       fact = 
           fix
             (\f:Nat->Nat.
                λx:Nat. 
                   if x=0 then 1 else x * (f (pred x)))    

<div class="paragraph">

</div>

The intuition is that the higher-order function <span
class="inlinecode"><span class="id" type="var">f</span></span> passed to
<span class="inlinecode"><span class="id" type="var">fix</span></span>
is a *generator* for the <span class="inlinecode"><span class="id"
type="var">fact</span></span> function: if <span
class="inlinecode"><span class="id" type="var">fact</span></span> is
applied to a function that approximates the desired behavior of <span
class="inlinecode"><span class="id" type="var">fact</span></span> up to
some number <span class="inlinecode"><span class="id"
type="var">n</span></span> (that is, a function that returns correct
results on inputs less than or equal to <span class="inlinecode"><span
class="id" type="var">n</span></span>), then it returns a better
approximation to <span class="inlinecode"><span class="id"
type="var">fact</span></span> — a function that returns correct results
for inputs up to <span class="inlinecode"><span class="id"
type="var">n</span>+1</span>. Applying <span class="inlinecode"><span
class="id" type="var">fix</span></span> to this generator returns its
*fixed point* — a function that gives the desired behavior for all
inputs <span class="inlinecode"><span class="id"
type="var">n</span></span>.
<div class="paragraph">

</div>

(The term "fixed point" has exactly the same sense as in ordinary
mathematics, where a fixed point of a function <span
class="inlinecode"><span class="id" type="var">f</span></span> is an
input <span class="inlinecode"><span class="id"
type="var">x</span></span> such that <span class="inlinecode"><span
class="id" type="var">f</span>(<span class="id"
type="var">x</span>)</span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">x</span></span>. Here, a
fixed point of a function <span class="inlinecode"><span class="id"
type="var">F</span></span> of type (say) <span class="inlinecode">(<span
class="id" type="var">Nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Nat</span>)-\>(<span class="id" type="var">Nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Nat</span>)</span> is a function <span
class="inlinecode"><span class="id" type="var">f</span></span> such that
<span class="inlinecode"><span class="id" type="var">F</span></span>
<span class="inlinecode"><span class="id" type="var">f</span></span> is
behaviorally equivalent to <span class="inlinecode"><span class="id"
type="var">f</span></span>.)
<div class="paragraph">

</div>

Syntax:
           t ::=                Terms
               | ...
               | fix t             fixed-point operator

Reduction:
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Fix1)  

------------------------------------------------------------------------

fix t~1~ <span style="font-family: arial;">⇒</span> fix t~1~'
F = \\xf:T~1~.t~2~
(ST\_FixAbs)  

------------------------------------------------------------------------

fix F <span style="font-family: arial;">⇒</span> [xf:=fix F]t~2~
Typing:
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : T~1~-\>T~1~
(T\_Fix)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> fix t~1~ : T~1~
<div class="paragraph">

</div>

Let's see how <span class="inlinecode"><span class="id"
type="var">ST\_FixAbs</span></span> works by reducing <span
class="inlinecode"><span class="id" type="var">fact</span></span> <span
class="inlinecode">3</span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">fix</span></span> <span
class="inlinecode"><span class="id" type="var">F</span></span> <span
class="inlinecode">3</span>, where <span class="inlinecode"><span
class="id" type="var">F</span></span> <span class="inlinecode">=</span>
<span class="inlinecode">(\\<span class="id" type="var">f</span>.</span>
<span class="inlinecode">\\<span class="id" type="var">x</span>.</span>
<span class="inlinecode"><span class="id"
type="keyword">if</span></span> <span class="inlinecode"><span
class="id" type="var">x</span>=0</span> <span class="inlinecode"><span
class="id" type="keyword">then</span></span> <span
class="inlinecode">1</span> <span class="inlinecode"><span class="id"
type="keyword">else</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">×</span>
<span class="inlinecode">(<span class="id" type="var">f</span></span>
<span class="inlinecode">(<span class="id" type="var">pred</span></span>
<span class="inlinecode"><span class="id" type="var">x</span>)))</span>
(we are omitting type annotations for brevity here).
    fix F 3

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_FixAbs</span></span>
    (\x. if x=0 then 1 else x * (fix F (pred x))) 3

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_AppAbs</span></span>
    if 3=0 then 1 else 3 * (fix F (pred 3))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id"
type="var">ST\_If0\_Nonzero</span></span>
    3 * (fix F (pred 3))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_FixAbs</span></span>
<span class="inlinecode">+</span> <span class="inlinecode"><span
class="id" type="var">ST\_Mult2</span></span>
    3 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 3))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_PredNat</span></span>
<span class="inlinecode">+</span> <span class="inlinecode"><span
class="id" type="var">ST\_Mult2</span></span> <span
class="inlinecode">+</span> <span class="inlinecode"><span class="id"
type="var">ST\_App2</span></span>
    3 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 2)

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_AppAbs</span></span>
<span class="inlinecode">+</span> <span class="inlinecode"><span
class="id" type="var">ST\_Mult2</span></span>
    3 * (if 2=0 then 1 else 2 * (fix F (pred 2)))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id"
type="var">ST\_If0\_Nonzero</span></span> <span
class="inlinecode">+</span> <span class="inlinecode"><span class="id"
type="var">ST\_Mult2</span></span>
    3 * (2 * (fix F (pred 2)))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_FixAbs</span></span>
<span class="inlinecode">+</span> <span class="inlinecode">2</span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode"><span class="id"
type="var">ST\_Mult2</span></span>
    3 * (2 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 2)))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_PredNat</span></span>
<span class="inlinecode">+</span> <span class="inlinecode">2</span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode"><span class="id"
type="var">ST\_Mult2</span></span> <span class="inlinecode">+</span>
<span class="inlinecode"><span class="id"
type="var">ST\_App2</span></span>
    3 * (2 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 1))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_AppAbs</span></span>
<span class="inlinecode">+</span> <span class="inlinecode">2</span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode"><span class="id"
type="var">ST\_Mult2</span></span>
    3 * (2 * (if 1=0 then 1 else 1 * (fix F (pred 1))))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id"
type="var">ST\_If0\_Nonzero</span></span> <span
class="inlinecode">+</span> <span class="inlinecode">2</span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_Mult2</span></span>
    3 * (2 * (1 * (fix F (pred 1))))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_FixAbs</span></span>
<span class="inlinecode">+</span> <span class="inlinecode">3</span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode"><span class="id"
type="var">ST\_Mult2</span></span>
    3 * (2 * (1 * ((\x. if x=0 then 1 else x * (fix F (pred x))) (pred 1))))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_PredNat</span></span>
<span class="inlinecode">+</span> <span class="inlinecode">3</span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode"><span class="id"
type="var">ST\_Mult2</span></span> <span class="inlinecode">+</span>
<span class="inlinecode"><span class="id"
type="var">ST\_App2</span></span>
    3 * (2 * (1 * ((\x. if x=0 then 1 else x * (fix F (pred x))) 0)))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_AppAbs</span></span>
<span class="inlinecode">+</span> <span class="inlinecode">3</span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode"><span class="id"
type="var">ST\_Mult2</span></span>
    3 * (2 * (1 * (if 0=0 then 1 else 0 * (fix F (pred 0)))))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">ST\_If0Zero</span></span>
<span class="inlinecode">+</span> <span class="inlinecode">3</span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode"><span class="id"
type="var">ST\_Mult2</span></span>
    3 * (2 * (1 * 1))

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id"
type="var">ST\_MultNats</span></span> <span class="inlinecode">+</span>
<span class="inlinecode">2</span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="var">ST\_Mult2</span></span>
    3 * (2 * 1)

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id"
type="var">ST\_MultNats</span></span> <span class="inlinecode">+</span>
<span class="inlinecode"><span class="id"
type="var">ST\_Mult2</span></span>
    3 * 2

<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id"
type="var">ST\_MultNats</span></span>
    6

<div class="paragraph">

</div>

#### Exercise: 1 star, optional (halve\_fix) {.section}

Translate this informal recursive definition into one using <span
class="inlinecode"><span class="id" type="var">fix</span></span>:
       halve = 
         λx:Nat. 
            if x=0 then 0 
            else if (pred x)=0 then 0
            else 1 + (halve (pred (pred x))))

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (fact\_steps) {.section}

Write down the sequence of steps that the term <span
class="inlinecode"><span class="id" type="var">fact</span></span> <span
class="inlinecode">1</span> goes through to reduce to a normal form
(assuming the usual reduction rules for arithmetic operations).
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

The ability to form the fixed point of a function of type <span
class="inlinecode"><span class="id" type="var">T</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T</span></span> for any <span class="inlinecode"><span
class="id" type="var">T</span></span> has some surprising consequences.
In particular, it implies that *every* type is inhabited by some term.
To see this, observe that, for every type <span class="inlinecode"><span
class="id" type="var">T</span></span>, we can define the term
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="var">fix</span> (\\<span class="id"
type="var">x</span>:<span class="id" type="var">T.x</span>)
<div class="paragraph">

</div>

</div>

By <span class="inlinecode"><span class="id"
type="var">T\_Fix</span></span> and <span class="inlinecode"><span
class="id" type="var">T\_Abs</span></span>, this term has type <span
class="inlinecode"><span class="id" type="var">T</span></span>. By <span
class="inlinecode"><span class="id" type="var">ST\_FixAbs</span></span>
it reduces to itself, over and over again. Thus it is an *undefined
element* of <span class="inlinecode"><span class="id"
type="var">T</span></span>.
<div class="paragraph">

</div>

More usefully, here's an example using <span class="inlinecode"><span
class="id" type="var">fix</span></span> to define a two-argument
recursive function:
        equal = 
          fix 
            (\eq:Nat->Nat->Bool.
               λm:Nat. λn:Nat.
                 if m=0 then iszero n 
                 else if n=0 then false
                 else eq (pred m) (pred n))

<div class="paragraph">

</div>

And finally, here is an example where <span class="inlinecode"><span
class="id" type="var">fix</span></span> is used to define a *pair* of
recursive functions (illustrating the fact that the type <span
class="inlinecode"><span class="id" type="var">T~1~</span></span> in the
rule <span class="inlinecode"><span class="id"
type="var">T\_Fix</span></span> need not be a function type):
        evenodd = 
          fix 
            (\eo: (Nat->Bool * Nat->Bool).
               let e = λn:Nat. if n=0 then true  else eo.snd (pred n) in
               let o = λn:Nat. if n=0 then false else eo.fst (pred n) in
               (e,o))

        even = evenodd.fst
        odd  = evenodd.snd

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Records {.section}
-------

<div class="paragraph">

</div>

As a final example of a basic extension of the STLC, let's look briefly
at how to define *records* and their types. Intuitively, records can be
obtained from pairs by two kinds of generalization: they are n-ary
products (rather than just binary) and their fields are accessed by
*label* (rather than position).
<div class="paragraph">

</div>

Conceptually, this extension is a straightforward generalization of
pairs and product types, but notationally it becomes a little heavier;
for this reason, we postpone its formal treatment to a separate chapter
(<span class="inlinecode"><span class="id"
type="var">Records</span></span>).
<div class="paragraph">

</div>

Records are not included in the extended exercise below, but they will
be useful to motivate the <span class="inlinecode"><span class="id"
type="var">Sub</span></span> chapter.
<div class="paragraph">

</div>

Syntax:
           t ::=                          Terms
               | ...
               | {i1=t1, ..., in=tn}         record 
               | t.i                         projection

           v ::=                          Values
               | ...
               | {i1=v1, ..., in=vn}         record value

           T ::=                          Types
               | ...
               | {i1:T1, ..., in:Tn}         record type

Intuitively, the generalization is pretty obvious. But it's worth
noticing that what we've actually written is rather informal: in
particular, we've written "<span class="inlinecode">...</span>" in
several places to mean "any number of these," and we've omitted explicit
mention of the usual side-condition that the labels of a record should
not contain repetitions.
<div class="paragraph">

</div>

It is possible to devise informal notations that are more precise, but
these tend to be quite heavy and to obscure the main points of the
definitions. So we'll leave these a bit loose here (they are informal
anyway, after all) and do the work of tightening things up elsewhere (in
chapter <span class="inlinecode"><span class="id"
type="var">Records</span></span>).
<div class="paragraph">

</div>

<div class="paragraph">

</div>

Reduction:
ti <span style="font-family: arial;">⇒</span> ti'
(ST\_Rcd)  

------------------------------------------------------------------------

{i1=v~1~, ..., im=vm, in=ti, ...}
<span
style="font-family: arial;">⇒</span> {i1=v~1~, ..., im=vm, in=ti', ...}
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Proj1)  

------------------------------------------------------------------------

t~1~.i <span style="font-family: arial;">⇒</span> t~1~'.i
  
(ST\_ProjRcd)  

------------------------------------------------------------------------

{..., i=vi, ...}.i <span style="font-family: arial;">⇒</span> vi
Again, these rules are a bit informal. For example, the first rule is
intended to be read "if <span class="inlinecode"><span class="id"
type="var">ti</span></span> is the leftmost field that is not a value
and if <span class="inlinecode"><span class="id"
type="var">ti</span></span> steps to <span class="inlinecode"><span
class="id" type="var">ti'</span></span>, then the whole record steps..."
In the last rule, the intention is that there should only be one field
called i, and that all the other fields must contain values.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

Typing:
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : T~1~     ...     <span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> tn : Tn
(T\_Rcd)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> {i1=t~1~, ..., in=tn} : {i1:T~1~, ..., in:Tn}
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t : {..., i:Ti, ...}
(T\_Proj)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t.i : Ti
<div class="paragraph">

</div>

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Encoding Records (Optional) {.section}

<div class="paragraph">

</div>

There are several ways to make the above definitions precise.
<div class="paragraph">

</div>

-   We can directly formalize the syntactic forms and inference rules,
    staying as close as possible to the form we've given them above.
    This is conceptually straightforward, and it's probably what we'd
    want to do if we were building a real compiler — in particular, it
    will allow is to print error messages in the form that programmers
    will find easy to understand. But the formal versions of the rules
    will not be pretty at all!
    <div class="paragraph">

    </div>

-   We could look for a smoother way of presenting records — for
    example, a binary presentation with one constructor for the empty
    record and another constructor for adding a single field to an
    existing record, instead of a single monolithic constructor that
    builds a whole record at once. This is the right way to go if we are
    primarily interested in studying the metatheory of the calculi with
    records, since it leads to clean and elegant definitions and proofs.
    Chapter <span class="inlinecode"><span class="id"
    type="var">Records</span></span> shows how this can be done.
    <div class="paragraph">

    </div>

-   Alternatively, if we like, we can avoid formalizing records
    altogether, by stipulating that record notations are just informal
    shorthands for more complex expressions involving pairs and product
    types. We sketch this approach here.

<div class="paragraph">

</div>

First, observe that we can encode arbitrary-size tuples using nested
pairs and the <span class="inlinecode"><span class="id"
type="var">unit</span></span> value. To avoid overloading the pair
notation <span class="inlinecode">(<span class="id"
type="var">t~1~</span>,<span class="id" type="var">t~2~</span>)</span>,
we'll use curly braces without labels to write down tuples, so <span
class="inlinecode">{}</span> is the empty tuple, <span
class="inlinecode">{5}</span> is a singleton tuple, <span
class="inlinecode">{5,6}</span> is a 2-tuple (morally the same as a
pair), <span class="inlinecode">{5,6,7}</span> is a triple, etc.
        {}                 ---->  unit
        {t1, t2, ..., tn}  ---->  (t1, trest)
                                  where {t2, ..., tn} ----> trest

Similarly, we can encode tuple types using nested product types:
        {}                 ---->  Unit
        {T1, T2, ..., Tn}  ---->  T1 * TRest
                                  where {T2, ..., Tn} ----> TRest

The operation of projecting a field from a tuple can be encoded using a
sequence of second projections followed by a first projection:
        t.0        ---->  t.fst
        t.(n+1)    ---->  (t.snd).n

<div class="paragraph">

</div>

Next, suppose that there is some total ordering on record labels, so
that we can associate each label with a unique natural number. This
number is called the *position* of the label. For example, we might
assign positions like this:
          LABEL   POSITION
          a       0
          b       1
          c       2
          ...     ...
          foo     1004
          ...     ...
          bar     10562
          ...     ...

<div class="paragraph">

</div>

We use these positions to encode record values as tuples (i.e., as
nested pairs) by sorting the fields according to their positions. For
example:
          {a=5, b=6}      ---->   {5,6}
          {a=5, c=7}      ---->   {5,unit,7}
          {c=7, a=5}      ---->   {5,unit,7}
          {c=5, b=3}      ---->   {unit,3,5}
          {f=8,c=5,a=7}   ---->   {7,unit,5,unit,unit,8}
          {f=8,c=5}       ---->   {unit,unit,5,unit,unit,8}

Note that each field appears in the position associated with its label,
that the size of the tuple is determined by the label with the highest
position, and that we fill in unused positions with <span
class="inlinecode"><span class="id" type="var">unit</span></span>.
<div class="paragraph">

</div>

We do exactly the same thing with record types:
          {a:Nat, b:Nat}      ---->   {Nat,Nat}
          {c:Nat, a:Nat}      ---->   {Nat,Unit,Nat}
          {f:Nat,c:Nat}       ---->   {Unit,Unit,Nat,Unit,Unit,Nat}

<div class="paragraph">

</div>

Finally, record projection is encoded as a tuple projection from the
appropriate position:
          t.l  ---->  t.(position of l)

<div class="paragraph">

</div>

It is not hard to check that all the typing rules for the original
"direct" presentation of records are validated by this encoding. (The
reduction rules are "almost validated" — not quite, because the encoding
reorders fields.)
<div class="paragraph">

</div>

Of course, this encoding will not be very efficient if we happen to use
a record with label <span class="inlinecode"><span class="id"
type="var">bar</span></span>! But things are not actually as bad as they
might seem: for example, if we assume that our compiler can see the
whole program at the same time, we can *choose* the numbering of labels
so that we assign small positions to the most frequently used labels.
Indeed, there are industrial compilers that essentially do this!
<div class="paragraph">

</div>

### Variants (Optional Reading) {.section}

<div class="paragraph">

</div>

Just as products can be generalized to records, sums can be generalized
to n-ary labeled types called *variants*. Instead of <span
class="inlinecode"><span class="id" type="var">T~1~</span>+<span
class="id" type="var">T~2~</span></span>, we can write something like
<span class="inlinecode">\<<span class="id" type="var">l1</span>:<span
class="id" type="var">T~1~</span>,<span class="id"
type="var">l2</span>:<span class="id" type="var">T~2~</span>,...<span
class="id" type="var">ln</span>:<span class="id"
type="var">Tn</span>\></span> where <span class="inlinecode"><span
class="id" type="var">l1</span></span>,<span class="inlinecode"><span
class="id" type="var">l2</span></span>,... are field labels which are
used both to build instances and as case arm labels.
<div class="paragraph">

</div>

These n-ary variants give us almost enough mechanism to build arbitrary
inductive data types like lists and trees from scratch — the only thing
missing is a way to allow *recursion* in type definitions. We won't
cover this here, but detailed treatments can be found in many textbooks
— e.g., Types and Programming Languages.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Exercise: Formalizing the Extensions {.section}
====================================

<div class="paragraph">

</div>

#### Exercise: 4 stars, optional (STLC\_extensions) {.section}

In this problem you will formalize a couple of the extensions described
above. We've provided the necessary additions to the syntax of terms and
types, and we've included a few examples that you can test your
definitions with to make sure they are working as expected. You'll fill
in the rest of the definitions and extend all the proofs accordingly.
<div class="paragraph">

</div>

To get you started, we've provided implementations for:
<div class="paragraph">

</div>

-   numbers
-   pairs and units
-   sums
-   lists

<div class="paragraph">

</div>

You need to complete the implementations for:
<div class="paragraph">

</div>

-   let (which involves binding)
-   <span class="inlinecode"><span class="id"
    type="var">fix</span></span>

<div class="paragraph">

</div>

A good strategy is to work on the extensions one at a time, in multiple
passes, rather than trying to work through the file from start to finish
in a single pass. For each definition or proof, begin by reading
carefully through the parts that are provided for you, referring to the
text in the <span class="inlinecode"><span class="id"
type="var">Stlc</span></span> chapter for high-level intuitions and the
embedded comments for detailed mechanics.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">STLCExtended</span>.\
\

</div>

<div class="doc">

### Syntax and Operational Semantics {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ty</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">TArrow</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TNat</span> : <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TUnit</span> : <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TProd</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TSum</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TList</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span> "T\_cases" <span
class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "TArrow" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "TNat"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "TProd" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"TUnit"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "TSum" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "TList"
].\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">tm</span> : <span class="id" type="keyword">Type</span> :=\
   <span class="comment">(\* pure STLC \*)</span>\
   | <span class="id" type="var">tvar</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">tapp</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tabs</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   <span class="comment">(\* numbers \*)</span>\
   | <span class="id" type="var">tnat</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">tsucc</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">tpred</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">tmult</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tif0</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   <span class="comment">(\* pairs \*)</span>\
   | <span class="id" type="var">tpair</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tfst</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">tsnd</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   <span class="comment">(\* units \*)</span>\
   | <span class="id" type="var">tunit</span> : <span class="id"
type="var">tm</span>\
   <span class="comment">(\* let \*)</span>\
   | <span class="id" type="var">tlet</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
           <span class="comment">(\* i.e., <span
class="inlinecode"><span class="id" type="keyword">let</span></span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> <span class="inlinecode"><span
class="id" type="keyword">in</span></span> <span
class="inlinecode"><span class="id"
type="var">t~2~</span></span> \*)</span>\
   <span class="comment">(\* sums \*)</span>\
   | <span class="id" type="var">tinl</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tinr</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tcase</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">id</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">id</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
           <span class="comment">(\* i.e., <span
class="inlinecode"><span class="id" type="tactic">case</span></span>
<span class="inlinecode"><span class="id" type="var">t0</span></span>
<span class="inlinecode"><span class="id" type="var">of</span></span>
<span class="inlinecode"><span class="id" type="var">inl</span></span>
<span class="inlinecode"><span class="id" type="var">x1</span></span>
<span class="inlinecode">⇒</span> <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> <span
class="inlinecode">|</span> <span class="inlinecode"><span class="id"
type="var">inr</span></span> <span class="inlinecode"><span class="id"
type="var">x2</span></span> <span class="inlinecode">⇒</span> <span
class="inlinecode"><span class="id"
type="var">t~2~</span></span> \*)</span>\
   <span class="comment">(\* lists \*)</span>\
   | <span class="id" type="var">tnil</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">tcons</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tlcase</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">id</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
           <span class="comment">(\* i.e., <span
class="inlinecode"><span class="id" type="var">lcase</span></span> <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> <span
class="inlinecode"><span class="id" type="var">of</span></span> <span
class="inlinecode">|</span> <span class="inlinecode"><span class="id"
type="var">nil</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">t~2~</span></span> <span
class="inlinecode">|</span> <span class="inlinecode"><span class="id"
type="var">x</span>::<span class="id" type="var">y</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id"
type="var">t~3~</span></span> \*)</span>\
   <span class="comment">(\* fix \*)</span>\
   | <span class="id" type="var">tfix</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>.\
\

</div>

<div class="doc">

Note that, for brevity, we've omitted booleans and instead provided a
single <span class="inlinecode"><span class="id"
type="var">if0</span></span> form combining a zero test and a
conditional. That is, instead of writing
           if x = 0 then ... else ...

we'll write this:
           if0 x then ... else ...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Tactic Notation</span> "t\_cases" <span
class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tvar" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tapp"
| <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tabs"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tnat" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tsucc"
| <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tpred"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tmult" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tif0"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tpair" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tfst"
| <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tsnd"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tunit" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tlet"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tinl" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tinr"
| <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tcase"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tnil" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tcons"
| <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tlcase"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tfix" ].\
\

</div>

<div class="doc">

### Substitution {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="tactic">subst</span> (<span class="id" type="var">x</span>:<span
class="id" type="var">id</span>) (<span class="id"
type="var">s</span>:<span class="id" type="var">tm</span>) (<span
class="id" type="var">t</span>:<span class="id" type="var">tm</span>) :
<span class="id" type="var">tm</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">t</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">tvar</span> <span class="id"
type="var">y</span> ⇒\
       <span class="id" type="keyword">if</span> <span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">s</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">t</span>\
   | <span class="id" type="var">tabs</span> <span class="id"
type="var">y</span> <span class="id" type="var">T</span> <span
class="id" type="var">t~1~</span> ⇒\
       <span class="id" type="var">tabs</span> <span class="id"
type="var">y</span> <span class="id" type="var">T</span> (<span
class="id" type="keyword">if</span> <span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">t~1~</span> <span
class="id" type="keyword">else</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id"
type="var">t~1~</span>))\
   | <span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒\
       <span class="id" type="var">tapp</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">tnat</span> <span class="id"
type="var">n</span> ⇒\
       <span class="id" type="var">tnat</span> <span class="id"
type="var">n</span>\
   | <span class="id" type="var">tsucc</span> <span class="id"
type="var">t~1~</span> ⇒\
       <span class="id" type="var">tsucc</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">tpred</span> <span class="id"
type="var">t~1~</span> ⇒\
       <span class="id" type="var">tpred</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">tmult</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒\
       <span class="id" type="var">tmult</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">tif0</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> ⇒\
       <span class="id" type="var">tif0</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>) (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~3~</span>)\
   | <span class="id" type="var">tpair</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒\
       <span class="id" type="var">tpair</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">tfst</span> <span class="id"
type="var">t~1~</span> ⇒\
       <span class="id" type="var">tfst</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">tsnd</span> <span class="id"
type="var">t~1~</span> ⇒\
       <span class="id" type="var">tsnd</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">tunit</span> ⇒ <span class="id"
type="var">tunit</span>\
   <span class="comment">(\* FILL IN HERE \*)</span>\
   | <span class="id" type="var">tinl</span> <span class="id"
type="var">T</span> <span class="id" type="var">t~1~</span> ⇒\
       <span class="id" type="var">tinl</span> <span class="id"
type="var">T</span> (<span class="id" type="tactic">subst</span> <span
class="id" type="var">x</span> <span class="id" type="var">s</span>
<span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">tinr</span> <span class="id"
type="var">T</span> <span class="id" type="var">t~1~</span> ⇒\
       <span class="id" type="var">tinr</span> <span class="id"
type="var">T</span> (<span class="id" type="tactic">subst</span> <span
class="id" type="var">x</span> <span class="id" type="var">s</span>
<span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">tcase</span> <span class="id"
type="var">t0</span> <span class="id" type="var">y1</span> <span
class="id" type="var">t~1~</span> <span class="id" type="var">y2</span>
<span class="id" type="var">t~2~</span> ⇒\
       <span class="id" type="var">tcase</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t0</span>)\
          <span class="id" type="var">y1</span> (<span class="id"
type="keyword">if</span> <span class="id" type="var">eq\_id\_dec</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y1</span> <span class="id" type="keyword">then</span> <span
class="id" type="var">t~1~</span> <span class="id"
type="keyword">else</span> (<span class="id" type="tactic">subst</span>
<span class="id" type="var">x</span> <span class="id"
type="var">s</span> <span class="id" type="var">t~1~</span>))\
          <span class="id" type="var">y2</span> (<span class="id"
type="keyword">if</span> <span class="id" type="var">eq\_id\_dec</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y2</span> <span class="id" type="keyword">then</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="keyword">else</span> (<span class="id" type="tactic">subst</span>
<span class="id" type="var">x</span> <span class="id"
type="var">s</span> <span class="id" type="var">t~2~</span>))\
   | <span class="id" type="var">tnil</span> <span class="id"
type="var">T</span> ⇒\
       <span class="id" type="var">tnil</span> <span class="id"
type="var">T</span>\
   | <span class="id" type="var">tcons</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒\
       <span class="id" type="var">tcons</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">tlcase</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">y1</span> <span class="id" type="var">y2</span>
<span class="id" type="var">t~3~</span> ⇒\
       <span class="id" type="var">tlcase</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>) <span class="id" type="var">y1</span>
<span class="id" type="var">y2</span>\
         (<span class="id" type="keyword">if</span> <span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y1</span> <span class="id"
type="keyword">then</span>\
            <span class="id" type="var">t~3~</span>\
          <span class="id" type="keyword">else</span> <span class="id"
type="keyword">if</span> <span class="id" type="var">eq\_id\_dec</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y2</span> <span class="id" type="keyword">then</span> <span
class="id" type="var">t~3~</span>\
               <span class="id" type="keyword">else</span> (<span
class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~3~</span>))\
 <span class="comment">(\* FILL IN HERE \*)</span>\
   | <span class="id" type="var">\_</span> ⇒ <span class="id"
type="var">t</span> <span
class="comment">(\* ... and delete this line \*)</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Notation</span> "'[' x ':=' s ']' t" :=
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 20).\
\

</div>

<div class="doc">

### Reduction {.section}

<div class="paragraph">

</div>

Next we define the values of our language.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">value</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">v\_abs</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>,\
       <span class="id" type="var">value</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>)\
   <span class="comment">(\* Numbers are values: \*)</span>\
   | <span class="id" type="var">v\_nat</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span>,\
       <span class="id" type="var">value</span> (<span class="id"
type="var">tnat</span> <span class="id" type="var">n1</span>)\
   <span
class="comment">(\* A pair is a value if both components are: \*)</span>\
   | <span class="id" type="var">v\_pair</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">v~2~</span>,\
       <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">value</span> <span class="id"
type="var">v~2~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">value</span> (<span class="id"
type="var">tpair</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">v~2~</span>)\
   <span class="comment">(\* A unit is always a value \*)</span>\
   | <span class="id" type="var">v\_unit</span> : <span class="id"
type="var">value</span> <span class="id" type="var">tunit</span>\
   <span class="comment">(\* A tagged value is a value:  \*)</span>\
   | <span class="id" type="var">v\_inl</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">v</span>
<span class="id" type="var">T</span>,\
       <span class="id" type="var">value</span> <span class="id"
type="var">v</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">value</span> (<span class="id"
type="var">tinl</span> <span class="id" type="var">T</span> <span
class="id" type="var">v</span>)\
   | <span class="id" type="var">v\_inr</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">v</span>
<span class="id" type="var">T</span>,\
       <span class="id" type="var">value</span> <span class="id"
type="var">v</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">value</span> (<span class="id"
type="var">tinr</span> <span class="id" type="var">T</span> <span
class="id" type="var">v</span>)\
   <span
class="comment">(\* A list is a value iff its head and tail are values: \*)</span>\
   | <span class="id" type="var">v\_lnil</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T</span>, <span class="id" type="var">value</span> (<span
class="id" type="var">tnil</span> <span class="id" type="var">T</span>)\
   | <span class="id" type="var">v\_lcons</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">vl</span>,\
       <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">value</span> <span class="id"
type="var">vl</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">value</span> (<span class="id"
type="var">tcons</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">vl</span>)\
   .\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">value</span>.\
\
 <span class="id" type="keyword">Reserved Notation</span> "t~1~ '<span
style="font-family: arial;">⇒</span>' t~2~" (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">step</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">ST\_AppAbs</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span> <span class="id" type="var">v~2~</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~2~</span> <span style="font-family: arial;">→</span>\
          (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>) <span class="id" type="var">v~2~</span>) <span
style="font-family: arial;">⇒</span> [<span class="id"
type="var">x</span>:=<span class="id" type="var">v~2~</span>]<span
class="id" type="var">t~12~</span>\
   | <span class="id" type="var">ST\_App1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
          <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
          (<span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">ST\_App2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
          (<span class="id" type="var">tapp</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>)\
   <span class="comment">(\* nats \*)</span>\
   | <span class="id" type="var">ST\_Succ1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span>,\
        <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
        (<span class="id" type="var">tsucc</span> <span class="id"
type="var">t~1~</span>) <span style="font-family: arial;">⇒</span>
(<span class="id" type="var">tsucc</span> <span class="id"
type="var">t~1~'</span>)\
   | <span class="id" type="var">ST\_SuccNat</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span>,\
        (<span class="id" type="var">tsucc</span> (<span class="id"
type="var">tnat</span> <span class="id" type="var">n1</span>)) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tnat</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n1</span>))\
   | <span class="id" type="var">ST\_Pred</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span>,\
        <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
        (<span class="id" type="var">tpred</span> <span class="id"
type="var">t~1~</span>) <span style="font-family: arial;">⇒</span>
(<span class="id" type="var">tpred</span> <span class="id"
type="var">t~1~'</span>)\
   | <span class="id" type="var">ST\_PredNat</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span>,\
        (<span class="id" type="var">tpred</span> (<span class="id"
type="var">tnat</span> <span class="id" type="var">n1</span>)) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tnat</span> (<span class="id" type="var">pred</span> <span
class="id" type="var">n1</span>))\
   | <span class="id" type="var">ST\_Mult1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
        <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
        (<span class="id" type="var">tmult</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tmult</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">ST\_Mult2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
        <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
        <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
        (<span class="id" type="var">tmult</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tmult</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>)\
   | <span class="id" type="var">ST\_MultNats</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">n2</span>,\
        (<span class="id" type="var">tmult</span> (<span class="id"
type="var">tnat</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">tnat</span> <span class="id"
type="var">n2</span>)) <span style="font-family: arial;">⇒</span> (<span
class="id" type="var">tnat</span> (<span class="id"
type="var">mult</span> <span class="id" type="var">n1</span> <span
class="id" type="var">n2</span>))\
   | <span class="id" type="var">ST\_If01</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>,\
        <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
        (<span class="id" type="var">tif0</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tif0</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>)\
   | <span class="id" type="var">ST\_If0Zero</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
        (<span class="id" type="var">tif0</span> (<span class="id"
type="var">tnat</span> 0) <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span>) <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~</span>\
   | <span class="id" type="var">ST\_If0Nonzero</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>,\
        (<span class="id" type="var">tif0</span> (<span class="id"
type="var">tnat</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>)) <span class="id" type="var">t~2~</span>
<span class="id" type="var">t~3~</span>) <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~3~</span>\
   <span class="comment">(\* pairs \*)</span>\
   | <span class="id" type="var">ST\_Pair1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
         <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tpair</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tpair</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">ST\_Pair2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
         <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
         <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tpair</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tpair</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>)\
   | <span class="id" type="var">ST\_Fst1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span>,\
         <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tfst</span> <span class="id"
type="var">t~1~</span>) <span style="font-family: arial;">⇒</span>
(<span class="id" type="var">tfst</span> <span class="id"
type="var">t~1~'</span>)\
   | <span class="id" type="var">ST\_FstPair</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">v~2~</span>,\
         <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
         <span class="id" type="var">value</span> <span class="id"
type="var">v~2~</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tfst</span> (<span class="id"
type="var">tpair</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">v~2~</span>)) <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">v~1~</span>\
   | <span class="id" type="var">ST\_Snd1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span>,\
         <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tsnd</span> <span class="id"
type="var">t~1~</span>) <span style="font-family: arial;">⇒</span>
(<span class="id" type="var">tsnd</span> <span class="id"
type="var">t~1~'</span>)\
   | <span class="id" type="var">ST\_SndPair</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">v~2~</span>,\
         <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
         <span class="id" type="var">value</span> <span class="id"
type="var">v~2~</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tsnd</span> (<span class="id"
type="var">tpair</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">v~2~</span>)) <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">v~2~</span>\
   <span class="comment">(\* let \*)</span>\
   <span class="comment">(\* FILL IN HERE \*)</span>\
   <span class="comment">(\* sums \*)</span>\
   | <span class="id" type="var">ST\_Inl</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">T</span>,\
         <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tinl</span> <span class="id"
type="var">T</span> <span class="id" type="var">t~1~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tinl</span> <span class="id" type="var">T</span> <span
class="id" type="var">t~1~'</span>)\
   | <span class="id" type="var">ST\_Inr</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">T</span>,\
         <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tinr</span> <span class="id"
type="var">T</span> <span class="id" type="var">t~1~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tinr</span> <span class="id" type="var">T</span> <span
class="id" type="var">t~1~'</span>)\
   | <span class="id" type="var">ST\_Case</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t0</span> <span class="id" type="var">t0'</span> <span
class="id" type="var">x1</span> <span class="id" type="var">t~1~</span>
<span class="id" type="var">x2</span> <span class="id"
type="var">t~2~</span>,\
         <span class="id" type="var">t0</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t0'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tcase</span> <span class="id"
type="var">t0</span> <span class="id" type="var">x1</span> <span
class="id" type="var">t~1~</span> <span class="id" type="var">x2</span>
<span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tcase</span> <span class="id" type="var">t0'</span> <span
class="id" type="var">x1</span> <span class="id" type="var">t~1~</span>
<span class="id" type="var">x2</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">ST\_CaseInl</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v0</span> <span class="id" type="var">x1</span> <span
class="id" type="var">t~1~</span> <span class="id" type="var">x2</span>
<span class="id" type="var">t~2~</span> <span class="id"
type="var">T</span>,\
         <span class="id" type="var">value</span> <span class="id"
type="var">v0</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tcase</span> (<span class="id"
type="var">tinl</span> <span class="id" type="var">T</span> <span
class="id" type="var">v0</span>) <span class="id" type="var">x1</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">x2</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> [<span class="id"
type="var">x1</span>:=<span class="id" type="var">v0</span>]<span
class="id" type="var">t~1~</span>\
   | <span class="id" type="var">ST\_CaseInr</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v0</span> <span class="id" type="var">x1</span> <span
class="id" type="var">t~1~</span> <span class="id" type="var">x2</span>
<span class="id" type="var">t~2~</span> <span class="id"
type="var">T</span>,\
         <span class="id" type="var">value</span> <span class="id"
type="var">v0</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tcase</span> (<span class="id"
type="var">tinr</span> <span class="id" type="var">T</span> <span
class="id" type="var">v0</span>) <span class="id" type="var">x1</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">x2</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> [<span class="id"
type="var">x2</span>:=<span class="id" type="var">v0</span>]<span
class="id" type="var">t~2~</span>\
   <span class="comment">(\* lists \*)</span>\
   | <span class="id" type="var">ST\_Cons1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
        <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
        (<span class="id" type="var">tcons</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tcons</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">ST\_Cons2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
        <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
        <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
        (<span class="id" type="var">tcons</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tcons</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>)\
   | <span class="id" type="var">ST\_Lcase1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">x1</span>
<span class="id" type="var">x2</span> <span class="id"
type="var">t~3~</span>,\
        <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
        (<span class="id" type="var">tlcase</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">x1</span> <span class="id" type="var">x2</span>
<span class="id" type="var">t~3~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tlcase</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">x1</span>
<span class="id" type="var">x2</span> <span class="id"
type="var">t~3~</span>)\
   | <span class="id" type="var">ST\_LcaseNil</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">T</span>
<span class="id" type="var">t~2~</span> <span class="id"
type="var">x1</span> <span class="id" type="var">x2</span> <span
class="id" type="var">t~3~</span>,\
        (<span class="id" type="var">tlcase</span> (<span class="id"
type="var">tnil</span> <span class="id" type="var">T</span>) <span
class="id" type="var">t~2~</span> <span class="id" type="var">x1</span>
<span class="id" type="var">x2</span> <span class="id"
type="var">t~3~</span>) <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~2~</span>\
   | <span class="id" type="var">ST\_LcaseCons</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">vl</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">x1</span>
<span class="id" type="var">x2</span> <span class="id"
type="var">t~3~</span>,\
        <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
        <span class="id" type="var">value</span> <span class="id"
type="var">vl</span> <span style="font-family: arial;">→</span>\
        (<span class="id" type="var">tlcase</span> (<span class="id"
type="var">tcons</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">vl</span>) <span class="id" type="var">t~2~</span>
<span class="id" type="var">x1</span> <span class="id"
type="var">x2</span> <span class="id" type="var">t~3~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x2</span> <span
class="id" type="var">vl</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x1</span> <span
class="id" type="var">v~1~</span> <span class="id"
type="var">t~3~</span>))\
   <span class="comment">(\* fix \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\
 <span class="id" type="keyword">where</span> "t~1~ '<span
style="font-family: arial;">⇒</span>' t~2~" := (<span class="id"
type="var">step</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>).\
\
 <span class="id" type="keyword">Tactic Notation</span> "step\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_AppAbs" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_App1" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "ST\_App2"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Succ1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_SuccNat"\
     | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Pred1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_PredNat"\
     | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Mult1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Mult2"\
     | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_MultNats" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_If01"\
     | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_If0Zero" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_If0Nonzero"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Pair1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Pair2"\
     | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Fst1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_FstPair"\
     | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Snd1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_SndPair"\
     <span class="comment">(\* FILL IN HERE \*)</span>\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Inl" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Inr" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "ST\_Case"\
     | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_CaseInl" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_CaseInr"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Cons1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Cons2" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "ST\_Lcase1"\
     | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_LcaseNil" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_LcaseCons"\
 <span class="comment">(\* FILL IN HERE \*)</span>\
   ].\
\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">multistep</span> := (<span class="id" type="var">multi</span>
<span class="id" type="var">step</span>).\
 <span class="id" type="keyword">Notation</span> "t~1~ '<span
style="font-family: arial;">⇒\*</span>' t~2~" := (<span class="id"
type="var">multistep</span> <span class="id" type="var">t~1~</span>
<span class="id" type="var">t~2~</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id" type="var">step</span>.\
\

</div>

<div class="doc">

### Typing {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">context</span> := <span class="id"
type="var">partial\_map</span> <span class="id" type="var">ty</span>.\
\

</div>

<div class="doc">

Next we define the typing rules. These are nearly direct transcriptions
of the inference rules shown above.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> "Gamma '<span
style="font-family: arial;">⊢</span>' t '∈' T" (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">has\_type</span> : <span class="id" type="var">context</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   <span class="comment">(\* Typing rules for proper terms \*)</span>\
   | <span class="id" type="var">T\_Var</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
class="id" type="var">x</span> = <span class="id" type="var">Some</span>
<span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) ∈ <span
class="id" type="var">T</span>\
   | <span class="id" type="var">T\_Abs</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T~11~</span> <span
class="id" type="var">T~12~</span> <span class="id"
type="var">t~12~</span>,\
       (<span class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T~11~</span>) <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~12~</span> ∈ <span class="id" type="var">T~12~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>) ∈ (<span class="id" type="var">TArrow</span>
<span class="id" type="var">T~11~</span> <span class="id"
type="var">T~12~</span>)\
   | <span class="id" type="var">T\_App</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ (<span class="id" type="var">TArrow</span>
<span class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) ∈ <span class="id"
type="var">T~2~</span>\
   <span class="comment">(\* nats \*)</span>\
   | <span class="id" type="var">T\_Nat</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">n1</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tnat</span> <span class="id" type="var">n1</span>) ∈ <span
class="id" type="var">TNat</span>\
   | <span class="id" type="var">T\_Succ</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tsucc</span> <span class="id" type="var">t~1~</span>) ∈ <span
class="id" type="var">TNat</span>\
   | <span class="id" type="var">T\_Pred</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tpred</span> <span class="id" type="var">t~1~</span>) ∈ <span
class="id" type="var">TNat</span>\
   | <span class="id" type="var">T\_Mult</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tmult</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) ∈ <span class="id"
type="var">TNat</span>\
   | <span class="id" type="var">T\_If0</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> <span class="id"
type="var">T~1~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~3~</span> ∈ <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tif0</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>) ∈ <span class="id" type="var">T~1~</span>\
   <span class="comment">(\* pairs \*)</span>\
   | <span class="id" type="var">T\_Pair</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T~2~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tpair</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) ∈ (<span class="id"
type="var">TProd</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>)\
   | <span class="id" type="var">T\_Fst</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ (<span class="id" type="var">TProd</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tfst</span> <span class="id" type="var">t</span>) ∈ <span
class="id" type="var">T~1~</span>\
   | <span class="id" type="var">T\_Snd</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ (<span class="id" type="var">TProd</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tsnd</span> <span class="id" type="var">t</span>) ∈ <span
class="id" type="var">T~2~</span>\
   <span class="comment">(\* unit \*)</span>\
   | <span class="id" type="var">T\_Unit</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tunit</span> ∈ <span class="id" type="var">TUnit</span>\
   <span class="comment">(\* let \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
   <span class="comment">(\* sums \*)</span>\
   | <span class="id" type="var">T\_Inl</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tinl</span> <span class="id" type="var">T~2~</span> <span
class="id" type="var">t~1~</span>) ∈ (<span class="id"
type="var">TSum</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>)\
   | <span class="id" type="var">T\_Inr</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T~2~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tinr</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">t~2~</span>) ∈ (<span class="id"
type="var">TSum</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>)\
   | <span class="id" type="var">T\_Case</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t0</span> <span class="id" type="var">x1</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">x2</span> <span
class="id" type="var">T~2~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">T</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t0</span> ∈ (<span class="id" type="var">TSum</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x1</span> <span class="id" type="var">T~1~</span>) <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       (<span class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x2</span> <span class="id" type="var">T~2~</span>) <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tcase</span> <span class="id" type="var">t0</span> <span
class="id" type="var">x1</span> <span class="id" type="var">t~1~</span>
<span class="id" type="var">x2</span> <span class="id"
type="var">t~2~</span>) ∈ <span class="id" type="var">T</span>\
   <span class="comment">(\* lists \*)</span>\
   | <span class="id" type="var">T\_Nil</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">T</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tnil</span> <span class="id" type="var">T</span>) ∈ (<span
class="id" type="var">TList</span> <span class="id"
type="var">T</span>)\
   | <span class="id" type="var">T\_Cons</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">T~1~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ (<span class="id" type="var">TList</span> <span
class="id" type="var">T~1~</span>) <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tcons</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) ∈ (<span class="id"
type="var">TList</span> <span class="id" type="var">T~1~</span>)\
   | <span class="id" type="var">T\_Lcase</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">x1</span>
<span class="id" type="var">x2</span> <span class="id"
type="var">t~3~</span> <span class="id" type="var">T~2~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ (<span class="id" type="var">TList</span> <span
class="id" type="var">T~1~</span>) <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T~2~</span> <span
style="font-family: arial;">→</span>\
       (<span class="id" type="var">extend</span> (<span class="id"
type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x2</span> (<span class="id" type="var">TList</span> <span
class="id" type="var">T~1~</span>)) <span class="id"
type="var">x1</span> <span class="id" type="var">T~1~</span>) <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~3~</span> ∈ <span class="id" type="var">T~2~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tlcase</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">x1</span>
<span class="id" type="var">x2</span> <span class="id"
type="var">t~3~</span>) ∈ <span class="id" type="var">T~2~</span>\
   <span class="comment">(\* fix \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\
 <span class="id" type="keyword">where</span> "Gamma '<span
style="font-family: arial;">⊢</span>' t '∈' T" := (<span class="id"
type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span>).\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">has\_type</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span>
"has\_type\_cases" <span class="id" type="var">tactic</span>(<span
class="id" type="var">first</span>) <span class="id"
type="var">ident</span>(<span class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Var" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_Abs" | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_App"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Nat" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_Succ" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "T\_Pred"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Mult" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_If0"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Pair" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_Fst" | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Snd"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Unit"\
 <span class="comment">(\* let \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Inl" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_Inr" | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Case"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Nil" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_Cons" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "T\_Lcase"\
 <span class="comment">(\* fix \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
 ].\
\

</div>

<div class="doc">

Examples {.section}
--------

<div class="paragraph">

</div>

This section presents formalized versions of the examples from above
(plus several more). The ones at the beginning focus on specific
features; you can use these to make sure your definition of a given
feature is reasonable before moving on to extending the proofs later in
the file with the cases relating to this feature. The later examples
require all the features together, so you'll need to come back to these
when you've got all the definitions filled in.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Examples</span>.\
\

</div>

<div class="doc">

### Preliminaries {.section}

<div class="paragraph">

</div>

First, let's define a few variable names:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">a</span> := (<span class="id" type="var">Id</span> 0).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">f</span> := (<span class="id" type="var">Id</span> 1).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">g</span> := (<span class="id" type="var">Id</span> 2).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">l</span> := (<span class="id" type="var">Id</span> 3).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">k</span> := (<span class="id" type="var">Id</span> 6).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">i1</span> := (<span class="id" type="var">Id</span> 7).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">i2</span> := (<span class="id" type="var">Id</span> 8).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">x</span> := (<span class="id" type="var">Id</span> 9).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">y</span> := (<span class="id" type="var">Id</span> 10).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">processSum</span> := (<span class="id" type="var">Id</span>
11).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">n</span> := (<span class="id" type="var">Id</span> 12).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">eq</span> := (<span class="id" type="var">Id</span> 13).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">m</span> := (<span class="id" type="var">Id</span> 14).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">evenodd</span> := (<span class="id" type="var">Id</span>
15).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">even</span> := (<span class="id" type="var">Id</span> 16).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">odd</span> := (<span class="id" type="var">Id</span> 17).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">eo</span> := (<span class="id" type="var">Id</span> 18).\
\

</div>

<div class="doc">

Next, a bit of Coq hackery to automate searching for typing derivations.
You don't need to understand this bit in detail — just have a look over
it so that you'll know what to look for if you ever find yourself
needing to make custom extensions to <span class="inlinecode"><span
class="id" type="tactic">auto</span></span>.
<div class="paragraph">

</div>

The following <span class="inlinecode"><span class="id"
type="keyword">Hint</span></span> declarations say that, whenever <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
arrives at a goal of the form <span class="inlinecode">(<span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">(<span class="id" type="var">tapp</span></span>
<span class="inlinecode"><span class="id" type="var">e1</span></span>
<span class="inlinecode"><span class="id" type="var">e1</span>)</span>
<span class="inlinecode">∈</span> <span class="inlinecode"><span
class="id" type="var">T</span>)</span>, it should consider <span
class="inlinecode"><span class="id" type="tactic">eapply</span></span>
<span class="inlinecode"><span class="id"
type="var">T\_App</span></span>, leaving an existential variable for the
middle type T~1~, and similar for <span class="inlinecode"><span
class="id" type="var">lcase</span></span>. That variable will then be
filled in during the search for type derivations for <span
class="inlinecode"><span class="id" type="var">e1</span></span> and
<span class="inlinecode"><span class="id" type="var">e2</span></span>.
We also include a hint to "try harder" when solving equality goals; this
is useful to automate uses of <span class="inlinecode"><span class="id"
type="var">T\_Var</span></span> (which includes an equality as a
precondition).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Extern</span> 2 (<span class="id"
type="var">has\_type</span> <span class="id" type="var">\_</span> (<span
class="id" type="var">tapp</span> <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span>) <span class="id"
type="var">\_</span>) ⇒\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_App</span>; <span class="id" type="tactic">auto</span>.\
 <span
class="comment">(\* You'll want to uncomment the following line once \
    you've defined the <span class="inlinecode"><span class="id"
type="var">T\_Lcase</span></span> constructor for the typing\
    relation: \*)</span>\
 <span class="comment">(\* \
 Hint Extern 2 (has\_type \_ (tlcase \_ \_ \_ \_ \_) \_) =\> \
   eapply T\_Lcase; auto.\
 \*)</span>\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Extern</span> 2 (<span class="id" type="var">\_</span> =
<span class="id" type="var">\_</span>) ⇒ <span class="id"
type="tactic">compute</span>; <span class="id"
type="tactic">reflexivity</span>.\
\

</div>

<div class="doc">

### Numbers {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Numtest</span>.\
\
 <span
class="comment">(\* if0 (pred (succ (pred (2 \* 0))) then 5 else 6 \*)</span>\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">test</span> :=\
   <span class="id" type="var">tif0</span>\
     (<span class="id" type="var">tpred</span>\
       (<span class="id" type="var">tsucc</span>\
         (<span class="id" type="var">tpred</span>\
           (<span class="id" type="var">tmult</span>\
             (<span class="id" type="var">tnat</span> 2)\
             (<span class="id" type="var">tnat</span> 0)))))\
     (<span class="id" type="var">tnat</span> 5)\
     (<span class="id" type="var">tnat</span> 6).\
\

</div>

<div class="doc">

Remove the comment braces once you've implemented enough of the
definitions that you think this should work.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* \
 Example typechecks :\
   (@empty ty) |- test ∈ TNat.\
 Proof.\
   unfold test.\
   <span
class="comment">(\* This typing derivation is quite deep, so we need to increase the\
      max search depth of <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> from the default 5 to 10. \*)</span>\
   auto 10. \
 Qed.\
\
 Example numtest\_reduces :\
   test ==\>\* tnat 5.\
 Proof.\
   unfold test. normalize.\
 Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Numtest</span>.\
\

</div>

<div class="doc">

### Products {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Prodtest</span>.\
\
 <span class="comment">(\* ((5,6),7).fst.snd \*)</span>\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">test</span> :=\
   <span class="id" type="var">tsnd</span>\
     (<span class="id" type="var">tfst</span>\
       (<span class="id" type="var">tpair</span>\
         (<span class="id" type="var">tpair</span>\
           (<span class="id" type="var">tnat</span> 5)\
           (<span class="id" type="var">tnat</span> 6))\
         (<span class="id" type="var">tnat</span> 7))).\
\
 <span class="comment">(\* \
 Example typechecks :\
   (@empty ty) |- test ∈ TNat.\
 Proof. unfold test. eauto 15. Qed.\
\
 Example reduces :\
   test ==\>\* tnat 6.\
 Proof. unfold test. normalize. Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Prodtest</span>.\
\

</div>

<div class="doc">

### <span class="inlinecode"><span class="id" type="keyword">let</span></span> {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">LetTest</span>.\
\
 <span class="comment">(\* let x = pred 6 in succ x \*)</span>\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">test</span> :=\
   <span class="id" type="var">tlet</span>\
     <span class="id" type="var">x</span>\
     (<span class="id" type="var">tpred</span> (<span class="id"
type="var">tnat</span> 6))\
     (<span class="id" type="var">tsucc</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>)).\
\
 <span class="comment">(\* \
 Example typechecks :\
   (@empty ty) |- test ∈ TNat.\
 Proof. unfold test. eauto 15. Qed.\
\
 Example reduces :\
   test ==\>\* tnat 6.\
 Proof. unfold test. normalize. Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">LetTest</span>.\
\

</div>

<div class="doc">

### Sums {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Sumtest1</span>.\
\
 <span class="comment">(\* case (inl Nat 5) of\
      inl x =\> x\
    | inr y =\> y \*)</span>\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">test</span> :=\
   <span class="id" type="var">tcase</span> (<span class="id"
type="var">tinl</span> <span class="id" type="var">TNat</span> (<span
class="id" type="var">tnat</span> 5))\
     <span class="id" type="var">x</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>)\
     <span class="id" type="var">y</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">y</span>).\
\
 <span class="comment">(\* \
 Example typechecks :\
   (@empty ty) |- test ∈ TNat.\
 Proof. unfold test. eauto 15. Qed.\
\
 Example reduces :\
   test ==\>\* (tnat 5).\
 Proof. unfold test. normalize. Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Sumtest1</span>.\
\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Sumtest2</span>.\
\
 <span class="comment">(\* let processSum =\
      \\x:Nat+Nat.\
         case x of\
           inl n =\> n\
           inr n =\> if0 n then 1 else 0 in\
    (processSum (inl Nat 5), processSum (inr Nat 5))    \*)</span>\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">test</span> :=\
   <span class="id" type="var">tlet</span>\
     <span class="id" type="var">processSum</span>\
     (<span class="id" type="var">tabs</span> <span class="id"
type="var">x</span> (<span class="id" type="var">TSum</span> <span
class="id" type="var">TNat</span> <span class="id"
type="var">TNat</span>)\
       (<span class="id" type="var">tcase</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>)\
          <span class="id" type="var">n</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">n</span>)\
          <span class="id" type="var">n</span> (<span class="id"
type="var">tif0</span> (<span class="id" type="var">tvar</span> <span
class="id" type="var">n</span>) (<span class="id" type="var">tnat</span>
1) (<span class="id" type="var">tnat</span> 0))))\
     (<span class="id" type="var">tpair</span>\
       (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">processSum</span>)
(<span class="id" type="var">tinl</span> <span class="id"
type="var">TNat</span> (<span class="id" type="var">tnat</span> 5)))\
       (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">processSum</span>)
(<span class="id" type="var">tinr</span> <span class="id"
type="var">TNat</span> (<span class="id" type="var">tnat</span> 5)))).\
\
 <span class="comment">(\* \
 Example typechecks :\
   (@empty ty) |- test ∈ (TProd TNat TNat).\
 Proof. unfold test. eauto 15. Qed.\
\
 Example reduces :\
   test ==\>\* (tpair (tnat 5) (tnat 0)).\
 Proof. unfold test. normalize. Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Sumtest2</span>.\
\

</div>

<div class="doc">

### Lists {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">ListTest</span>.\
\
 <span class="comment">(\* let l = cons 5 (cons 6 (nil Nat)) in\
    lcase l of\
      nil =\> 0\
    | x::y =\> x\*x \*)</span>\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">test</span> :=\
   <span class="id" type="var">tlet</span> <span class="id"
type="var">l</span>\
     (<span class="id" type="var">tcons</span> (<span class="id"
type="var">tnat</span> 5) (<span class="id" type="var">tcons</span>
(<span class="id" type="var">tnat</span> 6) (<span class="id"
type="var">tnil</span> <span class="id" type="var">TNat</span>)))\
     (<span class="id" type="var">tlcase</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">l</span>)\
        (<span class="id" type="var">tnat</span> 0)\
        <span class="id" type="var">x</span> <span class="id"
type="var">y</span> (<span class="id" type="var">tmult</span> (<span
class="id" type="var">tvar</span> <span class="id" type="var">x</span>)
(<span class="id" type="var">tvar</span> <span class="id"
type="var">x</span>))).\
\
 <span class="comment">(\* \
 Example typechecks :\
   (@empty ty) |- test ∈ TNat.\
 Proof. unfold test. eauto 20. Qed.\
\
 Example reduces :\
   test ==\>\* (tnat 25).\
 Proof. unfold test. normalize. Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">ListTest</span>.\
\

</div>

<div class="doc">

### <span class="inlinecode"><span class="id" type="var">fix</span></span> {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">FixTest1</span>.\
\
 <span class="comment">(\* fact := fix\
              (\\f:nat-\>nat.\
                 \\a:nat. \
                    if a=0 then 1 else a \* (f (pred a))) \*)</span>\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">fact</span> :=\
   <span class="id" type="var">tfix</span>\
     (<span class="id" type="var">tabs</span> <span class="id"
type="var">f</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">TNat</span> <span class="id"
type="var">TNat</span>)\
       (<span class="id" type="var">tabs</span> <span class="id"
type="var">a</span> <span class="id" type="var">TNat</span>\
         (<span class="id" type="var">tif0</span>\
            (<span class="id" type="var">tvar</span> <span class="id"
type="var">a</span>)\
            (<span class="id" type="var">tnat</span> 1)\
            (<span class="id" type="var">tmult</span>\
               (<span class="id" type="var">tvar</span> <span class="id"
type="var">a</span>)\
               (<span class="id" type="var">tapp</span> (<span
class="id" type="var">tvar</span> <span class="id" type="var">f</span>)
(<span class="id" type="var">tpred</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">a</span>))))))).\
\

</div>

<div class="doc">

(Warning: you may be able to typecheck <span class="inlinecode"><span
class="id" type="var">fact</span></span> but still have some rules
wrong!)

</div>

<div class="code code-tight">

\
 <span class="comment">(\* \
 Example fact\_typechecks :\
   (@empty ty) |- fact ∈ (TArrow TNat TNat).\
 Proof. unfold fact. auto 10. \
 Qed.\
 \*)</span>\
\
 <span class="comment">(\* \
 Example fact\_example: \
   (tapp fact (tnat 4)) ==\>\* (tnat 24).\
 Proof. unfold fact. normalize. Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">FixTest1</span>.\
\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">FixTest2</span>.\
\
 <span class="comment">(\* map :=\
      \\g:nat-\>nat.\
        fix\
          (\\f:<span class="inlinecode"><span class="id"
type="var">nat</span></span>-\><span class="inlinecode"><span class="id"
type="var">nat</span></span>.\
             \\l:<span class="inlinecode"><span class="id"
type="var">nat</span></span>. \
                case l of\
                | <span class="inlinecode"></span> -\> <span
class="inlinecode"></span>\
                | x::l -\> (g x)::(f l)) \*)</span>\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">map</span> :=\
   <span class="id" type="var">tabs</span> <span class="id"
type="var">g</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">TNat</span> <span class="id"
type="var">TNat</span>)\
     (<span class="id" type="var">tfix</span>\
       (<span class="id" type="var">tabs</span> <span class="id"
type="var">f</span> (<span class="id" type="var">TArrow</span> (<span
class="id" type="var">TList</span> <span class="id"
type="var">TNat</span>) (<span class="id" type="var">TList</span> <span
class="id" type="var">TNat</span>))\
         (<span class="id" type="var">tabs</span> <span class="id"
type="var">l</span> (<span class="id" type="var">TList</span> <span
class="id" type="var">TNat</span>)\
           (<span class="id" type="var">tlcase</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">l</span>)\
             (<span class="id" type="var">tnil</span> <span class="id"
type="var">TNat</span>)\
             <span class="id" type="var">a</span> <span class="id"
type="var">l</span> (<span class="id" type="var">tcons</span> (<span
class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">g</span>) (<span
class="id" type="var">tvar</span> <span class="id"
type="var">a</span>))\
                          (<span class="id" type="var">tapp</span>
(<span class="id" type="var">tvar</span> <span class="id"
type="var">f</span>) (<span class="id" type="var">tvar</span> <span
class="id" type="var">l</span>))))))).\
\
 <span class="comment">(\* \
 <span class="comment">(\* Make sure you've uncommented the last <span
class="inlinecode"><span class="id" type="keyword">Hint</span></span>
<span class="inlinecode"><span class="id"
type="keyword">Extern</span></span> above... \*)</span>\
 Example map\_typechecks :\
   empty |- map ∈ \
     (TArrow (TArrow TNat TNat)\
       (TArrow (TList TNat) \
         (TList TNat))).\
 Proof. unfold map. auto 10. Qed.\
\
 Example map\_example :\
   tapp (tapp map (tabs a TNat (tsucc (tvar a))))\
          (tcons (tnat 1) (tcons (tnat 2) (tnil TNat)))\
   ==\>\* (tcons (tnat 2) (tcons (tnat 3) (tnil TNat))).\
 Proof. unfold map. normalize. Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">FixTest2</span>.\
\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">FixTest3</span>.\
\
 <span class="comment">(\* equal = \
       fix \
         (\\eq:Nat-\>Nat-\>Bool.\
            \\m:Nat. \\n:Nat.\
              if0 m then (if0 n then 1 else 0) \
              else if0 n then 0\
              else eq (pred m) (pred n))   \*)</span>\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">equal</span> :=\
   <span class="id" type="var">tfix</span>\
     (<span class="id" type="var">tabs</span> <span class="id"
type="var">eq</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">TNat</span> (<span class="id"
type="var">TArrow</span> <span class="id" type="var">TNat</span> <span
class="id" type="var">TNat</span>))\
       (<span class="id" type="var">tabs</span> <span class="id"
type="var">m</span> <span class="id" type="var">TNat</span>\
         (<span class="id" type="var">tabs</span> <span class="id"
type="var">n</span> <span class="id" type="var">TNat</span>\
           (<span class="id" type="var">tif0</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">m</span>)\
             (<span class="id" type="var">tif0</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">n</span>) (<span
class="id" type="var">tnat</span> 1) (<span class="id"
type="var">tnat</span> 0))\
             (<span class="id" type="var">tif0</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">n</span>)\
               (<span class="id" type="var">tnat</span> 0)\
               (<span class="id" type="var">tapp</span> (<span
class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">eq</span>)\
                               (<span class="id" type="var">tpred</span>
(<span class="id" type="var">tvar</span> <span class="id"
type="var">m</span>)))\
                       (<span class="id" type="var">tpred</span> (<span
class="id" type="var">tvar</span> <span class="id"
type="var">n</span>)))))))).\
\
 <span class="comment">(\* \
 Example equal\_typechecks :\
   (@empty ty) |- equal ∈ (TArrow TNat (TArrow TNat TNat)).\
 Proof. unfold equal. auto 10. \
 Qed.\
 \*)</span>\
\
 <span class="comment">(\* \
 Example equal\_example1: \
   (tapp (tapp equal (tnat 4)) (tnat 4)) ==\>\* (tnat 1).\
 Proof. unfold equal. normalize. Qed.\
 \*)</span>\
\
 <span class="comment">(\* \
 Example equal\_example2: \
   (tapp (tapp equal (tnat 4)) (tnat 5)) ==\>\* (tnat 0).\
 Proof. unfold equal. normalize. Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">FixTest3</span>.\
\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">FixTest4</span>.\
\
 <span class="comment">(\* let evenodd = \
          fix \
            (\\eo: (Nat-\>Nat \* Nat-\>Nat).\
               let e = \\n:Nat. if0 n then 1 else eo.snd (pred n) in\
               let o = \\n:Nat. if0 n then 0 else eo.fst (pred n) in\
               (e,o)) in\
     let even = evenodd.fst in\
     let odd  = evenodd.snd in\
     (even 3, even 4)\
 \*)</span>\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">eotest</span> :=\
   <span class="id" type="var">tlet</span> <span class="id"
type="var">evenodd</span>\
     (<span class="id" type="var">tfix</span>\
       (<span class="id" type="var">tabs</span> <span class="id"
type="var">eo</span> (<span class="id" type="var">TProd</span> (<span
class="id" type="var">TArrow</span> <span class="id"
type="var">TNat</span> <span class="id" type="var">TNat</span>) (<span
class="id" type="var">TArrow</span> <span class="id"
type="var">TNat</span> <span class="id" type="var">TNat</span>))\
         (<span class="id" type="var">tpair</span>\
           (<span class="id" type="var">tabs</span> <span class="id"
type="var">n</span> <span class="id" type="var">TNat</span>\
             (<span class="id" type="var">tif0</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">n</span>)\
               (<span class="id" type="var">tnat</span> 1)\
               (<span class="id" type="var">tapp</span> (<span
class="id" type="var">tsnd</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">eo</span>)) (<span
class="id" type="var">tpred</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">n</span>)))))\
           (<span class="id" type="var">tabs</span> <span class="id"
type="var">n</span> <span class="id" type="var">TNat</span>\
             (<span class="id" type="var">tif0</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">n</span>)\
               (<span class="id" type="var">tnat</span> 0)\
               (<span class="id" type="var">tapp</span> (<span
class="id" type="var">tfst</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">eo</span>)) (<span
class="id" type="var">tpred</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">n</span>))))))))\
   (<span class="id" type="var">tlet</span> <span class="id"
type="var">even</span> (<span class="id" type="var">tfst</span> (<span
class="id" type="var">tvar</span> <span class="id"
type="var">evenodd</span>))\
   (<span class="id" type="var">tlet</span> <span class="id"
type="var">odd</span> (<span class="id" type="var">tsnd</span> (<span
class="id" type="var">tvar</span> <span class="id"
type="var">evenodd</span>))\
   (<span class="id" type="var">tpair</span>\
     (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">even</span>) (<span
class="id" type="var">tnat</span> 3))\
     (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">even</span>) (<span
class="id" type="var">tnat</span> 4))))).\
\
 <span class="comment">(\* \
 Example eotest\_typechecks :\
   (@empty ty) |- eotest ∈ (TProd TNat TNat).\
 Proof. unfold eotest. eauto 30. \
 Qed.\
 \*)</span>\
\
 <span class="comment">(\* \
 Example eotest\_example1: \
   eotest ==\>\* (tpair (tnat 0) (tnat 1)).\
 Proof. unfold eotest. normalize. Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">FixTest4</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Examples</span>.\
\

</div>

<div class="doc">

Properties of Typing {.section}
--------------------

<div class="paragraph">

</div>

The proofs of progress and preservation for this system are essentially
the same (though of course somewhat longer) as for the pure simply typed
lambda-calculus.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Progress {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="tactic">progress</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">T</span>,\
      <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">∨</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>, <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span
class="comment">(\* Theorem: Suppose empty |- t : T.  Then either\
        1. t is a value, or\
        2. t ==\> t' for some t'.\
      Proof: By induction on the given typing derivation. \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
class="id" type="var">Ht</span>.\
   <span class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id"
type="var">HeqGamma</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Ht</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">HeqGamma</span>;
<span class="id" type="tactic">subst</span>.\
   <span class="id" type="var">Case</span> "T\_Var".\
     <span
class="comment">(\* The final rule in the given typing derivation cannot be <span
class="inlinecode"><span class="id" type="var">T\_Var</span></span>,\
        since it can never be the case that <span
class="inlinecode"><span class="id" type="var">empty</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T</span></span> (since the\
        context is empty). \*)</span>\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="comment">(\* If the <span class="inlinecode"><span
class="id"
type="var">T\_Abs</span></span> rule was the last used, then <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">tabs</span></span> <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode"><span class="id"
type="var">T~11~</span></span> <span class="inlinecode"><span class="id"
type="var">t~12~</span></span>,\
        which is a value. \*)</span>\
     <span class="id" type="var">left</span>...\
   <span class="id" type="var">Case</span> "T\_App".\
     <span
class="comment">(\* If the last rule applied was T\_App, then <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> <span class="inlinecode"><span class="id"
type="var">t~2~</span></span>, and we know \
        from the form of the rule that\
          <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~1~</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">T~2~</span></span>\
          <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t~2~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~1~</span></span>\

       By the induction hypothesis, each of t~1~ and t~2~ either is a value \
        or can take a step. \*)</span>\
     <span class="id" type="var">right</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span>; <span class="id" type="tactic">subst</span>...\
       <span class="id" type="var">SSCase</span> "t~2~ is a value".\
       <span class="comment">(\* If both <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> and <span
class="inlinecode"><span class="id"
type="var">t~2~</span></span> are values, then we know that \
          <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">tabs</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">T~11~</span></span> <span
class="inlinecode"><span class="id"
type="var">t~12~</span></span>, since abstractions are the only values\
          that can have an arrow type.  But \
          <span class="inlinecode">(<span class="id"
type="var">tabs</span></span> <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode"><span class="id"
type="var">T~11~</span></span> <span class="inlinecode"><span class="id"
type="var">t~12~</span>)</span> <span class="inlinecode"><span
class="id" type="var">t~2~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">t~2~</span>]<span class="id"
type="var">t~12~</span></span> by <span class="inlinecode"><span
class="id" type="var">ST\_AppAbs</span></span>. \*)</span>\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">H</span>; <span class="id"
type="tactic">subst</span>; <span class="id" type="tactic">try</span>
(<span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>).\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~12~</span>)...\
       <span class="id" type="var">SSCase</span> "t~2~ steps".\
         <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> is a value and <span
class="inlinecode"><span class="id" type="var">t~2~</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span>
<span class="inlinecode"><span class="id"
type="var">t~2~'</span></span>, then <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> <span class="inlinecode"><span
class="id" type="var">t~2~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> <span
class="inlinecode"><span class="id" type="var">t~2~'</span></span> \
            by <span class="inlinecode"><span class="id"
type="var">ST\_App2</span></span>. \*)</span>\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">H0</span> <span class="id"
type="keyword">as</span> [<span class="id" type="var">t~2~'</span> <span
class="id" type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~'</span>)...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="comment">(\* Finally, If <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span>
<span class="inlinecode"><span class="id"
type="var">t~1~'</span></span>, then <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> <span class="inlinecode"><span
class="id" type="var">t~2~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t~1~'</span></span> <span
class="inlinecode"><span class="id"
type="var">t~2~</span></span> by <span class="inlinecode"><span
class="id" type="var">ST\_App1</span></span>. \*)</span>\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)...\
   <span class="id" type="var">Case</span> "T\_Nat".\
     <span class="id" type="var">left</span>...\
   <span class="id" type="var">Case</span> "T\_Succ".\
     <span class="id" type="var">right</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt</span>...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tnat</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n1</span>))...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tsucc</span> <span class="id" type="var">t~1~'</span>)...\
   <span class="id" type="var">Case</span> "T\_Pred".\
     <span class="id" type="var">right</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt</span>...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tnat</span> (<span class="id" type="var">pred</span> <span
class="id" type="var">n1</span>))...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tpred</span> <span class="id" type="var">t~1~'</span>)...\
   <span class="id" type="var">Case</span> "T\_Mult".\
     <span class="id" type="var">right</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span>...\
       <span class="id" type="var">SSCase</span> "t~2~ is a value".\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">H</span>; <span class="id"
type="tactic">subst</span>; <span class="id" type="tactic">try</span>
<span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">H0</span>; <span class="id"
type="tactic">subst</span>; <span class="id" type="tactic">try</span>
<span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tnat</span> (<span class="id" type="var">mult</span> <span
class="id" type="var">n1</span> <span class="id"
type="var">n0</span>))...\
       <span class="id" type="var">SSCase</span> "t~2~ steps".\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">H0</span> <span class="id"
type="keyword">as</span> [<span class="id" type="var">t~2~'</span> <span
class="id" type="var">Hstp</span>].\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tmult</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~'</span>)...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tmult</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)...\
   <span class="id" type="var">Case</span> "T\_If0".\
     <span class="id" type="var">right</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">n1</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">n1'</span>].\
       <span class="id" type="var">SSCase</span> "n1=0".\
         <span style="font-family: arial;">∃</span><span class="id"
type="var">t~2~</span>...\
       <span class="id" type="var">SSCase</span> "n1≠0".\
         <span style="font-family: arial;">∃</span><span class="id"
type="var">t~3~</span>...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">H0</span>].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tif0</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>)...\
   <span class="id" type="var">Case</span> "T\_Pair".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span>...\
       <span class="id" type="var">SSCase</span> "t~2~ steps".\
         <span class="id" type="var">right</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H0</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">t~2~'</span> <span class="id" type="var">Hstp</span>].\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tpair</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~'</span>)...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="var">right</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">t~1~'</span> <span class="id" type="var">Hstp</span>].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tpair</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)...\
   <span class="id" type="var">Case</span> "T\_Fst".\
     <span class="id" type="var">right</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt</span>...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">v~1~</span>...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tfst</span> <span class="id" type="var">t~1~'</span>)...\
   <span class="id" type="var">Case</span> "T\_Snd".\
     <span class="id" type="var">right</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt</span>...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">v~2~</span>...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tsnd</span> <span class="id" type="var">t~1~'</span>)...\
   <span class="id" type="var">Case</span> "T\_Unit".\
     <span class="id" type="var">left</span>...\
 <span class="comment">(\* let \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
   <span class="id" type="var">Case</span> "T\_Inl".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt</span>...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="var">right</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">t~1~'</span> <span class="id" type="var">Hstp</span>]...\
       <span class="comment">(\* exists (tinl \_ t~1~')... \*)</span>\
   <span class="id" type="var">Case</span> "T\_Inr".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt</span>...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="var">right</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">t~1~'</span> <span class="id" type="var">Hstp</span>]...\
       <span class="comment">(\* exists (tinr \_ t~1~')... \*)</span>\
   <span class="id" type="var">Case</span> "T\_Case".\
     <span class="id" type="var">right</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>...\
     <span class="id" type="var">SCase</span> "t0 is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
       <span class="id" type="var">SSCase</span> "t0 is inl".\
         <span style="font-family: arial;">∃</span>([<span class="id"
type="var">x1</span>:=<span class="id" type="var">v</span>]<span
class="id" type="var">t~1~</span>)...\
       <span class="id" type="var">SSCase</span> "t0 is inr".\
         <span style="font-family: arial;">∃</span>([<span class="id"
type="var">x2</span>:=<span class="id" type="var">v</span>]<span
class="id" type="var">t~2~</span>)...\
     <span class="id" type="var">SCase</span> "t0 steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t0'</span> <span class="id"
type="var">Hstp</span>].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tcase</span> <span class="id" type="var">t0'</span> <span
class="id" type="var">x1</span> <span class="id" type="var">t~1~</span>
<span class="id" type="var">x2</span> <span class="id"
type="var">t~2~</span>)...\
   <span class="id" type="var">Case</span> "T\_Nil".\
     <span class="id" type="var">left</span>...\
   <span class="id" type="var">Case</span> "T\_Cons".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>...\
     <span class="id" type="var">SCase</span> "head is a value".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span>...\
       <span class="id" type="var">SSCase</span> "tail steps".\
         <span class="id" type="var">right</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H0</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">t~2~'</span> <span class="id" type="var">Hstp</span>].\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tcons</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~'</span>)...\
     <span class="id" type="var">SCase</span> "head steps".\
       <span class="id" type="var">right</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">t~1~'</span> <span class="id" type="var">Hstp</span>].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tcons</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)...\
   <span class="id" type="var">Case</span> "T\_Lcase".\
     <span class="id" type="var">right</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
       <span class="id" type="var">SSCase</span> "t~1~=tnil".\
         <span style="font-family: arial;">∃</span><span class="id"
type="var">t~2~</span>...\
       <span class="id" type="var">SSCase</span> "t~1~=tcons v~1~ vl".\
         <span style="font-family: arial;">∃</span>([<span class="id"
type="var">x2</span>:=<span class="id" type="var">vl</span>]([<span
class="id" type="var">x1</span>:=<span class="id"
type="var">v~1~</span>]<span class="id" type="var">t~3~</span>))...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tlcase</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">x1</span>
<span class="id" type="var">x2</span> <span class="id"
type="var">t~3~</span>)...\
 <span class="comment">(\* fix \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Context Invariance {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">appears\_free\_in</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">afi\_var</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tvar</span>
<span class="id" type="var">x</span>)\
   | <span class="id" type="var">afi\_app1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">appears\_free\_in</span> <span class="id" type="var">x</span>
(<span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_app2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">appears\_free\_in</span> <span class="id" type="var">x</span>
(<span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_abs</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">y</span> <span class="id"
type="var">T~11~</span> <span class="id" type="var">t~12~</span>,\
         <span class="id" type="var">y</span> ≠ <span class="id"
type="var">x</span> <span style="font-family: arial;">→</span>\
         <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~12~</span>
<span style="font-family: arial;">→</span>\
         <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tabs</span>
<span class="id" type="var">y</span> <span class="id"
type="var">T~11~</span> <span class="id" type="var">t~12~</span>)\
   <span class="comment">(\* nats \*)</span>\
   | <span class="id" type="var">afi\_succ</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t</span>,\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tsucc</span>
<span class="id" type="var">t</span>)\
   | <span class="id" type="var">afi\_pred</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t</span>,\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tpred</span>
<span class="id" type="var">t</span>)\
   | <span class="id" type="var">afi\_mult1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tmult</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_mult2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tmult</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_if01</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif0</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>)\
   | <span class="id" type="var">afi\_if02</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif0</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>)\
   | <span class="id" type="var">afi\_if03</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~3~</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif0</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>)\
   <span class="comment">(\* pairs \*)</span>\
   | <span class="id" type="var">afi\_pair1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tpair</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_pair2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tpair</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_fst</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tfst</span>
<span class="id" type="var">t</span>)\
   | <span class="id" type="var">afi\_snd</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tsnd</span>
<span class="id" type="var">t</span>)\
   <span class="comment">(\* let \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
   <span class="comment">(\* sums \*)</span>\
   | <span class="id" type="var">afi\_inl</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t</span> <span class="id"
type="var">T</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tinl</span>
<span class="id" type="var">T</span> <span class="id"
type="var">t</span>)\
   | <span class="id" type="var">afi\_inr</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t</span> <span class="id"
type="var">T</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tinr</span>
<span class="id" type="var">T</span> <span class="id"
type="var">t</span>)\
   | <span class="id" type="var">afi\_case0</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t0</span> <span class="id"
type="var">x1</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">x2</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t0</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tcase</span>
<span class="id" type="var">t0</span> <span class="id"
type="var">x1</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">x2</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_case1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t0</span> <span class="id"
type="var">x1</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">x2</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">x1</span> ≠ <span class="id"
type="var">x</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tcase</span>
<span class="id" type="var">t0</span> <span class="id"
type="var">x1</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">x2</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_case2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t0</span> <span class="id"
type="var">x1</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">x2</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">x2</span> ≠ <span class="id"
type="var">x</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tcase</span>
<span class="id" type="var">t0</span> <span class="id"
type="var">x1</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">x2</span> <span class="id"
type="var">t~2~</span>)\
   <span class="comment">(\* lists \*)</span>\
   | <span class="id" type="var">afi\_cons1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tcons</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_cons2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tcons</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_lcase1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">y1</span> <span
class="id" type="var">y2</span> <span class="id"
type="var">t~3~</span>,\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id"
type="var">tlcase</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">y1</span>
<span class="id" type="var">y2</span> <span class="id"
type="var">t~3~</span>)\
   | <span class="id" type="var">afi\_lcase2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">y1</span> <span
class="id" type="var">y2</span> <span class="id"
type="var">t~3~</span>,\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id"
type="var">tlcase</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">y1</span>
<span class="id" type="var">y2</span> <span class="id"
type="var">t~3~</span>)\
   | <span class="id" type="var">afi\_lcase3</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">y1</span> <span
class="id" type="var">y2</span> <span class="id"
type="var">t~3~</span>,\
      <span class="id" type="var">y1</span> ≠ <span class="id"
type="var">x</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">y2</span> ≠ <span class="id"
type="var">x</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~3~</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id"
type="var">tlcase</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">y1</span>
<span class="id" type="var">y2</span> <span class="id"
type="var">t~3~</span>)\
   <span class="comment">(\* fix \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
   .\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">appears\_free\_in</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">context\_invariance</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: serif; font-size:85%;">Γ'</span> <span class="id"
type="var">t</span> <span class="id" type="var">S</span>,\
      <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">S</span> <span
style="font-family: arial;">→</span>\
      (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span class="id"
type="var">appears\_free\_in</span> <span class="id" type="var">x</span>
<span class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> = <span
style="font-family: serif; font-size:85%;">Γ'</span> <span class="id"
type="var">x</span>) <span style="font-family: arial;">→</span>\
      <span style="font-family: serif; font-size:85%;">Γ'</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">S</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ'</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ'</span> <span class="id"
type="var">Heqv</span>...\
   <span class="id" type="var">Case</span> "T\_Var".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Var</span>... <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">Heqv</span>...\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>... <span class="id" type="tactic">apply</span>
<span class="id" type="var">IHhas\_type</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">y</span> <span
class="id" type="var">Hafi</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>)...\
   <span class="id" type="var">Case</span> "T\_Mult".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Mult</span>...\
   <span class="id" type="var">Case</span> "T\_If0".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_If0</span>...\
   <span class="id" type="var">Case</span> "T\_Pair".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Pair</span>...\
 <span class="comment">(\* let \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
   <span class="id" type="var">Case</span> "T\_Case".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Case</span>...\
      <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHhas\_type2</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">y</span> <span
class="id" type="var">Hafi</span>.\
        <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
        <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x1</span>
<span class="id" type="var">y</span>)...\
      <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHhas\_type3</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">y</span> <span
class="id" type="var">Hafi</span>.\
        <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
        <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x2</span>
<span class="id" type="var">y</span>)...\
   <span class="id" type="var">Case</span> "T\_Cons".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Cons</span>...\
   <span class="id" type="var">Case</span> "T\_Lcase".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Lcase</span>... <span class="id"
type="tactic">apply</span> <span class="id"
type="var">IHhas\_type3</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">y</span> <span
class="id" type="var">Hafi</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x1</span>
<span class="id" type="var">y</span>)...\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x2</span>
<span class="id" type="var">y</span>)...\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">free\_in\_context</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t</span> <span class="id"
type="var">T</span> <span
style="font-family: serif; font-size:85%;">Γ</span>,\
    <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
    <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
    <span style="font-family: arial;">∃</span><span class="id"
type="var">T'</span>, <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> = <span class="id" type="var">Some</span> <span
class="id" type="var">T'</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">Hafi</span> <span class="id" type="var">Htyp</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Htyp</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hafi</span>;
<span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHtyp</span> <span class="id" type="keyword">as</span>
[<span class="id" type="var">T'</span> <span class="id"
type="var">Hctx</span>]... <span
style="font-family: arial;">∃</span><span class="id"
type="var">T'</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hctx</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">Hctx</span>...\
 <span class="comment">(\* let \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
   <span class="id" type="var">Case</span> "T\_Case".\
     <span class="id" type="var">SCase</span> "left".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHtyp2</span> <span class="id" type="keyword">as</span>
[<span class="id" type="var">T'</span> <span class="id"
type="var">Hctx</span>]... <span
style="font-family: arial;">∃</span><span class="id"
type="var">T'</span>.\
       <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hctx</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">Hctx</span>...\
     <span class="id" type="var">SCase</span> "right".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHtyp3</span> <span class="id" type="keyword">as</span>
[<span class="id" type="var">T'</span> <span class="id"
type="var">Hctx</span>]... <span
style="font-family: arial;">∃</span><span class="id"
type="var">T'</span>.\
       <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hctx</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">Hctx</span>...\
   <span class="id" type="var">Case</span> "T\_Lcase".\
     <span class="id" type="tactic">clear</span> <span class="id"
type="var">Htyp1</span> <span class="id" type="var">IHHtyp1</span> <span
class="id" type="var">Htyp2</span> <span class="id"
type="var">IHHtyp2</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHtyp3</span> <span class="id" type="keyword">as</span>
[<span class="id" type="var">T'</span> <span class="id"
type="var">Hctx</span>]... <span
style="font-family: arial;">∃</span><span class="id"
type="var">T'</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hctx</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">Hctx</span>... <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">neq\_id</span>
<span class="id" type="keyword">in</span> <span class="id"
type="var">Hctx</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Substitution {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">substitution\_preserves\_typing</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span> <span
class="id" type="var">v</span> <span class="id" type="var">t</span>
<span class="id" type="var">S</span>,\
      (<span class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span>) <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">S</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">v</span> ∈ <span class="id" type="var">U</span> <span
style="font-family: arial;">→</span>\
      <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> ([<span class="id"
type="var">x</span>:=<span class="id" type="var">v</span>]<span
class="id" type="var">t</span>) ∈ <span class="id" type="var">S</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span
class="comment">(\* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then \
      Gamma |- <span class="inlinecode"><span class="id"
type="var">x</span>:=<span class="id"
type="var">v</span></span>t : S. \*)</span>\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span> <span
class="id" type="var">v</span> <span class="id" type="var">t</span>
<span class="id" type="var">S</span> <span class="id"
type="var">Htypt</span> <span class="id" type="var">Htypv</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">S</span>.\
   <span
class="comment">(\* Proof: By induction on the term t.  Most cases follow directly\
      from the IH, with the exception of tvar and tabs.\
      The former aren't automatic because we must reason about how the\
      variables interact. \*)</span>\
   <span class="id" type="var">t\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">t</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">S</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">Htypt</span>; <span class="id" type="tactic">simpl</span>;
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">Htypt</span>; <span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "tvar".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rename</span> <span class="id" type="var">i</span> <span
class="id" type="var">into</span> <span class="id" type="var">y</span>.\
     <span class="comment">(\* If t = y, we know that\
          <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">v</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">U</span></span> and\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">S</span></span>\
        and, by inversion, <span class="inlinecode"><span class="id"
type="var">extend</span></span> <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">U</span></span> <span
class="inlinecode"><span class="id" type="var">y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">Some</span></span> <span class="inlinecode"><span class="id"
type="var">S</span></span>.  We want to\
        show that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">y</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">S</span></span>.\
\
        There are two cases to consider: either <span
class="inlinecode"><span class="id" type="var">x</span>=<span class="id"
type="var">y</span></span> or <span class="inlinecode"><span class="id"
type="var">x</span>≠<span class="id"
type="var">y</span></span>. \*)</span>\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>).\
     <span class="id" type="var">SCase</span> "x=y".\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">y</span></span>, then we know that <span
class="inlinecode"><span class="id" type="var">U</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">S</span></span>, and that <span class="inlinecode">[<span
class="id" type="var">x</span>:=<span class="id"
type="var">v</span>]<span class="id" type="var">y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">v</span></span>.\
        So what we really must show is that if <span
class="inlinecode"><span class="id" type="var">empty</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">v</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">U</span></span> then\
        <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">v</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id"
type="var">U</span></span>.  We have already proven a more general version\
        of this theorem, called context invariance. \*)</span>\
       <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H1</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">eq\_id</span>
<span class="id" type="keyword">in</span> <span class="id"
type="var">H1</span>.\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H1</span>; <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H1</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>...\
       <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">Hcontra</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">free\_in\_context</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">S</span> <span class="id" type="var">empty</span>
<span class="id" type="var">Hcontra</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">T'</span> <span
class="id" type="var">HT'</span>]...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT'</span>.\
     <span class="id" type="var">SCase</span> "x≠y".\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">≠</span>
<span class="inlinecode"><span class="id"
type="var">y</span></span>, then <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span class="id" type="var">y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">Some</span></span> <span class="inlinecode"><span class="id"
type="var">S</span></span> and the substitution has no\
        effect.  We can show that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">S</span></span> by <span class="inlinecode"><span
class="id" type="var">T\_Var</span></span>. \*)</span>\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Var</span>... <span class="id" type="tactic">unfold</span>
<span class="id" type="var">extend</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H1</span>. <span
class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H1</span>...\
   <span class="id" type="var">Case</span> "tabs".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y</span>. <span class="id"
type="tactic">rename</span> <span class="id" type="var">t</span> <span
class="id" type="var">into</span> <span class="id"
type="var">T~11~</span>.\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">tabs</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span>
<span class="inlinecode"><span class="id" type="var">T~11~</span></span>
<span class="inlinecode"><span class="id"
type="var">t0</span></span>, then we know that\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">tabs</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span>
<span class="inlinecode"><span class="id" type="var">T~11~</span></span>
<span class="inlinecode"><span class="id" type="var">t0</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T~11~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T~12~</span></span>\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span>,<span
class="id" type="var">y</span>:<span class="id"
type="var">T~11~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~12~</span></span>\
          <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">v</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">U</span></span>\
        As our IH, we know that forall S Gamma, \
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t0</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">S</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t0</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">S</span></span>.\
     \
        We can calculate that \
          <span class="inlinecode"><span class="id"
type="var">x</span>:=<span class="id"
type="var">v</span></span>t = tabs y T~11~ (if beq\_id x y then t0 else <span
class="inlinecode"><span class="id" type="var">x</span>:=<span
class="id" type="var">v</span></span>t0)\
        And we must show that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">T~11~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T~12~</span></span>.  We know\
        we will do so using <span class="inlinecode"><span class="id"
type="var">T\_Abs</span></span>, so it remains to be shown that:\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span></span>
<span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="keyword">if</span></span>
<span class="inlinecode"><span class="id"
type="var">beq\_id</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="var">y</span></span> <span class="inlinecode"><span
class="id" type="keyword">then</span></span> <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode"><span class="id" type="keyword">else</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t0</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">T~12~</span></span>\
        We consider two cases: <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">y</span></span> and <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode">≠</span> <span class="inlinecode"><span class="id"
type="var">y</span></span>.\
     \*)</span>\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>...\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>).\
     <span class="id" type="var">SCase</span> "x=y".\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">y</span></span>, then the substitution has no effect.  Context\
        invariance shows that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">U</span>,<span
class="id" type="var">y</span>:<span class="id"
type="var">T~11~</span></span> and <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span></span> are\
        equivalent.  Since the former context shows that <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~12~</span></span>, so\
        does the latter. \*)</span>\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>...\
       <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">Hafi</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">y</span> <span
class="id" type="var">x</span>)...\
     <span class="id" type="var">SCase</span> "x≠y".\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">≠</span>
<span class="inlinecode"><span class="id"
type="var">y</span></span>, then the IH and context invariance allow us to show that\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span>,<span
class="id" type="var">y</span>:<span class="id"
type="var">T~11~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~12~</span></span>       =\>\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span>,<span
class="id" type="var">x</span>:<span class="id"
type="var">U</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~12~</span></span>       =\>\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span></span>
<span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t0</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id"
type="var">T~12~</span></span> \*)</span>\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHt</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">context\_invariance</span>...\
       <span class="id" type="tactic">intros</span> <span class="id"
type="var">z</span> <span class="id" type="var">Hafi</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span>)...\
       <span class="id" type="tactic">subst</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>...\
 <span class="comment">(\* let \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
   <span class="id" type="var">Case</span> "tcase".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">x1</span>. <span class="id"
type="tactic">rename</span> <span class="id" type="var">i0</span> <span
class="id" type="var">into</span> <span class="id"
type="var">x2</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Case</span>...\
       <span class="id" type="var">SCase</span> "left arm".\
        <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x1</span>).\
        <span class="id" type="var">SSCase</span> "x = x1".\
         <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>...\
         <span class="id" type="tactic">subst</span>.\
         <span class="id" type="tactic">intros</span> <span class="id"
type="var">z</span> <span class="id" type="var">Hafi</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
         <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x1</span> <span class="id" type="var">z</span>)...\
        <span class="id" type="var">SSCase</span> "x ≠ x1".\
          <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHt2</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">context\_invariance</span>...\
          <span class="id" type="tactic">intros</span> <span class="id"
type="var">z</span> <span class="id" type="var">Hafi</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
          <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x1</span> <span class="id" type="var">z</span>)...\
            <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>...\
       <span class="id" type="var">SCase</span> "right arm".\
        <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x2</span>).\
        <span class="id" type="var">SSCase</span> "x = x2".\
         <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>...\
         <span class="id" type="tactic">subst</span>.\
         <span class="id" type="tactic">intros</span> <span class="id"
type="var">z</span> <span class="id" type="var">Hafi</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
         <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x2</span> <span class="id" type="var">z</span>)...\
        <span class="id" type="var">SSCase</span> "x ≠ x2".\
          <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHt3</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">context\_invariance</span>...\
          <span class="id" type="tactic">intros</span> <span class="id"
type="var">z</span> <span class="id" type="var">Hafi</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
          <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x2</span> <span class="id" type="var">z</span>)...\
            <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>...\
   <span class="id" type="var">Case</span> "tlcase".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y1</span>. <span class="id"
type="tactic">rename</span> <span class="id" type="var">i0</span> <span
class="id" type="var">into</span> <span class="id"
type="var">y2</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Lcase</span>...\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y1</span>).\
     <span class="id" type="var">SCase</span> "x=y1".\
       <span class="id" type="tactic">simpl</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>...\
       <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">intros</span> <span class="id"
type="var">z</span> <span class="id" type="var">Hafi</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">y1</span>
<span class="id" type="var">z</span>)...\
     <span class="id" type="var">SCase</span> "x≠y1".\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y2</span>).\
       <span class="id" type="var">SSCase</span> "x=y2".\
         <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>...\
         <span class="id" type="tactic">subst</span>.\
         <span class="id" type="tactic">intros</span> <span class="id"
type="var">z</span> <span class="id" type="var">Hafi</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
         <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">y2</span> <span class="id" type="var">z</span>)...\
       <span class="id" type="var">SSCase</span> "x≠y2".\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHt3</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">context\_invariance</span>...\
         <span class="id" type="tactic">intros</span> <span class="id"
type="var">z</span> <span class="id" type="var">Hafi</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
         <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">y1</span> <span class="id" type="var">z</span>)...\
         <span class="id" type="tactic">subst</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>...\
         <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">y2</span> <span class="id" type="var">z</span>)...\
         <span class="id" type="tactic">subst</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Preservation {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">preservation</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">t'</span> <span class="id"
type="var">T</span>,\
      <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t'</span> ∈ <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">t'</span> <span
class="id" type="var">T</span> <span class="id" type="var">HT</span>.\
   <span class="comment">(\* Theorem: If <span class="inlinecode"><span
class="id" type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span> and <span class="inlinecode"><span class="id"
type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id"
type="var">t'</span></span>, then <span class="inlinecode"><span
class="id" type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>. \*)</span>\
   <span class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id"
type="var">HeqGamma</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">t'</span>.\
   <span
class="comment">(\* Proof: By induction on the given typing derivation.  Many cases are\
      contradictory (<span class="inlinecode"><span class="id"
type="var">T\_Var</span></span>, <span class="inlinecode"><span
class="id"
type="var">T\_Abs</span></span>).  We show just the interesting ones. \*)</span>\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">HT</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">t'</span> <span class="id" type="var">HeqGamma</span> <span
class="id" type="var">HE</span>; <span class="id"
type="tactic">subst</span>; <span class="id"
type="tactic">inversion</span> <span class="id" type="var">HE</span>;
<span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="comment">(\* If the last rule used was <span
class="inlinecode"><span class="id"
type="var">T\_App</span></span>, then <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">t~1~</span></span>
<span class="inlinecode"><span class="id"
type="var">t~2~</span></span>, and three rules\
        could have been used to show <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span>: <span
class="inlinecode"><span class="id"
type="var">ST\_App1</span></span>, <span class="inlinecode"><span
class="id" type="var">ST\_App2</span></span>, and \
        <span class="inlinecode"><span class="id"
type="var">ST\_AppAbs</span></span>. In the first two cases, the result follows directly from \
        the IH. \*)</span>\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">SCase</span> "ST\_AppAbs".\
       <span class="comment">(\* For the third case, suppose \
            <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">tabs</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">T~11~</span></span> <span
class="inlinecode"><span class="id" type="var">t~12~</span></span>\
          and\
            <span class="inlinecode"><span class="id"
type="var">t~2~</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">v~2~</span></span>.  \
          We must show that <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v~2~</span>]<span class="id"
type="var">t~12~</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">T~2~</span></span>. \
          We know by assumption that\
              <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">tabs</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">T~11~</span></span> <span
class="inlinecode"><span class="id" type="var">t~12~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~1~</span><span style="font-family: arial;">→</span><span
class="id" type="var">T~2~</span></span>\
          and by inversion\
              <span class="inlinecode"><span class="id"
type="var">x</span>:<span class="id" type="var">T~1~</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t~12~</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T~2~</span></span>\

         We have already proven that substitution\_preserves\_typing and \
              <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">v~2~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~1~</span></span>\
          by assumption, so we are done. \*)</span>\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">substitution\_preserves\_typing</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">T~1~</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT1</span>...\
   <span class="id" type="var">Case</span> "T\_Fst".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT</span>...\
   <span class="id" type="var">Case</span> "T\_Snd".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT</span>...\
 <span class="comment">(\* let \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
   <span class="id" type="var">Case</span> "T\_Case".\
     <span class="id" type="var">SCase</span> "ST\_CaseInl".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT1</span>; <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">substitution\_preserves\_typing</span>...\
     <span class="id" type="var">SCase</span> "ST\_CaseInr".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT1</span>; <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">substitution\_preserves\_typing</span>...\
   <span class="id" type="var">Case</span> "T\_Lcase".\
     <span class="id" type="var">SCase</span> "ST\_LcaseCons".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT1</span>; <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">substitution\_preserves\_typing</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">TList</span>
<span class="id" type="var">T~1~</span>)...\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">substitution\_preserves\_typing</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">T~1~</span>...\
 <span class="comment">(\* fix \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
 <span class="id" type="keyword">Qed</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">STLCExtended</span>.\
\
 <span
class="comment">(\* \$Date: 2014-12-01 15:15:02 -0500 (Mon, 01 Dec 2014) \$ \*)</span>\
\

</div>

</div>

<div id="footer">

------------------------------------------------------------------------

[Index](http://www.cis.upenn.edu/~bcpierce/sf/current/coqindex.html)

</div>

</div>
