<div id="page">

<div id="header">

</div>

<div id="main">

Prop<span class="subtitle">Propositions and Evidence</span> {.libtitle}
===========================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">Logic</span>.\
\

</div>

<div class="doc">

Inductively Defined Propositions {.section}
================================

<div class="paragraph">

</div>

In chapter <span class="inlinecode"><span class="id"
type="var">Basics</span></span> we defined a *function* <span
class="inlinecode"><span class="id" type="var">evenb</span></span> that
tests a number for evenness, yielding <span class="inlinecode"><span
class="id" type="var">true</span></span> if so. We can use this function
to define the *proposition* that some number <span
class="inlinecode"><span class="id" type="var">n</span></span> is even:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">even</span> (<span class="id" type="var">n</span>:<span
class="id" type="var">nat</span>) : <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">evenb</span> <span class="id"
type="var">n</span> = <span class="id" type="var">true</span>.\
\

</div>

<div class="doc">

That is, we can define "<span class="inlinecode"><span class="id"
type="var">n</span></span> is even" to mean "the function <span
class="inlinecode"><span class="id" type="var">evenb</span></span>
returns <span class="inlinecode"><span class="id"
type="var">true</span></span> when applied to <span
class="inlinecode"><span class="id" type="var">n</span></span>."
<div class="paragraph">

</div>

Note that here we have given a name to a proposition using a <span
class="inlinecode"><span class="id"
type="keyword">Definition</span></span>, just as we have given names to
expressions of other sorts. This isn't a fundamentally new kind of
proposition; it is still just an equality.
<div class="paragraph">

</div>

Another alternative is to define the concept of evenness directly.
Instead of going via the <span class="inlinecode"><span class="id"
type="var">evenb</span></span> function ("a number is even if a certain
computation yields <span class="inlinecode"><span class="id"
type="var">true</span></span>"), we can say what the concept of evenness
means by giving two different ways of presenting *evidence* that a
number is even.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ev</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">ev\_0</span> : <span class="id"
type="var">ev</span> <span class="id" type="var">O</span>\
   | <span class="id" type="var">ev\_SS</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>, <span
class="id" type="var">ev</span> <span class="id" type="var">n</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">ev</span> (<span class="id" type="var">S</span> (<span
class="id" type="var">S</span> <span class="id" type="var">n</span>)).\
\

</div>

<div class="doc">

The first line declares that <span class="inlinecode"><span class="id"
type="var">ev</span></span> is a proposition — or, more formally, a
family of propositions "indexed by" natural numbers. (That is, for each
number <span class="inlinecode"><span class="id"
type="var">n</span></span>, the claim that "<span
class="inlinecode"><span class="id" type="var">n</span></span> is even"
is a proposition.) Such a family of propositions is often called a
*property* of numbers.
<div class="paragraph">

</div>

The last two lines declare the two ways to give evidence that a number
<span class="inlinecode"><span class="id" type="var">m</span></span> is
even. First, <span class="inlinecode">0</span> is even, and <span
class="inlinecode"><span class="id" type="var">ev\_0</span></span> is
evidence for this. Second, if <span class="inlinecode"><span class="id"
type="var">m</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">S</span></span> <span
class="inlinecode">(<span class="id" type="var">S</span></span> <span
class="inlinecode"><span class="id" type="var">n</span>)</span> for some
<span class="inlinecode"><span class="id" type="var">n</span></span> and
we can give evidence <span class="inlinecode"><span class="id"
type="var">e</span></span> that <span class="inlinecode"><span
class="id" type="var">n</span></span> is even, then <span
class="inlinecode"><span class="id" type="var">m</span></span> is also
even, and <span class="inlinecode"><span class="id"
type="var">ev\_SS</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode"><span
class="id" type="var">e</span></span> is the evidence.
<div class="paragraph">

</div>

#### Exercise: 1 star (double\_even) {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">double\_even</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
   <span class="id" type="var">ev</span> (<span class="id"
type="var">double</span> <span class="id" type="var">n</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
\

</div>

<div class="doc">

For <span class="inlinecode"><span class="id"
type="var">ev</span></span>, we had already defined <span
class="inlinecode"><span class="id" type="var">even</span></span> as a
function (returning a boolean), and then defined an inductive relation
that agreed with it. However, we don't necessarily need to think about
propositions first as boolean functions, we can start off with the
inductive definition.
<div class="paragraph">

</div>

As another example of an inductively defined proposition, let's define a
simple property of natural numbers — we'll call it "<span
class="inlinecode"><span class="id" type="var">beautiful</span></span>."
<div class="paragraph">

</div>

Informally, a number is <span class="inlinecode"><span class="id"
type="var">beautiful</span></span> if it is <span
class="inlinecode">0</span>, <span class="inlinecode">3</span>, <span
class="inlinecode">5</span>, or the sum of two <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>
numbers.
<div class="paragraph">

</div>

More pedantically, we can define <span class="inlinecode"><span
class="id" type="var">beautiful</span></span> numbers by giving four
rules:
<div class="paragraph">

</div>

-   Rule <span class="inlinecode"><span class="id"
    type="var">b\_0</span></span>: The number <span
    class="inlinecode">0</span> is <span class="inlinecode"><span
    class="id" type="var">beautiful</span></span>.
-   Rule <span class="inlinecode"><span class="id"
    type="var">b\_3</span></span>: The number <span
    class="inlinecode">3</span> is <span class="inlinecode"><span
    class="id" type="var">beautiful</span></span>.
-   Rule <span class="inlinecode"><span class="id"
    type="var">b\_5</span></span>: The number <span
    class="inlinecode">5</span> is <span class="inlinecode"><span
    class="id" type="var">beautiful</span></span>.
-   Rule <span class="inlinecode"><span class="id"
    type="var">b\_sum</span></span>: If <span class="inlinecode"><span
    class="id" type="var">n</span></span> and <span
    class="inlinecode"><span class="id" type="var">m</span></span> are
    both <span class="inlinecode"><span class="id"
    type="var">beautiful</span></span>, then so is their sum.

<div class="paragraph">

</div>

We will see many definitions like this one during the rest of the
course, and for purposes of informal discussions, it is helpful to have
a lightweight notation that makes them easy to read and write.
*Inference rules* are one such notation:
<div class="paragraph">

</div>

  
(b\_0)  

------------------------------------------------------------------------

beautiful 0
  
(b\_3)  

------------------------------------------------------------------------

beautiful 3
  
(b\_5)  

------------------------------------------------------------------------

beautiful 5
beautiful n     beautiful m
(b\_sum)  

------------------------------------------------------------------------

beautiful (n+m)
<div class="paragraph">

</div>

###  {.section}

Each of the textual rules above is reformatted here as an inference
rule; the intended reading is that, if the *premises* above the line all
hold, then the *conclusion* below the line follows. For example, the
rule <span class="inlinecode"><span class="id"
type="var">b\_sum</span></span> says that, if <span
class="inlinecode"><span class="id" type="var">n</span></span> and <span
class="inlinecode"><span class="id" type="var">m</span></span> are both
<span class="inlinecode"><span class="id"
type="var">beautiful</span></span> numbers, then it follows that <span
class="inlinecode"><span class="id" type="var">n</span>+<span class="id"
type="var">m</span></span> is <span class="inlinecode"><span class="id"
type="var">beautiful</span></span> too. If a rule has no premises above
the line, then its conclusion holds unconditionally.
<div class="paragraph">

</div>

These rules *define* the property <span class="inlinecode"><span
class="id" type="var">beautiful</span></span>. That is, if we want to
convince someone that some particular number is <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>,
our argument must be based on these rules. For a simple example, suppose
we claim that the number <span class="inlinecode">5</span> is <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>.
To support this claim, we just need to point out that rule <span
class="inlinecode"><span class="id" type="var">b\_5</span></span> says
so. Or, if we want to claim that <span class="inlinecode">8</span> is
<span class="inlinecode"><span class="id"
type="var">beautiful</span></span>, we can support our claim by first
observing that <span class="inlinecode">3</span> and <span
class="inlinecode">5</span> are both <span class="inlinecode"><span
class="id" type="var">beautiful</span></span> (by rules <span
class="inlinecode"><span class="id" type="var">b\_3</span></span> and
<span class="inlinecode"><span class="id" type="var">b\_5</span></span>)
and then pointing out that their sum, <span class="inlinecode">8</span>,
is therefore <span class="inlinecode"><span class="id"
type="var">beautiful</span></span> by rule <span
class="inlinecode"><span class="id" type="var">b\_sum</span></span>.
This argument can be expressed graphically with the following *proof
tree*:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

         ----------- (<span class="id"
type="var">b\_3</span>)   ----------- (<span class="id"
type="var">b\_5</span>)\
          <span class="id" type="var">beautiful</span> 3         <span
class="id" type="var">beautiful</span> 5\
          ------------------------------- (<span class="id"
type="var">b\_sum</span>)\
                    <span class="id" type="var">beautiful</span> 8   
<div class="paragraph">

</div>

</div>

###  {.section}

<div class="paragraph">

</div>

Of course, there are other ways of using these rules to argue that <span
class="inlinecode">8</span> is <span class="inlinecode"><span class="id"
type="var">beautiful</span></span>, for instance:
<div class="paragraph">

</div>

<div class="code code-tight">

         ----------- (<span class="id"
type="var">b\_5</span>)   ----------- (<span class="id"
type="var">b\_3</span>)\
          <span class="id" type="var">beautiful</span> 5         <span
class="id" type="var">beautiful</span> 3\
          ------------------------------- (<span class="id"
type="var">b\_sum</span>)\
                    <span class="id" type="var">beautiful</span> 8   
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

#### Exercise: 1 star (varieties\_of\_beauty) {.section}

How many different ways are there to show that <span
class="inlinecode">8</span> is <span class="inlinecode"><span class="id"
type="var">beautiful</span></span>?

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Constructing Evidence {.section}
---------------------

<div class="paragraph">

</div>

In Coq, we can express the definition of <span class="inlinecode"><span
class="id" type="var">beautiful</span></span> as follows:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">beautiful</span> : <span class="id" type="var">nat</span>
<span style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">b\_0</span> : <span class="id"
type="var">beautiful</span> 0\
 | <span class="id" type="var">b\_3</span> : <span class="id"
type="var">beautiful</span> 3\
 | <span class="id" type="var">b\_5</span> : <span class="id"
type="var">beautiful</span> 5\
 | <span class="id" type="var">b\_sum</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>, <span class="id"
type="var">beautiful</span> <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">beautiful</span> <span class="id" type="var">m</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">beautiful</span> (<span class="id" type="var">n</span>+<span
class="id" type="var">m</span>).\
\

</div>

<div class="doc">

###  {.section}

<div class="paragraph">

</div>

The rules introduced this way have the same status as proven theorems;
that is, they are true axiomatically. So we can use Coq's <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
tactic with the rule names to prove that particular numbers are <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">three\_is\_beautiful</span>: <span class="id"
type="var">beautiful</span> 3.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="comment">(\* This simply follows from the rule <span
class="inlinecode"><span class="id"
type="var">b\_3</span></span>. \*)</span>\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_3</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">eight\_is\_beautiful</span>: <span class="id"
type="var">beautiful</span> 8.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="comment">(\* First we use the rule <span
class="inlinecode"><span class="id"
type="var">b\_sum</span></span>, telling Coq how to\
       instantiate <span class="inlinecode"><span class="id"
type="var">n</span></span> and <span class="inlinecode"><span class="id"
type="var">m</span></span>. \*)</span>\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_sum</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">n</span>:=3) (<span class="id"
type="var">m</span>:=5).\
    <span class="comment">(\* To solve the subgoals generated by <span
class="inlinecode"><span class="id"
type="var">b\_sum</span></span>, we must provide\
       evidence of <span class="inlinecode"><span class="id"
type="var">beautiful</span></span> <span
class="inlinecode">3</span> and <span class="inlinecode"><span
class="id" type="var">beautiful</span></span> <span
class="inlinecode">5</span>. Fortunately we\
       have rules for both. \*)</span>\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_3</span>.\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_5</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

As you would expect, we can also prove theorems that have hypotheses
about <span class="inlinecode"><span class="id"
type="var">beautiful</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">beautiful\_plus\_eight</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">beautiful</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">beautiful</span> (8+<span class="id" type="var">n</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">B</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_sum</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">n</span>:=8) (<span class="id"
type="var">m</span>:=<span class="id" type="var">n</span>).\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">eight\_is\_beautiful</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">B</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (b\_times2) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">b\_times2</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">beautiful</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">beautiful</span> (2×<span class="id" type="var">n</span>).\
 <span class="id" type="keyword">Proof</span>.\
     <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (b\_timesm) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">b\_timesm</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>, <span class="id"
type="var">beautiful</span> <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">beautiful</span> (<span class="id" type="var">m</span>×<span
class="id" type="var">n</span>).\
 <span class="id" type="keyword">Proof</span>.\
    <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Using Evidence in Proofs {.section}
========================

Induction over Evidence {.section}
-----------------------

<div class="paragraph">

</div>

Besides *constructing* evidence that numbers are beautiful, we can also
*reason about* such evidence.
<div class="paragraph">

</div>

The fact that we introduced <span class="inlinecode"><span class="id"
type="var">beautiful</span></span> with an <span
class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> declaration tells Coq not only
that the constructors <span class="inlinecode"><span class="id"
type="var">b\_0</span></span>, <span class="inlinecode"><span class="id"
type="var">b\_3</span></span>, <span class="inlinecode"><span class="id"
type="var">b\_5</span></span> and <span class="inlinecode"><span
class="id" type="var">b\_sum</span></span> are ways to build evidence,
but also that these four constructors are the *only* ways to build
evidence that numbers are beautiful.
<div class="paragraph">

</div>

In other words, if someone gives us evidence <span
class="inlinecode"><span class="id" type="var">E</span></span> for the
assertion <span class="inlinecode"><span class="id"
type="var">beautiful</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span>, then we know that <span
class="inlinecode"><span class="id" type="var">E</span></span> must have
one of four shapes:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">E</span></span>
    is <span class="inlinecode"><span class="id"
    type="var">b\_0</span></span> (and <span class="inlinecode"><span
    class="id" type="var">n</span></span> is <span
    class="inlinecode"><span class="id" type="var">O</span></span>),
-   <span class="inlinecode"><span class="id" type="var">E</span></span>
    is <span class="inlinecode"><span class="id"
    type="var">b\_3</span></span> (and <span class="inlinecode"><span
    class="id" type="var">n</span></span> is <span
    class="inlinecode">3</span>),
-   <span class="inlinecode"><span class="id" type="var">E</span></span>
    is <span class="inlinecode"><span class="id"
    type="var">b\_5</span></span> (and <span class="inlinecode"><span
    class="id" type="var">n</span></span> is <span
    class="inlinecode">5</span>), or
-   <span class="inlinecode"><span class="id" type="var">E</span></span>
    is <span class="inlinecode"><span class="id"
    type="var">b\_sum</span></span> <span class="inlinecode"><span
    class="id" type="var">n1</span></span> <span
    class="inlinecode"><span class="id" type="var">n2</span></span>
    <span class="inlinecode"><span class="id"
    type="var">E1</span></span> <span class="inlinecode"><span
    class="id" type="var">E2</span></span> (and <span
    class="inlinecode"><span class="id" type="var">n</span></span> is
    <span class="inlinecode"><span class="id" type="var">n1</span>+<span
    class="id" type="var">n2</span></span>, where <span
    class="inlinecode"><span class="id" type="var">E1</span></span> is
    evidence that <span class="inlinecode"><span class="id"
    type="var">n1</span></span> is beautiful and <span
    class="inlinecode"><span class="id" type="var">E2</span></span> is
    evidence that <span class="inlinecode"><span class="id"
    type="var">n2</span></span> is beautiful).

<div class="paragraph">

</div>

###  {.section}

This permits us to *analyze* any hypothesis of the form <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span> to
see how it was constructed, using the tactics we already know. In
particular, we can use the <span class="inlinecode"><span class="id"
type="tactic">induction</span></span> tactic that we have already seen
for reasoning about inductively defined *data* to reason about
inductively defined *evidence*.
<div class="paragraph">

</div>

To illustrate this, let's define another property of numbers:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">gorgeous</span> : <span class="id" type="var">nat</span>
<span style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">g\_0</span> : <span class="id"
type="var">gorgeous</span> 0\
 | <span class="id" type="var">g\_plus3</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">gorgeous</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">gorgeous</span> (3+<span class="id" type="var">n</span>)\
 | <span class="id" type="var">g\_plus5</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">gorgeous</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">gorgeous</span> (5+<span class="id" type="var">n</span>).\
\

</div>

<div class="doc">

#### Exercise: 1 star (gorgeous\_tree) {.section}

Write out the definition of <span class="inlinecode"><span class="id"
type="var">gorgeous</span></span> numbers using inference rule notation.
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 1 star (gorgeous\_plus13) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">gorgeous\_plus13</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
   <span class="id" type="var">gorgeous</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">gorgeous</span> (13+<span class="id"
type="var">n</span>).\
 <span class="id" type="keyword">Proof</span>.\
    <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

###  {.section}

It seems intuitively obvious that, although <span
class="inlinecode"><span class="id" type="var">gorgeous</span></span>
and <span class="inlinecode"><span class="id"
type="var">beautiful</span></span> are presented using slightly
different rules, they are actually the same property in the sense that
they are true of the same numbers. Indeed, we can prove this.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">gorgeous\_\_beautiful\_FAILED</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
   <span class="id" type="var">gorgeous</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">beautiful</span> <span class="id"
type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">n</span>
<span class="id" type="keyword">as</span> [| <span class="id"
type="var">n'</span>].\
    <span class="id" type="var">Case</span> "n = 0". <span class="id"
type="tactic">apply</span> <span class="id" type="var">b\_0</span>.\
    <span class="id" type="var">Case</span> "n = S n'". <span
class="comment">(\* We are stuck! \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

The problem here is that doing induction on <span
class="inlinecode"><span class="id" type="var">n</span></span> doesn't
yield a useful induction hypothesis. Knowing how the property we are
interested in behaves on the predecessor of <span
class="inlinecode"><span class="id" type="var">n</span></span> doesn't
help us prove that it holds for <span class="inlinecode"><span
class="id" type="var">n</span></span>. Instead, we would like to be able
to have induction hypotheses that mention other numbers, such as <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">-</span> <span class="inlinecode">3</span> and <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">-</span> <span class="inlinecode">5</span>. This is
given precisely by the shape of the constructors for <span
class="inlinecode"><span class="id" type="var">gorgeous</span></span>.
<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

Let's see what happens if we try to prove this by induction on the
evidence <span class="inlinecode"><span class="id"
type="var">H</span></span> instead of on <span class="inlinecode"><span
class="id" type="var">n</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">gorgeous\_\_beautiful</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
   <span class="id" type="var">gorgeous</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">beautiful</span> <span class="id"
type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">H</span>.\
    <span class="id" type="tactic">induction</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">n'</span>|<span class="id" type="var">n'</span>].\
    <span class="id" type="var">Case</span> "g\_0".\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_0</span>.\
    <span class="id" type="var">Case</span> "g\_plus3".\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_sum</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">b\_3</span>.\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHgorgeous</span>.\
    <span class="id" type="var">Case</span> "g\_plus5".\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_sum</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">b\_5</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">IHgorgeous</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span
class="comment">(\* These exercises also require the use of induction on the evidence. \*)</span>\
\

</div>

<div class="doc">

#### Exercise: 2 stars (gorgeous\_sum) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">gorgeous\_sum</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">gorgeous</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">gorgeous</span> <span class="id"
type="var">m</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">gorgeous</span> (<span class="id"
type="var">n</span> + <span class="id" type="var">m</span>).\
 <span class="id" type="keyword">Proof</span>.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (beautiful\_\_gorgeous) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">beautiful\_\_gorgeous</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">beautiful</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">gorgeous</span> <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (g\_times2) {.section}

Prove the <span class="inlinecode"><span class="id"
type="var">g\_times2</span></span> theorem below without using <span
class="inlinecode"><span class="id"
type="var">gorgeous\_\_beautiful</span></span>. You might find the
following helper lemma useful.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">helper\_g\_times2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">y</span> <span class="id"
type="var">z</span>, <span class="id" type="var">x</span> + (<span
class="id" type="var">z</span> + <span class="id" type="var">y</span>) =
<span class="id" type="var">z</span> + <span class="id"
type="var">x</span> + <span class="id" type="var">y</span>.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">g\_times2</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">gorgeous</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">gorgeous</span> (2×<span class="id" type="var">n</span>).\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">simpl</span>.\
    <span class="id" type="tactic">induction</span> <span class="id"
type="var">H</span>.\
    <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Here is a proof that the inductive definition of evenness implies the
computational one.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ev\_\_even</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
   <span class="id" type="var">ev</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">even</span> <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">E</span>. <span
class="id" type="tactic">induction</span> <span class="id"
type="var">E</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">n'</span> <span class="id" type="var">E'</span>].\
   <span class="id" type="var">Case</span> "E = ev\_0".\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">even</span>. <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "E = ev\_SS n' E'".\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">even</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">IHE'</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star (ev\_\_even) {.section}

Could this proof also be carried out by induction on <span
class="inlinecode"><span class="id" type="var">n</span></span> instead
of <span class="inlinecode"><span class="id" type="var">E</span></span>?
If not, why not?

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Intuitively, the induction principle <span class="inlinecode"><span
class="id" type="var">ev</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> evidence <span
class="inlinecode"><span class="id" type="var">ev</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> is
similar to induction on <span class="inlinecode"><span class="id"
type="var">n</span></span>, but restricts our attention to only those
numbers for which evidence <span class="inlinecode"><span class="id"
type="var">ev</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> could be generated.
<div class="paragraph">

</div>

#### Exercise: 1 star (l\_fails) {.section}

The following proof attempt will not succeed.
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">l</span> : <span style="font-family: arial;">∀</span><span
class="id" type="var">n</span>,\
        <span class="id" type="var">ev</span> <span class="id"
type="var">n</span>.\
      <span class="id" type="keyword">Proof</span>.\
        <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">n</span>.\
          <span class="id" type="var">Case</span> "O". <span class="id"
type="tactic">simpl</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">ev\_0</span>.\
          <span class="id" type="var">Case</span> "S".\
            ...
<div class="paragraph">

</div>

</div>

Intuitively, we expect the proof to fail because not every number is
even. However, what exactly causes the proof to fail?
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

Here's another exercise requiring induction on evidence.
#### Exercise: 2 stars (ev\_sum) {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ev\_sum</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
    <span class="id" type="var">ev</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ev</span> <span class="id" type="var">m</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">ev</span> (<span class="id" type="var">n</span>+<span
class="id" type="var">m</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Inversion on Evidence {.section}
---------------------

<div class="paragraph">

</div>

Having evidence for a proposition is useful while proving, because we
can *look* at that evidence for more information. For example, consider
proving that, if <span class="inlinecode"><span class="id"
type="var">n</span></span> is even, then <span class="inlinecode"><span
class="id" type="var">pred</span></span> <span class="inlinecode">(<span
class="id" type="var">pred</span></span> <span class="inlinecode"><span
class="id" type="var">n</span>)</span> is too. In this case, we don't
need to do an inductive proof. Instead the <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span> tactic provides all of the
information that we need.
<div class="paragraph">

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ev\_minus2</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">ev</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ev</span> (<span class="id" type="var">pred</span> (<span
class="id" type="var">pred</span> <span class="id"
type="var">n</span>)).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">E</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">E</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">n'</span> <span class="id" type="var">E'</span>].\
   <span class="id" type="var">Case</span> "E = ev\_0". <span class="id"
type="tactic">simpl</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">ev\_0</span>.\
   <span class="id" type="var">Case</span> "E = ev\_SS n' E'". <span
class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">E'</span>. <span
class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star, optional (ev\_minus2\_n) {.section}

What happens if we try to use <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> on <span class="inlinecode"><span
class="id" type="var">n</span></span> instead of <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span> on <span class="inlinecode"><span
class="id" type="var">E</span></span>?

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

###  {.section}

Here is another example, in which <span class="inlinecode"><span
class="id" type="tactic">inversion</span></span> helps narrow down to
the relevant cases.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">SSev\_\_even</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
   <span class="id" type="var">ev</span> (<span class="id"
type="var">S</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>)) <span
style="font-family: arial;">→</span> <span class="id"
type="var">ev</span> <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">E</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">E</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">n'</span> <span class="id" type="var">E'</span>].\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">E'</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The Inversion Tactic Revisited {.section}
------------------------------

<div class="paragraph">

</div>

These uses of <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> may seem a bit mysterious at
first. Until now, we've only used <span class="inlinecode"><span
class="id" type="tactic">inversion</span></span> on equality
propositions, to utilize injectivity of constructors or to discriminate
between different constructors. But we see here that <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span> can also be applied to analyzing
evidence for inductively defined propositions.
<div class="paragraph">

</div>

(You might also expect that <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> would be a more suitable tactic to
use here. Indeed, it is possible to use <span class="inlinecode"><span
class="id" type="tactic">destruct</span></span>, but it often throws
away useful information, and the <span class="inlinecode"><span
class="id" type="var">eqn</span>:</span> qualifier doesn't help much in
this case.)
<div class="paragraph">

</div>

Here's how <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> works in general. Suppose the name
<span class="inlinecode"><span class="id" type="var">I</span></span>
refers to an assumption <span class="inlinecode"><span class="id"
type="var">P</span></span> in the current context, where <span
class="inlinecode"><span class="id" type="var">P</span></span> has been
defined by an <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> declaration. Then, for each of
the constructors of <span class="inlinecode"><span class="id"
type="var">P</span></span>, <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> <span class="inlinecode"><span
class="id" type="var">I</span></span> generates a subgoal in which <span
class="inlinecode"><span class="id" type="var">I</span></span> has been
replaced by the exact, specific conditions under which this constructor
could have been used to prove <span class="inlinecode"><span class="id"
type="var">P</span></span>. Some of these subgoals will be
self-contradictory; <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> throws these away. The ones that
are left represent the cases that must be proved to establish the
original goal.
<div class="paragraph">

</div>

In this particular case, the <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> analyzed the construction <span
class="inlinecode"><span class="id" type="var">ev</span></span> <span
class="inlinecode">(<span class="id" type="var">S</span></span> <span
class="inlinecode">(<span class="id" type="var">S</span></span> <span
class="inlinecode"><span class="id" type="var">n</span>))</span>,
determined that this could only have been constructed using <span
class="inlinecode"><span class="id" type="var">ev\_SS</span></span>, and
generated a new subgoal with the arguments of that constructor as new
hypotheses. (It also produced an auxiliary equality, which happens to be
useless here.) We'll begin exploring this more general behavior of
inversion in what follows.
<div class="paragraph">

</div>

#### Exercise: 1 star (inversion\_practice) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">SSSSev\_\_even</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
   <span class="id" type="var">ev</span> (<span class="id"
type="var">S</span> (<span class="id" type="var">S</span> (<span
class="id" type="var">S</span> (<span class="id" type="var">S</span>
<span class="id" type="var">n</span>)))) <span
style="font-family: arial;">→</span> <span class="id"
type="var">ev</span> <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> tactic can also be used to derive
goals by showing the absurdity of a hypothesis.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">even5\_nonsense</span> :\
   <span class="id" type="var">ev</span> 5 <span
style="font-family: arial;">→</span> 2 + 2 = 9.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (ev\_ev\_\_ev) {.section}

Finding the appropriate thing to do induction on is a bit tricky here:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ev\_ev\_\_ev</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">ev</span> (<span class="id"
type="var">n</span>+<span class="id" type="var">m</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">ev</span> <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ev</span> <span class="id" type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (ev\_plus\_plus) {.section}

Here's an exercise that just requires applying existing lemmas. No
induction or even case analysis is needed, but some of the rewriting may
be tedious.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ev\_plus\_plus</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> <span class="id"
type="var">p</span>,\
   <span class="id" type="var">ev</span> (<span class="id"
type="var">n</span>+<span class="id" type="var">m</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">ev</span> (<span class="id" type="var">n</span>+<span
class="id" type="var">p</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">ev</span> (<span class="id" type="var">m</span>+<span
class="id" type="var">p</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Discussion and Variations {.section}
=========================

Computational vs. Inductive Definitions {.section}
---------------------------------------

<div class="paragraph">

</div>

We have seen that the proposition "<span class="inlinecode"><span
class="id" type="var">n</span></span> is even" can be phrased in two
different ways — indirectly, via a boolean testing function <span
class="inlinecode"><span class="id" type="var">evenb</span></span>, or
directly, by inductively describing what constitutes evidence for
evenness. These two ways of defining evenness are about equally easy to
state and work with. Which we choose is basically a question of taste.
<div class="paragraph">

</div>

However, for many other properties of interest, the direct inductive
definition is preferable, since writing a testing function may be
awkward or even impossible.
<div class="paragraph">

</div>

One such property is <span class="inlinecode"><span class="id"
type="var">beautiful</span></span>. This is a perfectly sensible
definition of a set of numbers, but we cannot translate its definition
directly into a Coq Fixpoint (or into a recursive function in any other
common programming language). We might be able to find a clever way of
testing this property using a <span class="inlinecode"><span class="id"
type="keyword">Fixpoint</span></span> (indeed, it is not too hard to
find one in this case), but in general this could require arbitrarily
deep thinking. In fact, if the property we are interested in is
uncomputable, then we cannot define it as a <span
class="inlinecode"><span class="id"
type="keyword">Fixpoint</span></span> no matter how hard we try, because
Coq requires that all <span class="inlinecode"><span class="id"
type="keyword">Fixpoint</span></span>s correspond to terminating
computations.
<div class="paragraph">

</div>

On the other hand, writing an inductive definition of what it means to
give evidence for the property <span class="inlinecode"><span class="id"
type="var">beautiful</span></span> is straightforward.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Parameterized Data Structures {.section}
-----------------------------

<div class="paragraph">

</div>

So far, we have only looked at propositions about natural numbers.
However, we can define inductive predicates about any type of data. For
example, suppose we would like to characterize lists of *even* length.
We can do that with the following definition.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ev\_list</span> {<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>} : <span class="id"
type="var">list</span> <span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">el\_nil</span> : <span class="id"
type="var">ev\_list</span> []\
   | <span class="id" type="var">el\_cc</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">y</span> <span class="id"
type="var">l</span>, <span class="id" type="var">ev\_list</span> <span
class="id" type="var">l</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ev\_list</span> (<span class="id" type="var">x</span> ::
<span class="id" type="var">y</span> :: <span class="id"
type="var">l</span>).\
\

</div>

<div class="doc">

Of course, this proposition is equivalent to just saying that the length
of the list is even.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">ev\_list\_\_ev\_length</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">X</span>
(<span class="id" type="var">l</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span>), <span
class="id" type="var">ev\_list</span> <span class="id"
type="var">l</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ev</span> (<span class="id"
type="var">length</span> <span class="id" type="var">l</span>).\
 <span class="id" type="keyword">Proof</span>.\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">X</span> <span class="id" type="var">l</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>.\
     <span class="id" type="var">Case</span> "el\_nil". <span class="id"
type="tactic">simpl</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">ev\_0</span>.\
     <span class="id" type="var">Case</span> "el\_cc". <span class="id"
type="tactic">simpl</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">ev\_SS</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">IHev\_list</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

However, because evidence for <span class="inlinecode"><span class="id"
type="var">ev</span></span> contains less information than evidence for
<span class="inlinecode"><span class="id"
type="var">ev\_list</span></span>, the converse direction must be stated
very carefully.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">ev\_length\_\_ev\_list</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">X</span>
<span class="id" type="var">n</span>, <span class="id"
type="var">ev</span> <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">l</span> : <span class="id" type="var">list</span> <span
class="id" type="var">X</span>), <span class="id" type="var">n</span> =
<span class="id" type="var">length</span> <span class="id"
type="var">l</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ev\_list</span> <span class="id"
type="var">l</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">X</span> <span class="id" type="var">n</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="var">Case</span> "ev\_0". <span class="id"
type="tactic">intros</span> <span class="id" type="var">l</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">l</span>.\
     <span class="id" type="var">SCase</span> "[]". <span class="id"
type="tactic">apply</span> <span class="id" type="var">el\_nil</span>.\
     <span class="id" type="var">SCase</span> "x::l". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>.\
   <span class="id" type="var">Case</span> "ev\_SS". <span class="id"
type="tactic">intros</span> <span class="id" type="var">l</span> <span
class="id" type="var">H2</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">l</span>.\
     <span class="id" type="var">SCase</span> "[]". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H2</span>.
<span class="id" type="tactic">destruct</span> <span class="id"
type="var">l</span>.\
     <span class="id" type="var">SCase</span> "[x]". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H2</span>.\
     <span class="id" type="var">SCase</span> "x :: x0 :: l". <span
class="id" type="tactic">apply</span> <span class="id"
type="var">el\_cc</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">IHev</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H2</span>.
<span class="id" type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 4 stars (palindromes) {.section}

A palindrome is a sequence that reads the same backwards as forwards.
<div class="paragraph">

</div>

-   Define an inductive proposition <span class="inlinecode"><span
    class="id" type="var">pal</span></span> on <span
    class="inlinecode"><span class="id" type="var">list</span></span>
    <span class="inlinecode"><span class="id" type="var">X</span></span>
    that captures what it means to be a palindrome. (Hint: You'll need
    three cases. Your definition should be based on the structure of the
    list; just having a single constructor
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">c</span> : <span
    style="font-family: arial;">∀</span><span class="id"
    type="var">l</span>, <span class="id" type="var">l</span> = <span
    class="id" type="var">rev</span> <span class="id"
    type="var">l</span> <span style="font-family: arial;">→</span> <span
    class="id" type="var">pal</span> <span class="id"
    type="var">l</span>
    <div class="paragraph">

    </div>

    </div>

    may seem obvious, but will not work very well.)
    <div class="paragraph">

    </div>

-   Prove <span class="inlinecode"><span class="id"
    type="var">pal\_app\_rev</span></span> that
    <div class="paragraph">

    </div>

    <div class="code code-tight">

     <span style="font-family: arial;">∀</span><span class="id"
    type="var">l</span>, <span class="id" type="var">pal</span> (<span
    class="id" type="var">l</span> ++ <span class="id"
    type="var">rev</span> <span class="id" type="var">l</span>).
    <div class="paragraph">

    </div>

    </div>

-   Prove <span class="inlinecode"><span class="id"
    type="var">pal\_rev</span></span> that
    <div class="paragraph">

    </div>

    <div class="code code-tight">

     <span style="font-family: arial;">∀</span><span class="id"
    type="var">l</span>, <span class="id" type="var">pal</span> <span
    class="id" type="var">l</span> <span
    style="font-family: arial;">→</span> <span class="id"
    type="var">l</span> = <span class="id" type="var">rev</span> <span
    class="id" type="var">l</span>.
    <div class="paragraph">

    </div>

    </div>

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span
class="comment">(\* Again, the converse direction is much more difficult, due to the\
 lack of evidence. \*)</span>\
\

</div>

<div class="doc">

#### Exercise: 5 stars, optional (palindrome\_converse) {.section}

Using your definition of <span class="inlinecode"><span class="id"
type="var">pal</span></span> from the previous exercise, prove that
<div class="paragraph">

</div>

<div class="code code-tight">

     <span style="font-family: arial;">∀</span><span class="id"
type="var">l</span>, <span class="id" type="var">l</span> = <span
class="id" type="var">rev</span> <span class="id"
type="var">l</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">pal</span> <span class="id" type="var">l</span>.
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Relations {.section}
---------

<div class="paragraph">

</div>

A proposition parameterized by a number (such as <span
class="inlinecode"><span class="id" type="var">ev</span></span> or <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>)
can be thought of as a *property* — i.e., it defines a subset of <span
class="inlinecode"><span class="id" type="var">nat</span></span>, namely
those numbers for which the proposition is provable. In the same way, a
two-argument proposition can be thought of as a *relation* — i.e., it
defines a set of pairs for which the proposition is provable.

</div>

<div class="code code-tight">

\
\

</div>

<div class="doc">

One useful example is the "less than or equal to" relation on numbers.
<div class="paragraph">

</div>

The following definition should be fairly intuitive. It says that there
are two ways to give evidence that one number is less than or equal to
another: either observe that they are the same number, or give evidence
that the first is less than or equal to the predecessor of the second.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">le</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">le\_n</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">le</span> <span
class="id" type="var">n</span> <span class="id" type="var">n</span>\
   | <span class="id" type="var">le\_S</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>, (<span class="id"
type="var">le</span> <span class="id" type="var">n</span> <span
class="id" type="var">m</span>) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">le</span> <span class="id" type="var">n</span> (<span
class="id" type="var">S</span> <span class="id" type="var">m</span>)).\
\
 <span class="id" type="keyword">Notation</span> "m ≤ n" := (<span
class="id" type="var">le</span> <span class="id" type="var">m</span>
<span class="id" type="var">n</span>).\
\

</div>

<div class="doc">

Proofs of facts about <span class="inlinecode">≤</span> using the
constructors <span class="inlinecode"><span class="id"
type="var">le\_n</span></span> and <span class="inlinecode"><span
class="id" type="var">le\_S</span></span> follow the same patterns as
proofs about properties, like <span class="inlinecode"><span class="id"
type="var">ev</span></span> in chapter <span class="inlinecode"><span
class="id" type="keyword">Prop</span></span>. We can <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
the constructors to prove <span class="inlinecode">≤</span> goals (e.g.,
to show that <span class="inlinecode">3≤3</span> or <span
class="inlinecode">3≤6</span>), and we can use tactics like <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span> to extract information from <span
class="inlinecode">≤</span> hypotheses in the context (e.g., to prove
that <span class="inlinecode">(2</span> <span
class="inlinecode">≤</span> <span class="inlinecode">1)</span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode">2+2=5</span>.)
<div class="paragraph">

</div>

###  {.section}

Here are some sanity checks on the definition. (Notice that, although
these are the same kind of simple "unit tests" as we gave for the
testing functions we wrote in the first few lectures, we must construct
their proofs explicitly — <span class="inlinecode"><span class="id"
type="tactic">simpl</span></span> and <span class="inlinecode"><span
class="id" type="tactic">reflexivity</span></span> don't do the job,
because the proofs aren't just a matter of simplifying computations.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">test\_le1</span> :\
   3 ≤ 3.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">le\_n</span>. <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">test\_le2</span> :\
   3 ≤ 6.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">le\_S</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">le\_S</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">le\_S</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">le\_n</span>. <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">test\_le3</span> :\
   (2 ≤ 1) <span style="font-family: arial;">→</span> 2 + 2 = 5.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">inversion</span>
<span class="id" type="var">H</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H2</span>.
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

The "strictly less than" relation <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">\<</span>
<span class="inlinecode"><span class="id" type="var">m</span></span> can
now be defined in terms of <span class="inlinecode"><span class="id"
type="var">le</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">lt</span> (<span class="id" type="var">n</span> <span
class="id" type="var">m</span>:<span class="id" type="var">nat</span>)
:= <span class="id" type="var">le</span> (<span class="id"
type="var">S</span> <span class="id" type="var">n</span>) <span
class="id" type="var">m</span>.\
\
 <span class="id" type="keyword">Notation</span> "m \< n" := (<span
class="id" type="var">lt</span> <span class="id" type="var">m</span>
<span class="id" type="var">n</span>).\
\

</div>

<div class="doc">

Here are a few more simple relations on numbers:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">square\_of</span> : <span class="id" type="var">nat</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   <span class="id" type="var">sq</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>, <span
class="id" type="var">square\_of</span> <span class="id"
type="var">n</span> (<span class="id" type="var">n</span> × <span
class="id" type="var">n</span>).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">next\_nat</span> : <span class="id" type="var">nat</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">nn</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>, <span
class="id" type="var">next\_nat</span> <span class="id"
type="var">n</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">next\_even</span> : <span class="id" type="var">nat</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">ne\_1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">ev</span> (<span
class="id" type="var">S</span> <span class="id" type="var">n</span>)
<span style="font-family: arial;">→</span> <span class="id"
type="var">next\_even</span> <span class="id" type="var">n</span> (<span
class="id" type="var">S</span> <span class="id" type="var">n</span>)\
   | <span class="id" type="var">ne\_2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">ev</span> (<span
class="id" type="var">S</span> (<span class="id" type="var">S</span>
<span class="id" type="var">n</span>)) <span
style="font-family: arial;">→</span> <span class="id"
type="var">next\_even</span> <span class="id" type="var">n</span> (<span
class="id" type="var">S</span> (<span class="id" type="var">S</span>
<span class="id" type="var">n</span>)).\
\

</div>

<div class="doc">

#### Exercise: 2 stars (total\_relation) {.section}

Define an inductive binary relation <span class="inlinecode"><span
class="id" type="var">total\_relation</span></span> that holds between
every pair of natural numbers.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (empty\_relation) {.section}

Define an inductive binary relation <span class="inlinecode"><span
class="id" type="var">empty\_relation</span></span> (on numbers) that
never holds.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (le\_exercises) {.section}

Here are a number of facts about the <span class="inlinecode">≤</span>
and <span class="inlinecode">\<</span> relations that we are going to
need later in the course. The proofs make good practice exercises.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">le\_trans</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">m</span>
<span class="id" type="var">n</span> <span class="id"
type="var">o</span>, <span class="id" type="var">m</span> ≤ <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> ≤ <span class="id" type="var">o</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">m</span> ≤ <span class="id" type="var">o</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">O\_le\_n</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
   0 ≤ <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">n\_le\_m\_\_Sn\_le\_Sm</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">n</span> ≤ <span class="id"
type="var">m</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">S</span> <span class="id" type="var">n</span> ≤
<span class="id" type="var">S</span> <span class="id"
type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">Sn\_le\_Sm\_\_n\_le\_m</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">S</span> <span class="id"
type="var">n</span> ≤ <span class="id" type="var">S</span> <span
class="id" type="var">m</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> ≤ <span class="id" type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">le\_plus\_l</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">a</span>
<span class="id" type="var">b</span>,\
   <span class="id" type="var">a</span> ≤ <span class="id"
type="var">a</span> + <span class="id" type="var">b</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">plus\_lt</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> <span
class="id" type="var">m</span>,\
   <span class="id" type="var">n1</span> + <span class="id"
type="var">n2</span> \< <span class="id" type="var">m</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">n1</span> \< <span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">n2</span> \< <span class="id"
type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
  <span class="id" type="tactic">unfold</span> <span class="id"
type="var">lt</span>.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">lt\_S</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">n</span> \< <span class="id"
type="var">m</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">n</span> \< <span class="id"
type="var">S</span> <span class="id" type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ble\_nat\_true</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">ble\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> ≤ <span class="id" type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">le\_ble\_nat</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">n</span> ≤ <span class="id"
type="var">m</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">ble\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span
class="comment">(\* Hint: This may be easiest to prove by induction on <span
class="inlinecode"><span class="id"
type="var">m</span></span>. \*)</span>\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ble\_nat\_true\_trans</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> <span class="id"
type="var">o</span>,\
   <span class="id" type="var">ble\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ble\_nat</span> <span class="id" type="var">m</span> <span
class="id" type="var">o</span> = <span class="id" type="var">true</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">ble\_nat</span> <span class="id" type="var">n</span> <span
class="id" type="var">o</span> = <span class="id"
type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span
class="comment">(\* Hint: This theorem can be easily proved without using <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span>. \*)</span>\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (ble\_nat\_false) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ble\_nat\_false</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">ble\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span> \~(<span class="id"
type="var">n</span> ≤ <span class="id" type="var">m</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (R\_provability2) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Module</span> <span class="id"
type="var">R</span>.\

</div>

<div class="doc">

We can define three-place relations, four-place relations, etc., in just
the same way as binary relations. For example, consider the following
three-place relation on numbers:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">R</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
    | <span class="id" type="var">c1</span> : <span class="id"
type="var">R</span> 0 0 0\
    | <span class="id" type="var">c2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">m</span>
<span class="id" type="var">n</span> <span class="id"
type="var">o</span>, <span class="id" type="var">R</span> <span
class="id" type="var">m</span> <span class="id" type="var">n</span>
<span class="id" type="var">o</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> (<span class="id" type="var">S</span> <span
class="id" type="var">m</span>) <span class="id" type="var">n</span>
(<span class="id" type="var">S</span> <span class="id"
type="var">o</span>)\
    | <span class="id" type="var">c3</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">m</span>
<span class="id" type="var">n</span> <span class="id"
type="var">o</span>, <span class="id" type="var">R</span> <span
class="id" type="var">m</span> <span class="id" type="var">n</span>
<span class="id" type="var">o</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">m</span> (<span
class="id" type="var">S</span> <span class="id" type="var">n</span>)
(<span class="id" type="var">S</span> <span class="id"
type="var">o</span>)\
    | <span class="id" type="var">c4</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">m</span>
<span class="id" type="var">n</span> <span class="id"
type="var">o</span>, <span class="id" type="var">R</span> (<span
class="id" type="var">S</span> <span class="id" type="var">m</span>)
(<span class="id" type="var">S</span> <span class="id"
type="var">n</span>) (<span class="id" type="var">S</span> (<span
class="id" type="var">S</span> <span class="id" type="var">o</span>))
<span style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">m</span> <span
class="id" type="var">n</span> <span class="id" type="var">o</span>\
    | <span class="id" type="var">c5</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">m</span>
<span class="id" type="var">n</span> <span class="id"
type="var">o</span>, <span class="id" type="var">R</span> <span
class="id" type="var">m</span> <span class="id" type="var">n</span>
<span class="id" type="var">o</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">n</span> <span
class="id" type="var">m</span> <span class="id" type="var">o</span>.\
\

</div>

<div class="doc">

<div class="paragraph">

</div>

-   Which of the following propositions are provable?
    -   <span class="inlinecode"><span class="id"
        type="var">R</span></span> <span class="inlinecode">1</span>
        <span class="inlinecode">1</span> <span
        class="inlinecode">2</span>
    -   <span class="inlinecode"><span class="id"
        type="var">R</span></span> <span class="inlinecode">2</span>
        <span class="inlinecode">2</span> <span
        class="inlinecode">6</span>
        <div class="paragraph">

        </div>

        <div class="paragraph">

        </div>
-   If we dropped constructor <span class="inlinecode"><span class="id"
    type="var">c5</span></span> from the definition of <span
    class="inlinecode"><span class="id" type="var">R</span></span>,
    would the set of provable propositions change? Briefly (1 sentence)
    explain your answer.
    <div class="paragraph">

    </div>

-   If we dropped constructor <span class="inlinecode"><span class="id"
    type="var">c4</span></span> from the definition of <span
    class="inlinecode"><span class="id" type="var">R</span></span>,
    would the set of provable propositions change? Briefly (1 sentence)
    explain your answer.

<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (R\_fact) {.section}

Relation <span class="inlinecode"><span class="id"
type="var">R</span></span> actually encodes a familiar function. State
and prove two theorems that formally connects the relation and the
function. That is, if <span class="inlinecode"><span class="id"
type="var">R</span></span> <span class="inlinecode"><span class="id"
type="var">m</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode"><span class="id"
type="var">o</span></span> is true, what can we say about <span
class="inlinecode"><span class="id" type="var">m</span></span>, <span
class="inlinecode"><span class="id" type="var">n</span></span>, and
<span class="inlinecode"><span class="id" type="var">o</span></span>,
and vice versa?

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">R</span>.\
\

</div>

<div class="doc">

#### Exercise: 4 stars, advanced (subsequence) {.section}

A list is a *subsequence* of another list if all of the elements in the
first list occur in the same order in the second list, possibly with
some extra elements in between. For example,
<div class="paragraph">

</div>

<div class="code code-tight">

    [1,2,3]
<div class="paragraph">

</div>

</div>

is a subsequence of each of the lists
<div class="paragraph">

</div>

<div class="code code-tight">

    [1,2,3]\
     [1,1,1,2,2,3]\
     [1,2,7,3]\
     [5,6,1,9,9,2,7,3,8]
<div class="paragraph">

</div>

</div>

but it is *not* a subsequence of any of the lists
<div class="paragraph">

</div>

<div class="code code-tight">

    [1,2]\
     [1,3]\
     [5,6,2,1,7,3,8]
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

-   Define an inductive proposition <span class="inlinecode"><span
    class="id" type="var">subseq</span></span> on <span
    class="inlinecode"><span class="id" type="var">list</span></span>
    <span class="inlinecode"><span class="id"
    type="var">nat</span></span> that captures what it means to be a
    subsequence. (Hint: You'll need three cases.)
    <div class="paragraph">

    </div>

-   Prove <span class="inlinecode"><span class="id"
    type="var">subseq\_refl</span></span> that subsequence is reflexive,
    that is, any list is a subsequence of itself.
    <div class="paragraph">

    </div>

-   Prove <span class="inlinecode"><span class="id"
    type="var">subseq\_app</span></span> that for any lists <span
    class="inlinecode"><span class="id" type="var">l1</span></span>,
    <span class="inlinecode"><span class="id"
    type="var">l2</span></span>, and <span class="inlinecode"><span
    class="id" type="var">l3</span></span>, if <span
    class="inlinecode"><span class="id" type="var">l1</span></span> is a
    subsequence of <span class="inlinecode"><span class="id"
    type="var">l2</span></span>, then <span class="inlinecode"><span
    class="id" type="var">l1</span></span> is also a subsequence of
    <span class="inlinecode"><span class="id"
    type="var">l2</span></span> <span class="inlinecode">++</span> <span
    class="inlinecode"><span class="id" type="var">l3</span></span>.
    <div class="paragraph">

    </div>

-   (Optional, harder) Prove <span class="inlinecode"><span class="id"
    type="var">subseq\_trans</span></span> that subsequence is
    transitive — that is, if <span class="inlinecode"><span class="id"
    type="var">l1</span></span> is a subsequence of <span
    class="inlinecode"><span class="id" type="var">l2</span></span> and
    <span class="inlinecode"><span class="id"
    type="var">l2</span></span> is a subsequence of <span
    class="inlinecode"><span class="id" type="var">l3</span></span>,
    then <span class="inlinecode"><span class="id"
    type="var">l1</span></span> is a subsequence of <span
    class="inlinecode"><span class="id" type="var">l3</span></span>.
    Hint: choose your induction carefully!

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (R\_provability) {.section}

Suppose we give Coq the following definition:
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">R</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">list</span> <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
       | <span class="id" type="var">c1</span> : <span class="id"
type="var">R</span> 0 []\
       | <span class="id" type="var">c2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span> <span class="id" type="var">l</span>, <span
class="id" type="var">R</span> <span class="id"
type="var">n</span> <span class="id" type="var">l</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>) (<span class="id"
type="var">n</span> :: <span class="id" type="var">l</span>)\
       | <span class="id" type="var">c3</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span> <span class="id" type="var">l</span>, <span
class="id" type="var">R</span> (<span class="id"
type="var">S</span> <span class="id" type="var">n</span>) <span
class="id" type="var">l</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">n</span> <span
class="id" type="var">l</span>.
<div class="paragraph">

</div>

</div>

Which of the following propositions are provable?
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">R</span></span>
    <span class="inlinecode">2</span> <span
    class="inlinecode">[1,0]</span>
-   <span class="inlinecode"><span class="id" type="var">R</span></span>
    <span class="inlinecode">1</span> <span
    class="inlinecode">[1,2,1,0]</span>
-   <span class="inlinecode"><span class="id" type="var">R</span></span>
    <span class="inlinecode">6</span> <span
    class="inlinecode">[3,2,1,0]</span>

<div class="paragraph">

</div>

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Programming with Propositions {.section}
=============================

<div class="paragraph">

</div>

As we have seen, a *proposition* is a statement expressing a factual
claim, like "two plus two equals four." In Coq, propositions are written
as expressions of type <span class="inlinecode"><span class="id"
type="keyword">Prop</span></span>. .

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> (2 + 2 = 4).\
 <span class="comment">(\* ===\> 2 + 2 = 4 : Prop \*)</span>\
\
 <span class="id" type="keyword">Check</span> (<span class="id"
type="var">ble\_nat</span> 3 2 = <span class="id"
type="var">false</span>).\
 <span class="comment">(\* ===\> ble\_nat 3 2 = false : Prop \*)</span>\
\
 <span class="id" type="keyword">Check</span> (<span class="id"
type="var">beautiful</span> 8).\
 <span class="comment">(\* ===\> beautiful 8 : Prop \*)</span>\
\

</div>

<div class="doc">

###  {.section}

Both provable and unprovable claims are perfectly good propositions.
Simply *being* a proposition is one thing; being *provable* is something
else!

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> (2 + 2 = 5).\
 <span class="comment">(\* ===\> 2 + 2 = 5 : Prop \*)</span>\
\
 <span class="id" type="keyword">Check</span> (<span class="id"
type="var">beautiful</span> 4).\
 <span class="comment">(\* ===\> beautiful 4 : Prop \*)</span>\
\

</div>

<div class="doc">

Both <span class="inlinecode">2</span> <span class="inlinecode">+</span>
<span class="inlinecode">2</span> <span class="inlinecode">=</span>
<span class="inlinecode">4</span> and <span class="inlinecode">2</span>
<span class="inlinecode">+</span> <span class="inlinecode">2</span>
<span class="inlinecode">=</span> <span class="inlinecode">5</span> are
legal expressions of type <span class="inlinecode"><span class="id"
type="keyword">Prop</span></span>.
<div class="paragraph">

</div>

###  {.section}

We've mainly seen one place that propositions can appear in Coq: in
<span class="inlinecode"><span class="id"
type="keyword">Theorem</span></span> (and <span class="inlinecode"><span
class="id" type="keyword">Lemma</span></span> and <span
class="inlinecode"><span class="id"
type="keyword">Example</span></span>) declarations.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">plus\_2\_2\_is\_4</span> :\
   2 + 2 = 4.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

But they can be used in many other ways. For example, we have also seen
that we can give a name to a proposition using a <span
class="inlinecode"><span class="id"
type="keyword">Definition</span></span>, just as we have given names to
expressions of other sorts.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">plus\_fact</span> : <span class="id"
type="keyword">Prop</span> := 2 + 2 = 4.\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">plus\_fact</span>.\
 <span class="comment">(\* ===\> plus\_fact : Prop \*)</span>\
\

</div>

<div class="doc">

We can later use this name in any situation where a proposition is
expected — for example, as the claim in a <span class="inlinecode"><span
class="id" type="keyword">Theorem</span></span> declaration.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">plus\_fact\_is\_true</span> :\
   <span class="id" type="var">plus\_fact</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

We've seen several ways of constructing propositions.
<div class="paragraph">

</div>

-   We can define a new proposition primitively using <span
    class="inlinecode"><span class="id"
    type="keyword">Inductive</span></span>.
    <div class="paragraph">

    </div>

-   Given two expressions <span class="inlinecode"><span class="id"
    type="var">e1</span></span> and <span class="inlinecode"><span
    class="id" type="var">e2</span></span> of the same type, we can form
    the proposition <span class="inlinecode"><span class="id"
    type="var">e1</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">e2</span></span>,
    which states that their values are equal.
    <div class="paragraph">

    </div>

-   We can combine propositions using implication and quantification.

###  {.section}

We have also seen *parameterized propositions*, such as <span
class="inlinecode"><span class="id" type="var">even</span></span> and
<span class="inlinecode"><span class="id"
type="var">beautiful</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> (<span class="id"
type="var">even</span> 4).\
 <span class="comment">(\* ===\> even 4 : Prop \*)</span>\
 <span class="id" type="keyword">Check</span> (<span class="id"
type="var">even</span> 3).\
 <span class="comment">(\* ===\> even 3 : Prop \*)</span>\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">even</span>.\
 <span class="comment">(\* ===\> even : nat -\> Prop \*)</span>\
\

</div>

<div class="doc">

###  {.section}

The type of <span class="inlinecode"><span class="id"
type="var">even</span></span>, i.e., <span class="inlinecode"><span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span></span>, can be pronounced in three equivalent
ways: (1) "<span class="inlinecode"><span class="id"
type="var">even</span></span> is a *function* from numbers to
propositions," (2) "<span class="inlinecode"><span class="id"
type="var">even</span></span> is a *family* of propositions, indexed by
a number <span class="inlinecode"><span class="id"
type="var">n</span></span>," or (3) "<span class="inlinecode"><span
class="id" type="var">even</span></span> is a *property* of numbers."
<div class="paragraph">

</div>

Propositions — including parameterized propositions — are first-class
citizens in Coq. For example, we can define functions from numbers to
propositions...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">between</span> (<span class="id" type="var">n</span> <span
class="id" type="var">m</span> <span class="id" type="var">o</span>:
<span class="id" type="var">nat</span>) : <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">andb</span> (<span class="id"
type="var">ble\_nat</span> <span class="id" type="var">n</span> <span
class="id" type="var">o</span>) (<span class="id"
type="var">ble\_nat</span> <span class="id" type="var">o</span> <span
class="id" type="var">m</span>) = <span class="id"
type="var">true</span>.\
\

</div>

<div class="doc">

... and then partially apply them:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">teen</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span> := <span class="id" type="var">between</span>
13 19.\
\

</div>

<div class="doc">

We can even pass propositions — including parameterized propositions —
as arguments to functions:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">true\_for\_zero</span> (<span class="id"
type="var">P</span>:<span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>) : <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">P</span> 0.\
\

</div>

<div class="doc">

###  {.section}

Here are two more examples of passing parameterized propositions as
arguments to a function.
<div class="paragraph">

</div>

The first function, <span class="inlinecode"><span class="id"
type="var">true\_for\_all\_numbers</span></span>, takes a proposition
<span class="inlinecode"><span class="id" type="var">P</span></span> as
argument and builds the proposition that <span class="inlinecode"><span
class="id" type="var">P</span></span> is true for all natural numbers.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">true\_for\_all\_numbers</span> (<span class="id"
type="var">P</span>:<span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>) : <span class="id"
type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">P</span> <span
class="id" type="var">n</span>.\
\

</div>

<div class="doc">

The second, <span class="inlinecode"><span class="id"
type="var">preserved\_by\_S</span></span>, takes <span
class="inlinecode"><span class="id" type="var">P</span></span> and
builds the proposition that, if <span class="inlinecode"><span
class="id" type="var">P</span></span> is true for some natural number
<span class="inlinecode"><span class="id" type="var">n'</span></span>,
then it is also true by the successor of <span class="inlinecode"><span
class="id" type="var">n'</span></span> — i.e. that <span
class="inlinecode"><span class="id" type="var">P</span></span> is
*preserved by successor*:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">preserved\_by\_S</span> (<span class="id"
type="var">P</span>:<span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>) : <span class="id"
type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">n'</span>, <span class="id" type="var">P</span> <span
class="id" type="var">n'</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n'</span>).\
\

</div>

<div class="doc">

###  {.section}

Finally, we can put these ingredients together to define a proposition
stating that induction is valid for natural numbers:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">natural\_number\_induction\_valid</span> : <span class="id"
type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span>:<span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
     <span class="id" type="var">true\_for\_zero</span> <span class="id"
type="var">P</span> <span style="font-family: arial;">→</span>\
     <span class="id" type="var">preserved\_by\_S</span> <span
class="id" type="var">P</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">true\_for\_all\_numbers</span> <span
class="id" type="var">P</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars (combine\_odd\_even) {.section}

Complete the definition of the <span class="inlinecode"><span class="id"
type="var">combine\_odd\_even</span></span> function below. It takes as
arguments two properties of numbers <span class="inlinecode"><span
class="id" type="var">Podd</span></span> and <span
class="inlinecode"><span class="id" type="var">Peven</span></span>. As
its result, it should return a new property <span
class="inlinecode"><span class="id" type="var">P</span></span> such that
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span> is
equivalent to <span class="inlinecode"><span class="id"
type="var">Podd</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> when <span class="inlinecode"><span
class="id" type="var">n</span></span> is odd, and equivalent to <span
class="inlinecode"><span class="id" type="var">Peven</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span>
otherwise.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">combine\_odd\_even</span> (<span class="id"
type="var">Podd</span> <span class="id" type="var">Peven</span> : <span
class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>) : <span class="id" type="var">nat</span>
<span style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\

</div>

<div class="doc">

To test your definition, see whether you can prove the following facts:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">combine\_odd\_even\_intro</span> :\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">Podd</span> <span class="id" type="var">Peven</span> : <span
class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>) (<span class="id" type="var">n</span> :
<span class="id" type="var">nat</span>),\
     (<span class="id" type="var">oddb</span> <span class="id"
type="var">n</span> = <span class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Podd</span> <span class="id" type="var">n</span>) <span
style="font-family: arial;">→</span>\
     (<span class="id" type="var">oddb</span> <span class="id"
type="var">n</span> = <span class="id" type="var">false</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Peven</span> <span class="id" type="var">n</span>) <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">combine\_odd\_even</span> <span
class="id" type="var">Podd</span> <span class="id"
type="var">Peven</span> <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">combine\_odd\_even\_elim\_odd</span> :\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">Podd</span> <span class="id" type="var">Peven</span> : <span
class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>) (<span class="id" type="var">n</span> :
<span class="id" type="var">nat</span>),\
     <span class="id" type="var">combine\_odd\_even</span> <span
class="id" type="var">Podd</span> <span class="id"
type="var">Peven</span> <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">oddb</span> <span class="id"
type="var">n</span> = <span class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">Podd</span> <span class="id"
type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">combine\_odd\_even\_elim\_even</span> :\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">Podd</span> <span class="id" type="var">Peven</span> : <span
class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>) (<span class="id" type="var">n</span> :
<span class="id" type="var">nat</span>),\
     <span class="id" type="var">combine\_odd\_even</span> <span
class="id" type="var">Podd</span> <span class="id"
type="var">Peven</span> <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">oddb</span> <span class="id"
type="var">n</span> = <span class="id" type="var">false</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">Peven</span> <span class="id"
type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

One more quick digression, for adventurous souls: if we can define
parameterized propositions using <span class="inlinecode"><span
class="id" type="keyword">Definition</span></span>, then can we also
define them using <span class="inlinecode"><span class="id"
type="keyword">Fixpoint</span></span>? Of course we can! However, this
kind of "recursive parameterization" doesn't correspond to anything very
familiar from everyday mathematics. The following exercise gives a
slightly contrived example.
<div class="paragraph">

</div>

#### Exercise: 4 stars, optional (true\_upto\_n\_\_true\_everywhere) {.section}

Define a recursive function <span class="inlinecode"><span class="id"
type="var">true\_upto\_n\_\_true\_everywhere</span></span> that makes
<span class="inlinecode"><span class="id"
type="var">true\_upto\_n\_example</span></span> work.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* \
 Fixpoint true\_upto\_n\_\_true\_everywhere\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\
 Example true\_upto\_n\_example :\
     (true\_upto\_n\_\_true\_everywhere 3 (fun n =\> even n))\
   = (even 3 -\> even 2 -\> even 1 -\> forall m : nat, even m).\
 Proof. reflexivity.  Qed.\
 \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

</div>

<div class="code code-tight">

\

</div>

</div>

<div id="footer">

------------------------------------------------------------------------

[Index](http://www.cis.upenn.edu/~bcpierce/sf/current/coqindex.html)

</div>

</div>
