<div id="page">

<div id="header">

</div>

<div id="main">

Logic<span class="subtitle">Logic in Coq</span> {.libtitle}
===============================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id"
type="var">MoreCoq</span>.\
\

</div>

<div class="doc">

Coq's built-in logic is very small: the only primitives are <span
class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> definitions, universal
quantification (<span class="inlinecode"><span
style="font-family: arial;">∀</span></span>), and implication (<span
class="inlinecode"><span style="font-family: arial;">→</span></span>),
while all the other familiar logical connectives — conjunction,
disjunction, negation, existential quantification, even equality — can
be encoded using just these.
<div class="paragraph">

</div>

This chapter explains the encodings and shows how the tactics we've seen
can be used to carry out standard forms of logical reasoning involving
these connectives.
<div class="paragraph">

</div>

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Propositions {.section}
============

<div class="paragraph">

</div>

In previous chapters, we have seen many examples of factual claims
(*propositions*) and ways of presenting evidence of their truth
(*proofs*). In particular, we have worked extensively with *equality
propositions* of the form <span class="inlinecode"><span class="id"
type="var">e1</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">e2</span></span>, with
implications (<span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">Q</span></span>), and
with quantified propositions (<span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">x</span>,</span> <span
class="inlinecode"><span class="id" type="var">P</span></span>).
<div class="paragraph">

</div>

In Coq, the type of things that can (potentially) be proven is <span
class="inlinecode"><span class="id" type="keyword">Prop</span></span>.
<div class="paragraph">

</div>

Here is an example of a provable proposition:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> (3 = 3).\
 <span class="comment">(\* ===\> Prop \*)</span>\
\

</div>

<div class="doc">

Here is an example of an unprovable proposition:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> (<span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>), <span
class="id" type="var">n</span> = 2).\
 <span class="comment">(\* ===\> Prop \*)</span>\
\

</div>

<div class="doc">

Recall that <span class="inlinecode"><span class="id"
type="keyword">Check</span></span> asks Coq to tell us the type of the
indicated expression.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Proofs and Evidence {.section}
===================

<div class="paragraph">

</div>

In Coq, propositions have the same status as other types, such as <span
class="inlinecode"><span class="id" type="var">nat</span></span>. Just
as the natural numbers <span class="inlinecode">0</span>, <span
class="inlinecode">1</span>, <span class="inlinecode">2</span>, etc.
inhabit the type <span class="inlinecode"><span class="id"
type="var">nat</span></span>, a Coq proposition <span
class="inlinecode"><span class="id" type="var">P</span></span> is
inhabited by its *proofs*. We will refer to such inhabitants as *proof
term* or *proof object* or *evidence* for the truth of <span
class="inlinecode"><span class="id" type="var">P</span></span>.
<div class="paragraph">

</div>

In Coq, when we state and then prove a lemma such as:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">silly</span> : 0 × 3 = 0.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

the tactics we use within the <span class="inlinecode"><span class="id"
type="keyword">Proof</span></span>...<span class="inlinecode"><span
class="id" type="keyword">Qed</span></span> keywords tell Coq how to
construct a proof term that inhabits the proposition. In this case, the
proposition <span class="inlinecode">0</span> <span
class="inlinecode">×</span> <span class="inlinecode">3</span> <span
class="inlinecode">=</span> <span class="inlinecode">0</span> is
justified by a combination of the *definition* of <span
class="inlinecode"><span class="id" type="var">mult</span></span>, which
says that <span class="inlinecode">0</span> <span
class="inlinecode">×</span> <span class="inlinecode">3</span>
*simplifies* to just <span class="inlinecode">0</span>, and the
*reflexive* principle of equality, which says that <span
class="inlinecode">0</span> <span class="inlinecode">=</span> <span
class="inlinecode">0</span>.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

###  {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">silly</span> : 0 × 3 = 0.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

We can see which proof term Coq constructs for a given Lemma by using
the <span class="inlinecode"><span class="id"
type="keyword">Print</span></span> directive:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">silly</span>.\
 <span
class="comment">(\* ===\> silly = eq\_refl : 0 \* 3 = 0 \*)</span>\
\

</div>

<div class="doc">

Here, the <span class="inlinecode"><span class="id"
type="var">eq\_refl</span></span> proof term witnesses the equality.
(More on equality later!)
<div class="paragraph">

</div>

Implications *are* functions {.section}
----------------------------

<div class="paragraph">

</div>

Just as we can implement natural number multiplication as a function:
<div class="paragraph">

</div>

<span class="inlinecode"></span> <span class="inlinecode"><span
class="id" type="var">mult</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">nat</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">nat</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">nat</span></span>
<span class="inlinecode"></span>
<div class="paragraph">

</div>

The *proof term* for an implication <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">Q</span></span> is a
*function* that takes evidence for <span class="inlinecode"><span
class="id" type="var">P</span></span> as input and produces evidence for
<span class="inlinecode"><span class="id" type="var">Q</span></span> as
its output.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">silly\_implication</span> : (1 + 1) = 2 <span
style="font-family: arial;">→</span> 0 × 3 = 0.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

We can see that the proof term for the above lemma is indeed a function:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">silly\_implication</span>.\
 <span
class="comment">(\* ===\> silly\_implication = fun \_ : 1 + 1 = 2 =\> eq\_refl\
      : 1 + 1 = 2 -\> 0 \* 3 = 0 \*)</span>\
\

</div>

<div class="doc">

Defining propositions {.section}
---------------------

<div class="paragraph">

</div>

Just as we can create user-defined inductive types (like the lists,
binary representations of natural numbers, etc., that we seen before),
we can also create *user-defined* propositions.
<div class="paragraph">

</div>

Question: How do you define the meaning of a proposition?
<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

The meaning of a proposition is given by *rules* and *definitions* that
say how to construct *evidence* for the truth of the proposition from
other evidence.
<div class="paragraph">

</div>

-   Typically, rules are defined *inductively*, just like any other
    datatype.
    <div class="paragraph">

    </div>

-   Sometimes a proposition is declared to be true without
    substantiating evidence. Such propositions are called *axioms*.

In this, and subsequence chapters, we'll see more about how these proof
terms work in more detail.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Conjunction (Logical "and") {.section}
===========================

<div class="paragraph">

</div>

The logical conjunction of propositions <span class="inlinecode"><span
class="id" type="var">P</span></span> and <span class="inlinecode"><span
class="id" type="var">Q</span></span> can be represented using an <span
class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> definition with one constructor.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">and</span> (<span class="id" type="var">P</span> <span
class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>) : <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">conj</span> : <span class="id"
type="var">P</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span> <span
style="font-family: arial;">→</span> (<span class="id"
type="var">and</span> <span class="id" type="var">P</span> <span
class="id" type="var">Q</span>).\
\

</div>

<div class="doc">

The intuition behind this definition is simple: to construct evidence
for <span class="inlinecode"><span class="id"
type="var">and</span></span> <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode"><span class="id"
type="var">Q</span></span>, we must provide evidence for <span
class="inlinecode"><span class="id" type="var">P</span></span> and
evidence for <span class="inlinecode"><span class="id"
type="var">Q</span></span>. More precisely:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">conj</span></span> <span class="inlinecode"><span
    class="id" type="var">p</span></span> <span class="inlinecode"><span
    class="id" type="var">q</span></span> can be taken as evidence for
    <span class="inlinecode"><span class="id"
    type="var">and</span></span> <span class="inlinecode"><span
    class="id" type="var">P</span></span> <span class="inlinecode"><span
    class="id" type="var">Q</span></span> if <span
    class="inlinecode"><span class="id" type="var">p</span></span> is
    evidence for <span class="inlinecode"><span class="id"
    type="var">P</span></span> and <span class="inlinecode"><span
    class="id" type="var">q</span></span> is evidence for <span
    class="inlinecode"><span class="id" type="var">Q</span></span>; and
    <div class="paragraph">

    </div>

-   this is the *only* way to give evidence for <span
    class="inlinecode"><span class="id" type="var">and</span></span>
    <span class="inlinecode"><span class="id" type="var">P</span></span>
    <span class="inlinecode"><span class="id" type="var">Q</span></span>
    — that is, if someone gives us evidence for <span
    class="inlinecode"><span class="id" type="var">and</span></span>
    <span class="inlinecode"><span class="id" type="var">P</span></span>
    <span class="inlinecode"><span class="id"
    type="var">Q</span></span>, we know it must have the form <span
    class="inlinecode"><span class="id" type="var">conj</span></span>
    <span class="inlinecode"><span class="id" type="var">p</span></span>
    <span class="inlinecode"><span class="id"
    type="var">q</span></span>, where <span class="inlinecode"><span
    class="id" type="var">p</span></span> is evidence for <span
    class="inlinecode"><span class="id" type="var">P</span></span> and
    <span class="inlinecode"><span class="id" type="var">q</span></span>
    is evidence for <span class="inlinecode"><span class="id"
    type="var">Q</span></span>.

<div class="paragraph">

</div>

Since we'll be using conjunction a lot, let's introduce a more
familiar-looking infix notation for it.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "P <span
style="font-family: arial;">∧</span> Q" := (<span class="id"
type="var">and</span> <span class="id" type="var">P</span> <span
class="id" type="var">Q</span>) : <span class="id"
type="var">type\_scope</span>.\
\

</div>

<div class="doc">

(The <span class="inlinecode"><span class="id"
type="var">type\_scope</span></span> annotation tells Coq that this
notation will be appearing in propositions, not values.)
<div class="paragraph">

</div>

Consider the "type" of the constructor <span class="inlinecode"><span
class="id" type="var">conj</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">conj</span>.\
 <span
class="comment">(\* ===\>  forall P Q : Prop, P -\> Q -\> P /\\ Q \*)</span>\
\

</div>

<div class="doc">

Notice that it takes 4 inputs — namely the propositions <span
class="inlinecode"><span class="id" type="var">P</span></span> and <span
class="inlinecode"><span class="id" type="var">Q</span></span> and
evidence for <span class="inlinecode"><span class="id"
type="var">P</span></span> and <span class="inlinecode"><span class="id"
type="var">Q</span></span> — and returns as output the evidence of <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span style="font-family: arial;">∧</span></span>
<span class="inlinecode"><span class="id" type="var">Q</span></span>.
<div class="paragraph">

</div>

"Introducing" conjunctions {.section}
--------------------------

Besides the elegance of building everything up from a tiny foundation,
what's nice about defining conjunction this way is that we can prove
statements involving conjunction using the tactics that we already know.
For example, if the goal statement is a conjuction, we can prove it by
applying the single constructor <span class="inlinecode"><span
class="id" type="var">conj</span></span>, which (as can be seen from the
type of <span class="inlinecode"><span class="id"
type="var">conj</span></span>) solves the current goal and leaves the
two parts of the conjunction as subgoals to be proved separately.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">and\_example</span> :\
   (0 = 0) <span style="font-family: arial;">∧</span> (4 = <span
class="id" type="var">mult</span> 2 2).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">conj</span>.\
   <span class="id" type="var">Case</span> "left". <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "right". <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Just for convenience, we can use the tactic <span
class="inlinecode"><span class="id" type="tactic">split</span></span> as
a shorthand for <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">conj</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">and\_example'</span> :\
   (0 = 0) <span style="font-family: arial;">∧</span> (4 = <span
class="id" type="var">mult</span> 2 2).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">split</span>.\
     <span class="id" type="var">Case</span> "left". <span class="id"
type="tactic">reflexivity</span>.\
     <span class="id" type="var">Case</span> "right". <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

"Eliminating" conjunctions {.section}
--------------------------

Conversely, the <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> tactic can be used to take a
conjunction hypothesis in the context, calculate what evidence must have
been used to build it, and add variables representing this evidence to
the proof context.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">proj1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>,\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">HP</span> <span class="id" type="var">HQ</span>].\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">HP</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star, optional (proj2) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">proj2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>,\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">and\_commut</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>,\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">HP</span> <span class="id" type="var">HQ</span>].\
   <span class="id" type="tactic">split</span>.\
     <span class="id" type="var">Case</span> "left". <span class="id"
type="tactic">apply</span> <span class="id" type="var">HQ</span>.\
     <span class="id" type="var">Case</span> "right". <span class="id"
type="tactic">apply</span> <span class="id" type="var">HP</span>. <span
class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (and\_assoc) {.section}

In the following proof, notice how the *nested pattern* in the <span
class="inlinecode"><span class="id" type="tactic">destruct</span></span>
breaks the hypothesis <span class="inlinecode"><span class="id"
type="var">H</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span style="font-family: arial;">∧</span></span>
<span class="inlinecode">(<span class="id" type="var">Q</span></span>
<span class="inlinecode"><span
style="font-family: arial;">∧</span></span> <span
class="inlinecode"><span class="id" type="var">R</span>)</span> down
into <span class="inlinecode"><span class="id"
type="var">HP</span>:</span> <span class="inlinecode"><span class="id"
type="var">P</span></span>, <span class="inlinecode"><span class="id"
type="var">HQ</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">Q</span></span>, and
<span class="inlinecode"><span class="id" type="var">HR</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">R</span></span>. Finish the proof from there:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">and\_assoc</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> <span class="id"
type="var">R</span> : <span class="id" type="keyword">Prop</span>,\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> (<span class="id"
type="var">Q</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">R</span>) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">P</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">Q</span>) <span
style="font-family: arial;">∧</span> <span class="id"
type="var">R</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">R</span> <span class="id" type="var">H</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">HP</span> [<span class="id" type="var">HQ</span>
<span class="id" type="var">HR</span>]].\
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

Iff {.section}
===

<div class="paragraph">

</div>

The handy "if and only if" connective is just the conjunction of two
implications.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">iff</span> (<span class="id" type="var">P</span> <span
class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>) := (<span class="id" type="var">P</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">Q</span>) <span style="font-family: arial;">∧</span> (<span
class="id" type="var">Q</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span>).\
\
 <span class="id" type="keyword">Notation</span> "P <span
style="font-family: arial;">↔</span> Q" := (<span class="id"
type="var">iff</span> <span class="id" type="var">P</span> <span
class="id" type="var">Q</span>)\
                       (<span class="id" type="tactic">at</span> <span
class="id" type="var">level</span> 95, <span class="id"
type="var">no</span> <span class="id" type="var">associativity</span>)\
                       : <span class="id"
type="var">type\_scope</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">iff\_implies</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>,\
   (<span class="id" type="var">P</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">Q</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">HAB</span> <span class="id"
type="var">HBA</span>]. <span class="id" type="tactic">apply</span>
<span class="id" type="var">HAB</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">iff\_sym</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>,\
   (<span class="id" type="var">P</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">Q</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">Q</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">P</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">HAB</span> <span class="id"
type="var">HBA</span>].\
   <span class="id" type="tactic">split</span>.\
     <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>". <span class="id"
type="tactic">apply</span> <span class="id" type="var">HBA</span>.\
     <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>". <span class="id"
type="tactic">apply</span> <span class="id" type="var">HAB</span>. <span
class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star, optional (iff\_properties) {.section}

Using the above proof that <span class="inlinecode"><span
style="font-family: arial;">↔</span></span> is symmetric (<span
class="inlinecode"><span class="id" type="var">iff\_sym</span></span>)
as a guide, prove that it is also reflexive and transitive.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">iff\_refl</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
: <span class="id" type="keyword">Prop</span>,\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">iff\_trans</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> <span class="id"
type="var">R</span> : <span class="id" type="keyword">Prop</span>,\
   (<span class="id" type="var">P</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">Q</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">Q</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">P</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">R</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Hint: If you have an iff hypothesis in the context, you can use <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span> to break it into two separate
implications. (Think about why this works.) ☐
<div class="paragraph">

</div>

Some of Coq's tactics treat <span class="inlinecode"><span class="id"
type="var">iff</span></span> statements specially, thus avoiding the
need for some low-level manipulation when reasoning with them. In
particular, <span class="inlinecode"><span class="id"
type="tactic">rewrite</span></span> can be used with <span
class="inlinecode"><span class="id" type="var">iff</span></span>
statements, not just equalities.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Disjunction (Logical "or") {.section}
==========================

<div class="paragraph">

</div>

Implementing disjunction {.section}
------------------------

<div class="paragraph">

</div>

Disjunction ("logical or") can also be defined as an inductive
proposition.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">or</span> (<span class="id" type="var">P</span> <span
class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>) : <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">or\_introl</span> : <span class="id"
type="var">P</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">or</span> <span class="id" type="var">P</span>
<span class="id" type="var">Q</span>\
   | <span class="id" type="var">or\_intror</span> : <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">or</span> <span class="id" type="var">P</span>
<span class="id" type="var">Q</span>.\
\
 <span class="id" type="keyword">Notation</span> "P <span
style="font-family: arial;">∨</span> Q" := (<span class="id"
type="var">or</span> <span class="id" type="var">P</span> <span
class="id" type="var">Q</span>) : <span class="id"
type="var">type\_scope</span>.\
\

</div>

<div class="doc">

Consider the "type" of the constructor <span class="inlinecode"><span
class="id" type="var">or\_introl</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">or\_introl</span>.\
 <span
class="comment">(\* ===\>  forall P Q : Prop, P -\> P \\/ Q \*)</span>\
\

</div>

<div class="doc">

It takes 3 inputs, namely the propositions <span
class="inlinecode"><span class="id" type="var">P</span></span>, <span
class="inlinecode"><span class="id" type="var">Q</span></span> and
evidence of <span class="inlinecode"><span class="id"
type="var">P</span></span>, and returns, as output, the evidence of
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span
style="font-family: arial;">∨</span></span> <span
class="inlinecode"><span class="id" type="var">Q</span></span>. Next,
look at the type of <span class="inlinecode"><span class="id"
type="var">or\_intror</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">or\_intror</span>.\
 <span
class="comment">(\* ===\>  forall P Q : Prop, Q -\> P \\/ Q \*)</span>\
\

</div>

<div class="doc">

It is like <span class="inlinecode"><span class="id"
type="var">or\_introl</span></span> but it requires evidence of <span
class="inlinecode"><span class="id" type="var">Q</span></span> instead
of evidence of <span class="inlinecode"><span class="id"
type="var">P</span></span>.
<div class="paragraph">

</div>

Intuitively, there are two ways of giving evidence for <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span style="font-family: arial;">∨</span></span>
<span class="inlinecode"><span class="id" type="var">Q</span></span>:
<div class="paragraph">

</div>

-   give evidence for <span class="inlinecode"><span class="id"
    type="var">P</span></span> (and say that it is <span
    class="inlinecode"><span class="id" type="var">P</span></span> you
    are giving evidence for — this is the function of the <span
    class="inlinecode"><span class="id"
    type="var">or\_introl</span></span> constructor), or
    <div class="paragraph">

    </div>

-   give evidence for <span class="inlinecode"><span class="id"
    type="var">Q</span></span>, tagged with the <span
    class="inlinecode"><span class="id"
    type="var">or\_intror</span></span> constructor.

<div class="paragraph">

</div>

###  {.section}

Since <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode"><span
style="font-family: arial;">∨</span></span> <span
class="inlinecode"><span class="id" type="var">Q</span></span> has two
constructors, doing <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> on a hypothesis of type <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span style="font-family: arial;">∨</span></span>
<span class="inlinecode"><span class="id" type="var">Q</span></span>
yields two subgoals.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">or\_commut</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>,\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">HP</span> | <span class="id"
type="var">HQ</span>].\
     <span class="id" type="var">Case</span> "left". <span class="id"
type="tactic">apply</span> <span class="id"
type="var">or\_intror</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">HP</span>.\
     <span class="id" type="var">Case</span> "right". <span class="id"
type="tactic">apply</span> <span class="id"
type="var">or\_introl</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">HQ</span>. <span
class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

From here on, we'll use the shorthand tactics <span
class="inlinecode"><span class="id" type="var">left</span></span> and
<span class="inlinecode"><span class="id" type="var">right</span></span>
in place of <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">or\_introl</span></span> and <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
<span class="inlinecode"><span class="id"
type="var">or\_intror</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">or\_commut'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>,\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">HP</span> | <span class="id"
type="var">HQ</span>].\
     <span class="id" type="var">Case</span> "left". <span class="id"
type="var">right</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">HP</span>.\
     <span class="id" type="var">Case</span> "right". <span class="id"
type="var">left</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">HQ</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">or\_distributes\_over\_and\_1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> <span class="id"
type="var">R</span> : <span class="id" type="keyword">Prop</span>,\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> (<span class="id"
type="var">Q</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">R</span>) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">P</span> <span style="font-family: arial;">∨</span> <span
class="id" type="var">Q</span>) <span
style="font-family: arial;">∧</span> (<span class="id"
type="var">P</span> <span style="font-family: arial;">∨</span> <span
class="id" type="var">R</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">R</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">HP</span> | [<span class="id" type="var">HQ</span>
<span class="id" type="var">HR</span>]].\
     <span class="id" type="var">Case</span> "left". <span class="id"
type="tactic">split</span>.\
       <span class="id" type="var">SCase</span> "left". <span class="id"
type="var">left</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">HP</span>.\
       <span class="id" type="var">SCase</span> "right". <span
class="id" type="var">left</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">HP</span>.\
     <span class="id" type="var">Case</span> "right". <span class="id"
type="tactic">split</span>.\
       <span class="id" type="var">SCase</span> "left". <span class="id"
type="var">right</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">HQ</span>.\
       <span class="id" type="var">SCase</span> "right". <span
class="id" type="var">right</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">HR</span>. <span
class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (or\_distributes\_over\_and\_2) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">or\_distributes\_over\_and\_2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> <span class="id"
type="var">R</span> : <span class="id" type="keyword">Prop</span>,\
   (<span class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">Q</span>) <span style="font-family: arial;">∧</span> (<span
class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> (<span class="id"
type="var">Q</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">R</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (or\_distributes\_over\_and) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">or\_distributes\_over\_and</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> <span class="id"
type="var">R</span> : <span class="id" type="keyword">Prop</span>,\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> (<span class="id"
type="var">Q</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">R</span>) <span
style="font-family: arial;">↔</span> (<span class="id"
type="var">P</span> <span style="font-family: arial;">∨</span> <span
class="id" type="var">Q</span>) <span
style="font-family: arial;">∧</span> (<span class="id"
type="var">P</span> <span style="font-family: arial;">∨</span> <span
class="id" type="var">R</span>).\
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

Relating <span class="inlinecode"><span style="font-family: arial;">∧</span></span> and <span class="inlinecode"><span style="font-family: arial;">∨</span></span> with <span class="inlinecode"><span class="id" type="var">andb</span></span> and <span class="inlinecode"><span class="id" type="var">orb</span></span> {.section}
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

<div class="paragraph">

</div>

We've already seen several places where analogous structures can be
found in Coq's computational (<span class="inlinecode"><span class="id"
type="keyword">Type</span></span>) and logical (<span
class="inlinecode"><span class="id" type="keyword">Prop</span></span>)
worlds. Here is one more: the boolean operators <span
class="inlinecode"><span class="id" type="var">andb</span></span> and
<span class="inlinecode"><span class="id" type="var">orb</span></span>
are clearly analogs of the logical connectives <span
class="inlinecode"><span style="font-family: arial;">∧</span></span> and
<span class="inlinecode"><span
style="font-family: arial;">∨</span></span>. This analogy can be made
more precise by the following theorems, which show how to translate
knowledge about <span class="inlinecode"><span class="id"
type="var">andb</span></span> and <span class="inlinecode"><span
class="id" type="var">orb</span></span>'s behaviors on certain inputs
into propositional facts about those inputs.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">andb\_prop</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span>,\
   <span class="id" type="var">andb</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">b</span> = <span class="id" type="var">true</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">c</span> = <span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">b</span>.\
     <span class="id" type="var">Case</span> "b = true". <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">c</span>.\
       <span class="id" type="var">SCase</span> "c = true". <span
class="id" type="tactic">apply</span> <span class="id"
type="var">conj</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="tactic">reflexivity</span>.\
       <span class="id" type="var">SCase</span> "c = false". <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>.\
     <span class="id" type="var">Case</span> "b = false". <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>. <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">andb\_true\_intro</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span>,\
   <span class="id" type="var">b</span> = <span class="id"
type="var">true</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">c</span> = <span class="id" type="var">true</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">andb</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span> = <span class="id"
type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">rewrite</span> <span
class="id" type="var">H0</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (andb\_false) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">andb\_false</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span>,\
   <span class="id" type="var">andb</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">b</span> = <span class="id" type="var">false</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">c</span> = <span class="id" type="var">false</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (orb\_false) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">orb\_prop</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span>,\
   <span class="id" type="var">orb</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">b</span> = <span class="id" type="var">true</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">c</span> = <span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (orb\_false\_elim) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">orb\_false\_elim</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span>,\
   <span class="id" type="var">orb</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">b</span> = <span class="id" type="var">false</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">c</span> = <span class="id" type="var">false</span>.\
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

Falsehood {.section}
=========

<div class="paragraph">

</div>

Logical falsehood can be represented in Coq as an inductively defined
proposition with no constructors.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">False</span> : <span class="id" type="keyword">Prop</span> :=
.\
\

</div>

<div class="doc">

Intuition: <span class="inlinecode"><span class="id"
type="var">False</span></span> is a proposition for which there is no
way to give evidence.
<div class="paragraph">

</div>

Since <span class="inlinecode"><span class="id"
type="var">False</span></span> has no constructors, inverting an
assumption of type <span class="inlinecode"><span class="id"
type="var">False</span></span> always yields zero subgoals, allowing us
to immediately prove any goal.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">False\_implies\_nonsense</span> :\
   <span class="id" type="var">False</span> <span
style="font-family: arial;">→</span> 2 + 2 = 5.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">contra</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">contra</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

How does this work? The <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> tactic breaks <span
class="inlinecode"><span class="id" type="var">contra</span></span> into
each of its possible cases, and yields a subgoal for each case. As <span
class="inlinecode"><span class="id" type="var">contra</span></span> is
evidence for <span class="inlinecode"><span class="id"
type="var">False</span></span>, it has *no* possible cases, hence, there
are no possible subgoals and the proof is done.
<div class="paragraph">

</div>

###  {.section}

Conversely, the only way to prove <span class="inlinecode"><span
class="id" type="var">False</span></span> is if there is already
something nonsensical or contradictory in the context:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">nonsense\_implies\_False</span> :\
   2 + 2 = 5 <span style="font-family: arial;">→</span> <span class="id"
type="var">False</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">contra</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">contra</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Actually, since the proof of <span class="inlinecode"><span class="id"
type="var">False\_implies\_nonsense</span></span> doesn't actually have
anything to do with the specific nonsensical thing being proved; it can
easily be generalized to work for an arbitrary <span
class="inlinecode"><span class="id" type="var">P</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ex\_falso\_quodlibet</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span>:<span class="id" type="keyword">Prop</span>),\
   <span class="id" type="var">False</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">contra</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">contra</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The Latin *ex falso quodlibet* means, literally, "from falsehood follows
whatever you please." This theorem is also known as the *principle of
explosion*.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Truth {.section}
-----

<div class="paragraph">

</div>

Since we have defined falsehood in Coq, one might wonder whether it is
possible to define truth in the same way. We can.
<div class="paragraph">

</div>

#### Exercise: 2 stars, advanced (True) {.section}

Define <span class="inlinecode"><span class="id"
type="var">True</span></span> as another inductively defined
proposition. (The intution is that <span class="inlinecode"><span
class="id" type="var">True</span></span> should be a proposition for
which it is trivial to give evidence.)

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

However, unlike <span class="inlinecode"><span class="id"
type="var">False</span></span>, which we'll use extensively, <span
class="inlinecode"><span class="id" type="var">True</span></span> is
used fairly rarely. By itself, it is trivial (and therefore
uninteresting) to prove as a goal, and it carries no useful information
as a hypothesis. But it can be useful when defining complex <span
class="inlinecode"><span class="id" type="keyword">Prop</span></span>s
using conditionals, or as a parameter to higher-order <span
class="inlinecode"><span class="id" type="keyword">Prop</span></span>s.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Negation {.section}
========

<div class="paragraph">

</div>

The logical complement of a proposition <span class="inlinecode"><span
class="id" type="var">P</span></span> is written <span
class="inlinecode"><span class="id" type="var">not</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span> or, for
shorthand, <span class="inlinecode">¬<span class="id"
type="var">P</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">not</span> (<span class="id" type="var">P</span>:<span
class="id" type="keyword">Prop</span>) := <span class="id"
type="var">P</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">False</span>.\
\

</div>

<div class="doc">

The intuition is that, if <span class="inlinecode"><span class="id"
type="var">P</span></span> is not true, then anything at all (even <span
class="inlinecode"><span class="id" type="var">False</span></span>)
follows from assuming <span class="inlinecode"><span class="id"
type="var">P</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "¬ x" := (<span
class="id" type="var">not</span> <span class="id" type="var">x</span>) :
<span class="id" type="var">type\_scope</span>.\
\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">not</span>.\
 <span class="comment">(\* ===\> Prop -\> Prop \*)</span>\
\

</div>

<div class="doc">

It takes a little practice to get used to working with negation in Coq.
Even though you can see perfectly well why something is true, it can be
a little hard at first to get things into the right configuration so
that Coq can see it! Here are proofs of a few familiar facts about
negation to get you warmed up.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">not\_False</span> :\
   ¬ <span class="id" type="var">False</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">not</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">H</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>.
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">contradiction\_implies\_anything</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>,\
   (<span class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> ¬<span class="id"
type="var">P</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">H</span> <span
class="id" type="keyword">as</span> [<span class="id"
type="var">HP</span> <span class="id" type="var">HNA</span>]. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">not</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">HNA</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">HNA</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">HP</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">HP</span>.
<span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">double\_neg</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
: <span class="id" type="keyword">Prop</span>,\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">→</span> \~\~<span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">not</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">G</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">G</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">H</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, advanced (double\_neg\_inf) {.section}

Write an informal proof of <span class="inlinecode"><span class="id"
type="var">double\_neg</span></span>:
<div class="paragraph">

</div>

*Theorem*: <span class="inlinecode"><span class="id"
type="var">P</span></span> implies <span class="inlinecode">\~\~<span
class="id" type="var">P</span></span>, for any proposition <span
class="inlinecode"><span class="id" type="var">P</span></span>.
<div class="paragraph">

</div>

*Proof*: <span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (contrapositive) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">contrapositive</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>,\
   (<span class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span>) <span style="font-family: arial;">→</span> (¬<span
class="id" type="var">Q</span> <span
style="font-family: arial;">→</span> ¬<span class="id"
type="var">P</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star (not\_both\_true\_and\_false) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">not\_both\_true\_and\_false</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
: <span class="id" type="keyword">Prop</span>,\
   ¬ (<span class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> ¬<span class="id"
type="var">P</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, advanced (informal\_not\_PNP) {.section}

Write an informal proof (in English) of the proposition <span
class="inlinecode"><span style="font-family: arial;">∀</span></span>
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="keyword">Prop</span>,</span> <span
class="inlinecode">\~(<span class="id" type="var">P</span></span> <span
class="inlinecode"><span style="font-family: arial;">∧</span></span>
<span class="inlinecode">¬<span class="id" type="var">P</span>)</span>.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

### Constructive logic {.section}

Note that some theorems that are true in classical logic are *not*
provable in Coq's (constructive) logic. E.g., let's look at how this
proof gets stuck...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">classic\_double\_neg</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
: <span class="id" type="keyword">Prop</span>,\
   \~\~<span class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">not</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H</span>.\
   <span
class="comment">(\* But now what? There is no way to "invent" evidence for <span
class="inlinecode">¬<span class="id" type="var">P</span></span> \
      from evidence for <span class="inlinecode"><span class="id"
type="var">P</span></span>. \*)</span>\
   <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

#### Exercise: 5 stars, advanced, optional (classical\_axioms) {.section}

For those who like a challenge, here is an exercise taken from the
Coq'Art book (p. 123). The following five statements are often
considered as characterizations of classical logic (as opposed to
constructive logic, which is what is "built in" to Coq). We can't prove
them in Coq, but we can consistently add any one of them as an unproven
axiom if we wish to work in classical logic. Prove that these five
propositions are equivalent.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">peirce</span> := <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span>: <span class="id"
type="keyword">Prop</span>,\
   ((<span class="id" type="var">P</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Q</span>)<span style="font-family: arial;">→</span><span
class="id" type="var">P</span>)<span
style="font-family: arial;">→</span><span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">classic</span> := <span
style="font-family: arial;">∀</span><span class="id"
type="var">P</span>:<span class="id" type="keyword">Prop</span>,\
   \~\~<span class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">excluded\_middle</span> := <span
style="font-family: arial;">∀</span><span class="id"
type="var">P</span>:<span class="id" type="keyword">Prop</span>,\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> ¬<span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">de\_morgan\_not\_and\_not</span> := <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span>:<span class="id"
type="keyword">Prop</span>,\
   \~(\~<span class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> ¬<span class="id"
type="var">Q</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span><span
style="font-family: arial;">∨</span><span class="id"
type="var">Q</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">implies\_to\_or</span> := <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span>:<span class="id"
type="keyword">Prop</span>,\
   (<span class="id" type="var">P</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Q</span>) <span style="font-family: arial;">→</span> (¬<span
class="id" type="var">P</span><span
style="font-family: arial;">∨</span><span class="id"
type="var">Q</span>).\
\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (excluded\_middle\_irrefutable) {.section}

This theorem implies that it is always safe to add a decidability axiom
(i.e. an instance of excluded middle) for any *particular* Prop <span
class="inlinecode"><span class="id" type="var">P</span></span>. Why?
Because we cannot prove the negation of such an axiom; if we could, we
would have both <span class="inlinecode">¬</span> <span
class="inlinecode">(<span class="id" type="var">P</span></span> <span
class="inlinecode"><span style="font-family: arial;">∨</span></span>
<span class="inlinecode">¬<span class="id" type="var">P</span>)</span>
and <span class="inlinecode">¬</span> <span class="inlinecode">¬</span>
<span class="inlinecode">(<span class="id" type="var">P</span></span>
<span class="inlinecode"><span
style="font-family: arial;">∨</span></span> <span
class="inlinecode">¬<span class="id" type="var">P</span>)</span>, a
contradiction.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">excluded\_middle\_irrefutable</span>: <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span>:<span class="id" type="keyword">Prop</span>), ¬ ¬
(<span class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> ¬ <span class="id"
type="var">P</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Inequality {.section}
----------

<div class="paragraph">

</div>

Saying <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode">≠</span> <span
class="inlinecode"><span class="id" type="var">y</span></span> is just
the same as saying <span class="inlinecode">\~(<span class="id"
type="var">x</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">y</span>)</span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "x ≠ y" := (¬ (<span
class="id" type="var">x</span> = <span class="id" type="var">y</span>))
: <span class="id" type="var">type\_scope</span>.\
\

</div>

<div class="doc">

Since inequality involves a negation, it again requires a little
practice to be able to work with it fluently. Here is one very useful
trick. If you are trying to prove a goal that is nonsensical (e.g., the
goal state is <span class="inlinecode"><span class="id"
type="var">false</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">true</span></span>),
apply the lemma <span class="inlinecode"><span class="id"
type="var">ex\_falso\_quodlibet</span></span> to change the goal to
<span class="inlinecode"><span class="id"
type="var">False</span></span>. This makes it easier to use assumptions
of the form <span class="inlinecode">¬<span class="id"
type="var">P</span></span> that are available in the context — in
particular, assumptions of the form <span class="inlinecode"><span
class="id" type="var">x</span>≠<span class="id"
type="var">y</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">not\_false\_then\_true</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
: <span class="id" type="var">bool</span>,\
   <span class="id" type="var">b</span> ≠ <span class="id"
type="var">false</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">b</span> = <span class="id"
type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">b</span>.\
   <span class="id" type="var">Case</span> "b = true". <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "b = false".\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">not</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ex\_falso\_quodlibet</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">reflexivity</span>.
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

#### Exercise: 2 stars (false\_beq\_nat) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">false\_beq\_nat</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> : <span class="id"
type="var">nat</span>,\
      <span class="id" type="var">n</span> ≠ <span class="id"
type="var">m</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">false</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (beq\_nat\_false) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">beq\_nat\_false</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> ≠ <span class="id" type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

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
