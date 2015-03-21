<div id="page">

<div id="header">

</div>

<div id="main">

MoreLogic<span class="subtitle">More on Logic in Coq</span> {.libtitle}
===========================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> "Prop".\
\

</div>

<div class="doc">

Existential Quantification {.section}
==========================

<div class="paragraph">

</div>

Another critical logical connective is *existential quantification*. We
can express it with the following definition:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ex</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) (<span class="id"
type="var">P</span> : <span class="id" type="var">X</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>) : <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">ex\_intro</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">witness</span>:<span class="id" type="var">X</span>), <span
class="id" type="var">P</span> <span class="id"
type="var">witness</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">ex</span> <span class="id"
type="var">X</span> <span class="id" type="var">P</span>.\
\

</div>

<div class="doc">

That is, <span class="inlinecode"><span class="id"
type="var">ex</span></span> is a family of propositions indexed by a
type <span class="inlinecode"><span class="id"
type="var">X</span></span> and a property <span class="inlinecode"><span
class="id" type="var">P</span></span> over <span
class="inlinecode"><span class="id" type="var">X</span></span>. In order
to give evidence for the assertion "there exists an <span
class="inlinecode"><span class="id" type="var">x</span></span> for which
the property <span class="inlinecode"><span class="id"
type="var">P</span></span> holds" we must actually name a *witness* — a
specific value <span class="inlinecode"><span class="id"
type="var">x</span></span> — and then give evidence for <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span>, i.e.,
evidence that <span class="inlinecode"><span class="id"
type="var">x</span></span> has the property <span
class="inlinecode"><span class="id" type="var">P</span></span>.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

###  {.section}

Coq's <span class="inlinecode"><span class="id"
type="keyword">Notation</span></span> facility can be used to introduce
more familiar notation for writing existentially quantified
propositions, exactly parallel to the built-in syntax for universally
quantified propositions. Instead of writing <span
class="inlinecode"><span class="id" type="var">ex</span></span> <span
class="inlinecode"><span class="id" type="var">nat</span></span> <span
class="inlinecode"><span class="id" type="var">ev</span></span> to
express the proposition that there exists some number that is even, for
example, we can write <span class="inlinecode"><span
style="font-family: arial;">∃</span></span> <span
class="inlinecode"><span class="id" type="var">x</span>:<span class="id"
type="var">nat</span>,</span> <span class="inlinecode"><span class="id"
type="var">ev</span></span> <span class="inlinecode"><span class="id"
type="var">x</span></span>. (It is not necessary to understand exactly
how the <span class="inlinecode"><span class="id"
type="keyword">Notation</span></span> definition works.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "'exists' x , p" :=
(<span class="id" type="var">ex</span> <span class="id"
type="var">\_</span> (<span class="id" type="keyword">fun</span> <span
class="id" type="var">x</span> ⇒ <span class="id" type="var">p</span>))\
   (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 200, <span class="id" type="var">x</span> <span
class="id" type="var">ident</span>, <span class="id"
type="var">right</span> <span class="id"
type="var">associativity</span>) : <span class="id"
type="var">type\_scope</span>.\
 <span class="id" type="keyword">Notation</span> "'exists' x : X , p" :=
(<span class="id" type="var">ex</span> <span class="id"
type="var">\_</span> (<span class="id" type="keyword">fun</span> <span
class="id" type="var">x</span>:<span class="id" type="var">X</span> ⇒
<span class="id" type="var">p</span>))\
   (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 200, <span class="id" type="var">x</span> <span
class="id" type="var">ident</span>, <span class="id"
type="var">right</span> <span class="id"
type="var">associativity</span>) : <span class="id"
type="var">type\_scope</span>.\
\

</div>

<div class="doc">

###  {.section}

We can use the usual set of tactics for manipulating existentials. For
example, to prove an existential, we can <span class="inlinecode"><span
class="id" type="tactic">apply</span></span> the constructor <span
class="inlinecode"><span class="id" type="var">ex\_intro</span></span>.
Since the premise of <span class="inlinecode"><span class="id"
type="var">ex\_intro</span></span> involves a variable (<span
class="inlinecode"><span class="id" type="var">witness</span></span>)
that does not appear in its conclusion, we need to explicitly give its
value when we use <span class="inlinecode"><span class="id"
type="tactic">apply</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">exists\_example\_1</span> : <span
style="font-family: arial;">∃</span><span class="id"
type="var">n</span>, <span class="id" type="var">n</span> + (<span
class="id" type="var">n</span> × <span class="id" type="var">n</span>) =
6.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ex\_intro</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">witness</span>:=2).\
   <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Note that we have to explicitly give the witness.
<div class="paragraph">

</div>

###  {.section}

Or, instead of writing <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">ex\_intro</span></span> <span
class="inlinecode"><span class="id" type="keyword">with</span></span>
<span class="inlinecode">(<span class="id"
type="var">witness</span>:=<span class="id" type="var">e</span>)</span>
all the time, we can use the convenient shorthand <span
class="inlinecode"><span style="font-family: arial;">∃</span></span>
<span class="inlinecode"><span class="id" type="var">e</span></span>,
which means the same thing.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">exists\_example\_1'</span> : <span
style="font-family: arial;">∃</span><span class="id"
type="var">n</span>, <span class="id" type="var">n</span> + (<span
class="id" type="var">n</span> × <span class="id" type="var">n</span>) =
6.\
 <span class="id" type="keyword">Proof</span>.\
   <span style="font-family: arial;">∃</span>2.\
   <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

Conversely, if we have an existential hypothesis in the context, we can
eliminate it with <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span>. Note the use of the <span
class="inlinecode"><span class="id" type="keyword">as</span>...</span>
pattern to name the variable that Coq introduces to name the witness
value and get evidence that the hypothesis holds for the witness. (If we
don't explicitly choose one, Coq will just call it <span
class="inlinecode"><span class="id" type="var">witness</span></span>,
which makes proofs confusing.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">exists\_example\_2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
   (<span style="font-family: arial;">∃</span><span class="id"
type="var">m</span>, <span class="id" type="var">n</span> = 4 + <span
class="id" type="var">m</span>) <span
style="font-family: arial;">→</span>\
   (<span style="font-family: arial;">∃</span><span class="id"
type="var">o</span>, <span class="id" type="var">n</span> = 2 + <span
class="id" type="var">o</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">H</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">m</span> <span class="id" type="var">Hm</span>].\
   <span style="font-family: arial;">∃</span>(2 + <span class="id"
type="var">m</span>).\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">Hm</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Here is another example of how to work with existentials.

</div>

<div class="code code-tight">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">exists\_example\_3</span> :\
   <span style="font-family: arial;">∃</span>(<span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>), <span
class="id" type="var">even</span> <span class="id" type="var">n</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">beautiful</span> <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span style="font-family: arial;">∃</span>8.\
   <span class="id" type="tactic">split</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">even</span>. <span class="id" type="tactic">simpl</span>.
<span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_sum</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">n</span>:=3) (<span class="id"
type="var">m</span>:=5).\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_3</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">b\_5</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star, optional (english\_exists) {.section}

In English, what does the proposition
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">ex</span> <span class="id"
type="var">nat</span> (<span class="id" type="keyword">fun</span> <span
class="id" type="var">n</span> ⇒ <span class="id"
type="var">beautiful</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>))
<div class="paragraph">

</div>

</div>

mean?

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\
 <span class="comment">(\*\
 \*)</span>\

</div>

<div class="doc">

#### Exercise: 1 star (dist\_not\_exists) {.section}

Prove that "<span class="inlinecode"><span class="id"
type="var">P</span></span> holds for all <span class="inlinecode"><span
class="id" type="var">x</span></span>" implies "there is no <span
class="inlinecode"><span class="id" type="var">x</span></span> for which
<span class="inlinecode"><span class="id" type="var">P</span></span>
does not hold."

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">dist\_not\_exists</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">P</span> : <span class="id" type="var">X</span>
<span style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span class="id" type="var">P</span> <span
class="id" type="var">x</span>) <span
style="font-family: arial;">→</span> ¬ (<span
style="font-family: arial;">∃</span><span class="id"
type="var">x</span>, ¬ <span class="id" type="var">P</span> <span
class="id" type="var">x</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (not\_exists\_dist) {.section}

(The other direction of this theorem requires the classical "law of the
excluded middle".)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">not\_exists\_dist</span> :\
   <span class="id" type="var">excluded\_middle</span> <span
style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">P</span> : <span class="id" type="var">X</span>
<span style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>),\
     ¬ (<span style="font-family: arial;">∃</span><span class="id"
type="var">x</span>, ¬ <span class="id" type="var">P</span> <span
class="id" type="var">x</span>) <span
style="font-family: arial;">→</span> (<span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span class="id" type="var">P</span> <span
class="id" type="var">x</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (dist\_exists\_or) {.section}

Prove that existential quantification distributes over disjunction.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">dist\_exists\_or</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">P</span> <span class="id" type="var">Q</span> :
<span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∃</span><span class="id"
type="var">x</span>, <span class="id" type="var">P</span> <span
class="id" type="var">x</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">Q</span> <span class="id" type="var">x</span>) <span
style="font-family: arial;">↔</span> (<span
style="font-family: arial;">∃</span><span class="id"
type="var">x</span>, <span class="id" type="var">P</span> <span
class="id" type="var">x</span>) <span
style="font-family: arial;">∨</span> (<span
style="font-family: arial;">∃</span><span class="id"
type="var">x</span>, <span class="id" type="var">Q</span> <span
class="id" type="var">x</span>).\
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

Evidence-Carrying Booleans {.section}
==========================

<div class="paragraph">

</div>

So far we've seen two different forms of equality predicates: <span
class="inlinecode"><span class="id" type="var">eq</span></span>, which
produces a <span class="inlinecode"><span class="id"
type="keyword">Prop</span></span>, and the type-specific forms, like
<span class="inlinecode"><span class="id"
type="var">beq\_nat</span></span>, that produce <span
class="inlinecode"><span class="id" type="var">boolean</span></span>
values. The former are more convenient to reason about, but we've relied
on the latter to let us use equality tests in *computations*. While it
is straightforward to write lemmas (e.g. <span class="inlinecode"><span
class="id" type="var">beq\_nat\_true</span></span> and <span
class="inlinecode"><span class="id"
type="var">beq\_nat\_false</span></span>) that connect the two forms,
using these lemmas quickly gets tedious.
<div class="paragraph">

</div>

###  {.section}

It turns out that we can get the benefits of both forms at once by using
a construct called <span class="inlinecode"><span class="id"
type="var">sumbool</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">sumbool</span> (<span class="id" type="var">A</span> <span
class="id" type="var">B</span> : <span class="id"
type="keyword">Prop</span>) : <span class="id" type="keyword">Set</span>
:=\
  | <span class="id" type="var">left</span> : <span class="id"
type="var">A</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">sumbool</span> <span class="id"
type="var">A</span> <span class="id" type="var">B</span>\
  | <span class="id" type="var">right</span> : <span class="id"
type="var">B</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">sumbool</span> <span class="id"
type="var">A</span> <span class="id" type="var">B</span>.\
\
 <span class="id" type="keyword">Notation</span> "{ A } + { B }" :=
(<span class="id" type="var">sumbool</span> <span class="id"
type="var">A</span> <span class="id" type="var">B</span>) : <span
class="id" type="var">type\_scope</span>.\
\

</div>

<div class="doc">

Think of <span class="inlinecode"><span class="id"
type="var">sumbool</span></span> as being like the <span
class="inlinecode"><span class="id" type="var">boolean</span></span>
type, but instead of its values being just <span
class="inlinecode"><span class="id" type="var">true</span></span> and
<span class="inlinecode"><span class="id"
type="var">false</span></span>, they carry *evidence* of truth or
falsity. This means that when we <span class="inlinecode"><span
class="id" type="tactic">destruct</span></span> them, we are left with
the relevant evidence as a hypothesis — just as with <span
class="inlinecode"><span class="id" type="var">or</span></span>. (In
fact, the definition of <span class="inlinecode"><span class="id"
type="var">sumbool</span></span> is almost the same as for <span
class="inlinecode"><span class="id" type="var">or</span></span>. The
only difference is that values of <span class="inlinecode"><span
class="id" type="var">sumbool</span></span> are declared to be in <span
class="inlinecode"><span class="id" type="keyword">Set</span></span>
rather than in <span class="inlinecode"><span class="id"
type="keyword">Prop</span></span>; this is a technical distinction that
allows us to compute with them.)
<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

Here's how we can define a <span class="inlinecode"><span class="id"
type="var">sumbool</span></span> for equality on <span
class="inlinecode"><span class="id" type="var">nat</span></span>s

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">eq\_nat\_dec</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> : <span class="id"
type="var">nat</span>, {<span class="id" type="var">n</span> = <span
class="id" type="var">m</span>} + {<span class="id" type="var">n</span>
≠ <span class="id" type="var">m</span>}.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">n</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">n'</span>].\
   <span class="id" type="var">Case</span> "n = 0".\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">m</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">m</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">m'</span>].\
     <span class="id" type="var">SCase</span> "m = 0".\
       <span class="id" type="var">left</span>. <span class="id"
type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> "m = S m'".\
       <span class="id" type="var">right</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">contra</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">contra</span>.\
   <span class="id" type="var">Case</span> "n = S n'".\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">m</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">m</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">m'</span>].\
     <span class="id" type="var">SCase</span> "m = 0".\
       <span class="id" type="var">right</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">contra</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">contra</span>.\
     <span class="id" type="var">SCase</span> "m = S m'".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHn'</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">m</span> := <span class="id"
type="var">m'</span>) <span class="id" type="keyword">as</span> [<span
class="id" type="var">eq</span> | <span class="id"
type="var">neq</span>].\
       <span class="id" type="var">left</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="tactic">f\_equal</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">eq</span>.\
       <span class="id" type="var">right</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">Heq</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heq</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">Heq'</span>]. <span class="id"
type="tactic">apply</span> <span class="id" type="var">neq</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">Heq'</span>.\
 <span class="id" type="keyword">Defined</span>.\
\

</div>

<div class="doc">

Read as a theorem, this says that equality on <span
class="inlinecode"><span class="id" type="var">nat</span></span>s is
decidable: that is, given two <span class="inlinecode"><span class="id"
type="var">nat</span></span> values, we can always produce either
evidence that they are equal or evidence that they are not. Read
computationally, <span class="inlinecode"><span class="id"
type="var">eq\_nat\_dec</span></span> takes two <span
class="inlinecode"><span class="id" type="var">nat</span></span> values
and returns a <span class="inlinecode"><span class="id"
type="var">sumbool</span></span> constructed with <span
class="inlinecode"><span class="id" type="var">left</span></span> if
they are equal and <span class="inlinecode"><span class="id"
type="var">right</span></span> if they are not; this result can be
tested with a <span class="inlinecode"><span class="id"
type="keyword">match</span></span> or, better, with an <span
class="inlinecode"><span class="id" type="keyword">if</span>-<span
class="id" type="keyword">then</span>-<span class="id"
type="keyword">else</span></span>, just like a regular <span
class="inlinecode"><span class="id" type="var">boolean</span></span>.
(Notice that we ended this proof with <span class="inlinecode"><span
class="id" type="keyword">Defined</span></span> rather than <span
class="inlinecode"><span class="id" type="keyword">Qed</span></span>.
The only difference this makes is that the proof becomes *transparent*,
meaning that its definition is available when Coq tries to do
reductions, which is important for the computational interpretation.)
<div class="paragraph">

</div>

###  {.section}

Here's a simple example illustrating the advantages of the <span
class="inlinecode"><span class="id" type="var">sumbool</span></span>
form.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">override'</span> {<span class="id" type="var">X</span>: <span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">f</span>: <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">X</span>) (<span class="id" type="var">k</span>:<span
class="id" type="var">nat</span>) (<span class="id"
type="var">x</span>:<span class="id" type="var">X</span>) : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">X</span>:=\
   <span class="id" type="keyword">fun</span> (<span class="id"
type="var">k'</span>:<span class="id" type="var">nat</span>) ⇒ <span
class="id" type="keyword">if</span> <span class="id"
type="var">eq\_nat\_dec</span> <span class="id" type="var">k</span>
<span class="id" type="var">k'</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">x</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">f</span> <span class="id" type="var">k'</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">override\_same'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) <span
class="id" type="var">x1</span> <span class="id" type="var">k1</span>
<span class="id" type="var">k2</span> (<span class="id"
type="var">f</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">X</span>),\
   <span class="id" type="var">f</span> <span class="id"
type="var">k1</span> = <span class="id" type="var">x1</span> <span
style="font-family: arial;">→</span>\
   (<span class="id" type="var">override'</span> <span class="id"
type="var">f</span> <span class="id" type="var">k1</span> <span
class="id" type="var">x1</span>) <span class="id" type="var">k2</span> =
<span class="id" type="var">f</span> <span class="id"
type="var">k2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">X</span> <span class="id" type="var">x1</span> <span
class="id" type="var">k1</span> <span class="id" type="var">k2</span>
<span class="id" type="var">f</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">Hx1</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">override'</span>.\
   <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_nat\_dec</span> <span class="id" type="var">k1</span>
<span class="id" type="var">k2</span>). <span
class="comment">(\* observe what appears as a hypothesis \*)</span>\
   <span class="id" type="var">Case</span> "k1 = k2".\
     <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">e</span>.\
     <span class="id" type="tactic">symmetry</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">Hx1</span>.\
   <span class="id" type="var">Case</span> "k1 ≠ k2".\
     <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Compare this to the more laborious proof (in MoreCoq.v) for the version
of <span class="inlinecode"><span class="id"
type="var">override</span></span> defined using <span
class="inlinecode"><span class="id" type="var">beq\_nat</span></span>,
where we had to use the auxiliary lemma <span class="inlinecode"><span
class="id" type="var">beq\_nat\_true</span></span> to convert a fact
about booleans to a Prop.
<div class="paragraph">

</div>

#### Exercise: 1 star (override\_shadow') {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">override\_shadow'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) <span
class="id" type="var">x1</span> <span class="id" type="var">x2</span>
<span class="id" type="var">k1</span> <span class="id"
type="var">k2</span> (<span class="id" type="var">f</span> : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">X</span>),\
   (<span class="id" type="var">override'</span> (<span class="id"
type="var">override'</span> <span class="id" type="var">f</span> <span
class="id" type="var">k1</span> <span class="id" type="var">x2</span>)
<span class="id" type="var">k1</span> <span class="id"
type="var">x1</span>) <span class="id" type="var">k2</span> = (<span
class="id" type="var">override'</span> <span class="id"
type="var">f</span> <span class="id" type="var">k1</span> <span
class="id" type="var">x1</span>) <span class="id" type="var">k2</span>.\
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

Additional Exercises {.section}
====================

<div class="paragraph">

</div>

#### Exercise: 3 stars (all\_forallb) {.section}

Inductively define a property <span class="inlinecode"><span class="id"
type="var">all</span></span> of lists, parameterized by a type <span
class="inlinecode"><span class="id" type="var">X</span></span> and a
property <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id"
type="keyword">Prop</span></span>, such that <span
class="inlinecode"><span class="id" type="var">all</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">l</span></span> asserts
that <span class="inlinecode"><span class="id"
type="var">P</span></span> is true for every element of the list <span
class="inlinecode"><span class="id" type="var">l</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">all</span> (<span class="id" type="var">X</span> : <span
class="id" type="keyword">Type</span>) (<span class="id"
type="var">P</span> : <span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>) : <span class="id" type="var">list</span>
<span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span>\
 .\
\

</div>

<div class="doc">

Recall the function <span class="inlinecode"><span class="id"
type="var">forallb</span></span>, from the exercise <span
class="inlinecode"><span class="id"
type="var">forall\_exists\_challenge</span></span> in chapter <span
class="inlinecode"><span class="id" type="var">Poly</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">forallb</span> {<span class="id" type="var">X</span> : <span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">test</span> : <span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bool</span>) (<span class="id" type="var">l</span> : <span
class="id" type="var">list</span> <span class="id" type="var">X</span>)
: <span class="id" type="var">bool</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
     | [] ⇒ <span class="id" type="var">true</span>\
     | <span class="id" type="var">x</span> :: <span class="id"
type="var">l'</span> ⇒ <span class="id" type="var">andb</span> (<span
class="id" type="var">test</span> <span class="id" type="var">x</span>)
(<span class="id" type="var">forallb</span> <span class="id"
type="var">test</span> <span class="id" type="var">l'</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Using the property <span class="inlinecode"><span class="id"
type="var">all</span></span>, write down a specification for <span
class="inlinecode"><span class="id" type="var">forallb</span></span>,
and prove that it satisfies the specification. Try to make your
specification as precise as possible.
<div class="paragraph">

</div>

Are there any important properties of the function <span
class="inlinecode"><span class="id" type="var">forallb</span></span>
which are not captured by your specification?

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, advanced (filter\_challenge) {.section}

One of the main purposes of Coq is to prove that programs match their
specifications. To this end, let's prove that our definition of <span
class="inlinecode"><span class="id" type="var">filter</span></span>
matches a specification. Here is the specification, written out
informally in English.
<div class="paragraph">

</div>

Suppose we have a set <span class="inlinecode"><span class="id"
type="var">X</span></span>, a function <span class="inlinecode"><span
class="id" type="var">test</span>:</span> <span class="inlinecode"><span
class="id" type="var">X</span><span
style="font-family: arial;">→</span><span class="id"
type="var">bool</span></span>, and a list <span class="inlinecode"><span
class="id" type="var">l</span></span> of type <span
class="inlinecode"><span class="id" type="var">list</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span>. Suppose
further that <span class="inlinecode"><span class="id"
type="var">l</span></span> is an "in-order merge" of two lists, <span
class="inlinecode"><span class="id" type="var">l1</span></span> and
<span class="inlinecode"><span class="id" type="var">l2</span></span>,
such that every item in <span class="inlinecode"><span class="id"
type="var">l1</span></span> satisfies <span class="inlinecode"><span
class="id" type="var">test</span></span> and no item in <span
class="inlinecode"><span class="id" type="var">l2</span></span>
satisfies test. Then <span class="inlinecode"><span class="id"
type="var">filter</span></span> <span class="inlinecode"><span
class="id" type="var">test</span></span> <span class="inlinecode"><span
class="id" type="var">l</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">l1</span></span>.
<div class="paragraph">

</div>

A list <span class="inlinecode"><span class="id"
type="var">l</span></span> is an "in-order merge" of <span
class="inlinecode"><span class="id" type="var">l1</span></span> and
<span class="inlinecode"><span class="id" type="var">l2</span></span> if
it contains all the same elements as <span class="inlinecode"><span
class="id" type="var">l1</span></span> and <span
class="inlinecode"><span class="id" type="var">l2</span></span>, in the
same order as <span class="inlinecode"><span class="id"
type="var">l1</span></span> and <span class="inlinecode"><span
class="id" type="var">l2</span></span>, but possibly interleaved. For
example,
<div class="paragraph">

</div>

<div class="code code-tight">

    [1,4,6,2,3]
<div class="paragraph">

</div>

</div>

is an in-order merge of
<div class="paragraph">

</div>

<div class="code code-tight">

    [1,6,2]
<div class="paragraph">

</div>

</div>

and
<div class="paragraph">

</div>

<div class="code code-tight">

    [4,3].
<div class="paragraph">

</div>

</div>

Your job is to translate this specification into a Coq theorem and prove
it. (Hint: You'll need to begin by defining what it means for one list
to be a merge of two others. Do this with an inductive relation, not a
<span class="inlinecode"><span class="id"
type="keyword">Fixpoint</span></span>.)

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 5 stars, advanced, optional (filter\_challenge\_2) {.section}

A different way to formally characterize the behavior of <span
class="inlinecode"><span class="id" type="var">filter</span></span> goes
like this: Among all subsequences of <span class="inlinecode"><span
class="id" type="var">l</span></span> with the property that <span
class="inlinecode"><span class="id" type="var">test</span></span>
evaluates to <span class="inlinecode"><span class="id"
type="var">true</span></span> on all their members, <span
class="inlinecode"><span class="id" type="var">filter</span></span>
<span class="inlinecode"><span class="id" type="var">test</span></span>
<span class="inlinecode"><span class="id" type="var">l</span></span> is
the longest. Express this claim formally and prove it.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, advanced (no\_repeats) {.section}

The following inductively defined proposition...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">appears\_in</span> {<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>} (<span
class="id" type="var">a</span>:<span class="id" type="var">X</span>) :
<span class="id" type="var">list</span> <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">ai\_here</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l</span>, <span class="id" type="var">appears\_in</span>
<span class="id" type="var">a</span> (<span class="id"
type="var">a</span>::<span class="id" type="var">l</span>)\
   | <span class="id" type="var">ai\_later</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">l</span>, <span class="id"
type="var">appears\_in</span> <span class="id" type="var">a</span> <span
class="id" type="var">l</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">appears\_in</span> <span class="id" type="var">a</span>
(<span class="id" type="var">b</span>::<span class="id"
type="var">l</span>).\
\

</div>

<div class="doc">

...gives us a precise way of saying that a value <span
class="inlinecode"><span class="id" type="var">a</span></span> appears
at least once as a member of a list <span class="inlinecode"><span
class="id" type="var">l</span></span>.
<div class="paragraph">

</div>

Here's a pair of warm-ups about <span class="inlinecode"><span
class="id" type="var">appears\_in</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">appears\_in\_app</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">xs</span> <span class="id" type="var">ys</span> :
<span class="id" type="var">list</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">x</span>:<span
class="id" type="var">X</span>),\
      <span class="id" type="var">appears\_in</span> <span class="id"
type="var">x</span> (<span class="id" type="var">xs</span> ++ <span
class="id" type="var">ys</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">appears\_in</span> <span class="id" type="var">x</span> <span
class="id" type="var">xs</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">appears\_in</span> <span class="id" type="var">x</span> <span
class="id" type="var">ys</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">app\_appears\_in</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">xs</span> <span class="id" type="var">ys</span> :
<span class="id" type="var">list</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">x</span>:<span
class="id" type="var">X</span>),\
      <span class="id" type="var">appears\_in</span> <span class="id"
type="var">x</span> <span class="id" type="var">xs</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">appears\_in</span> <span class="id" type="var">x</span> <span
class="id" type="var">ys</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">appears\_in</span> <span class="id" type="var">x</span>
(<span class="id" type="var">xs</span> ++ <span class="id"
type="var">ys</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Now use <span class="inlinecode"><span class="id"
type="var">appears\_in</span></span> to define a proposition <span
class="inlinecode"><span class="id" type="var">disjoint</span></span>
<span class="inlinecode"><span class="id" type="var">X</span></span>
<span class="inlinecode"><span class="id" type="var">l1</span></span>
<span class="inlinecode"><span class="id" type="var">l2</span></span>,
which should be provable exactly when <span class="inlinecode"><span
class="id" type="var">l1</span></span> and <span
class="inlinecode"><span class="id" type="var">l2</span></span> are
lists (with elements of type X) that have no elements in common.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\

</div>

<div class="doc">

Next, use <span class="inlinecode"><span class="id"
type="var">appears\_in</span></span> to define an inductive proposition
<span class="inlinecode"><span class="id"
type="var">no\_repeats</span></span> <span class="inlinecode"><span
class="id" type="var">X</span></span> <span class="inlinecode"><span
class="id" type="var">l</span></span>, which should be provable exactly
when <span class="inlinecode"><span class="id"
type="var">l</span></span> is a list (with elements of type <span
class="inlinecode"><span class="id" type="var">X</span></span>) where
every member is different from every other. For example, <span
class="inlinecode"><span class="id" type="var">no\_repeats</span></span>
<span class="inlinecode"><span class="id" type="var">nat</span></span>
<span class="inlinecode">[1,2,3,4]</span> and <span
class="inlinecode"><span class="id" type="var">no\_repeats</span></span>
<span class="inlinecode"><span class="id" type="var">bool</span></span>
<span class="inlinecode">[]</span> should be provable, while <span
class="inlinecode"><span class="id" type="var">no\_repeats</span></span>
<span class="inlinecode"><span class="id" type="var">nat</span></span>
<span class="inlinecode">[1,2,1]</span> and <span
class="inlinecode"><span class="id" type="var">no\_repeats</span></span>
<span class="inlinecode"><span class="id" type="var">bool</span></span>
<span class="inlinecode">[<span class="id" type="var">true</span>,<span
class="id" type="var">true</span>]</span> should not be.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\

</div>

<div class="doc">

Finally, state and prove one or more interesting theorems relating <span
class="inlinecode"><span class="id" type="var">disjoint</span></span>,
<span class="inlinecode"><span class="id"
type="var">no\_repeats</span></span> and <span
class="inlinecode">++</span> (list append).

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (nostutter) {.section}

Formulating inductive definitions of predicates is an important skill
you'll need in this course. Try to solve this exercise without any help
at all.
<div class="paragraph">

</div>

We say that a list of numbers "stutters" if it repeats the same number
consecutively. The predicate "<span class="inlinecode"><span class="id"
type="var">nostutter</span></span> <span class="inlinecode"><span
class="id" type="var">mylist</span></span>" means that <span
class="inlinecode"><span class="id" type="var">mylist</span></span> does
not stutter. Formulate an inductive definition for <span
class="inlinecode"><span class="id" type="var">nostutter</span></span>.
(This is different from the <span class="inlinecode"><span class="id"
type="var">no\_repeats</span></span> predicate in the exercise above;
the sequence <span class="inlinecode">1;4;1</span> repeats but does not
stutter.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">nostutter</span>: <span class="id" type="var">list</span>
<span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
  <span class="comment">(\* FILL IN HERE \*)</span>\
 .\
\

</div>

<div class="doc">

Make sure each of these tests succeeds, but you are free to change the
proof if the given one doesn't work for you. Your definition might be
different from mine and still correct, in which case the examples might
need a different proof.
<div class="paragraph">

</div>

The suggested proofs for the examples (in comments) use a number of
tactics we haven't talked about, to try to make them robust with respect
to different possible ways of defining <span class="inlinecode"><span
class="id" type="var">nostutter</span></span>. You should be able to
just uncomment and use them as-is, but if you prefer you can also prove
each example with more basic tactics.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_nostutter\_1</span>: <span class="id"
type="var">nostutter</span> [3;1;4;1;5;6].\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="comment">(\* \
   Proof. repeat constructor; apply beq\_nat\_false; auto. Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_nostutter\_2</span>: <span class="id"
type="var">nostutter</span> [].\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="comment">(\* \
   Proof. repeat constructor; apply beq\_nat\_false; auto. Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_nostutter\_3</span>: <span class="id"
type="var">nostutter</span> [5].\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="comment">(\* \
   Proof. repeat constructor; apply beq\_nat\_false; auto. Qed.\
 \*)</span>\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_nostutter\_4</span>: <span class="id"
type="var">not</span> (<span class="id" type="var">nostutter</span>
[3;1;1;4]).\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="comment">(\* \
   Proof. intro.\
   repeat match goal with \
     h: nostutter \_ |- \_ =\> inversion h; clear h; subst \
   end.\
   contradiction H1; auto. Qed.\
 \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, advanced (pigeonhole principle) {.section}

The "pigeonhole principle" states a basic fact about counting: if you
distribute more than <span class="inlinecode"><span class="id"
type="var">n</span></span> items into <span class="inlinecode"><span
class="id" type="var">n</span></span> pigeonholes, some pigeonhole must
contain at least two items. As is often the case, this apparently
trivial fact about numbers requires non-trivial machinery to prove, but
we now have enough...
<div class="paragraph">

</div>

First a pair of useful lemmas (we already proved these for lists of
naturals, but not for arbitrary lists).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">app\_length</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">l1</span> <span class="id" type="var">l2</span> :
<span class="id" type="var">list</span> <span class="id"
type="var">X</span>),\
   <span class="id" type="var">length</span> (<span class="id"
type="var">l1</span> ++ <span class="id" type="var">l2</span>) = <span
class="id" type="var">length</span> <span class="id"
type="var">l1</span> + <span class="id" type="var">length</span> <span
class="id" type="var">l2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">appears\_in\_app\_split</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">x</span>:<span class="id" type="var">X</span>)
(<span class="id" type="var">l</span>:<span class="id"
type="var">list</span> <span class="id" type="var">X</span>),\
   <span class="id" type="var">appears\_in</span> <span class="id"
type="var">x</span> <span class="id" type="var">l</span> <span
style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">l1</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">l2</span>, <span class="id" type="var">l</span> =
<span class="id" type="var">l1</span> ++ (<span class="id"
type="var">x</span>::<span class="id" type="var">l2</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Now define a predicate <span class="inlinecode"><span class="id"
type="var">repeats</span></span> (analogous to <span
class="inlinecode"><span class="id" type="var">no\_repeats</span></span>
in the exercise above), such that <span class="inlinecode"><span
class="id" type="var">repeats</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode"><span class="id" type="var">l</span></span> asserts
that <span class="inlinecode"><span class="id"
type="var">l</span></span> contains at least one repeated element (of
type <span class="inlinecode"><span class="id"
type="var">X</span></span>).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">repeats</span> {<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>} : <span class="id"
type="var">list</span> <span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span>\
 .\
\

</div>

<div class="doc">

Now here's a way to formalize the pigeonhole principle. List <span
class="inlinecode"><span class="id" type="var">l2</span></span>
represents a list of pigeonhole labels, and list <span
class="inlinecode"><span class="id" type="var">l1</span></span>
represents the labels assigned to a list of items: if there are more
items than labels, at least two items must have the same label. This
proof is much easier if you use the <span class="inlinecode"><span
class="id" type="var">excluded\_middle</span></span> hypothesis to show
that <span class="inlinecode"><span class="id"
type="var">appears\_in</span></span> is decidable, i.e. <span
class="inlinecode"><span style="font-family: arial;">∀</span></span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode"><span class="id" type="var">l</span>,</span>
<span class="inlinecode">(<span class="id"
type="var">appears\_in</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="var">l</span>)</span> <span class="inlinecode"><span
style="font-family: arial;">∨</span></span> <span
class="inlinecode">¬</span> <span class="inlinecode">(<span class="id"
type="var">appears\_in</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="var">l</span>)</span>. However, it is also possible to
make the proof go through *without* assuming that <span
class="inlinecode"><span class="id" type="var">appears\_in</span></span>
is decidable; if you can manage to do this, you will not need the <span
class="inlinecode"><span class="id"
type="var">excluded\_middle</span></span> hypothesis.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">pigeonhole\_principle</span>: <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">l1</span> <span class="id"
type="var">l2</span>:<span class="id" type="var">list</span> <span
class="id" type="var">X</span>),\
    <span class="id" type="var">excluded\_middle</span> <span
style="font-family: arial;">→</span>\
    (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span class="id" type="var">appears\_in</span>
<span class="id" type="var">x</span> <span class="id"
type="var">l1</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">appears\_in</span> <span class="id"
type="var">x</span> <span class="id" type="var">l2</span>) <span
style="font-family: arial;">→</span>\
    <span class="id" type="var">length</span> <span class="id"
type="var">l2</span> \< <span class="id" type="var">length</span> <span
class="id" type="var">l1</span> <span
style="font-family: arial;">→</span>\
    <span class="id" type="var">repeats</span> <span class="id"
type="var">l1</span>.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">intros</span> <span class="id"
type="var">X</span> <span class="id" type="var">l1</span>. <span
class="id" type="tactic">induction</span> <span class="id"
type="var">l1</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">x</span> <span class="id" type="var">l1'</span>].\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\

</div>

<div class="doc">

</div>

<div class="code code-tight">

</div>

</div>

<div id="footer">

------------------------------------------------------------------------

[Index](http://www.cis.upenn.edu/~bcpierce/sf/current/coqindex.html)

</div>

</div>
