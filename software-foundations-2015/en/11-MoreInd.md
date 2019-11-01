<div id="page">

<div id="header">

</div>

<div id="main">

MoreInd<span class="subtitle">More on Induction</span> {.libtitle}
======================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> "ProofObjects".\
\

</div>

<div class="doc">

Induction Principles {.section}
====================

<div class="paragraph">

</div>

This is a good point to pause and take a deeper look at induction
principles.
<div class="paragraph">

</div>

Every time we declare a new <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> datatype, Coq automatically
generates and proves an *induction principle* for this type.
<div class="paragraph">

</div>

The induction principle for a type <span class="inlinecode"><span
class="id" type="var">t</span></span> is called <span
class="inlinecode"><span class="id" type="var">t\_ind</span></span>.
Here is the one for natural numbers:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">nat\_ind</span>.\
 <span class="comment">(\*  ===\> nat\_ind : \
            forall P : nat -\> Prop,\
               P 0  -\>\
               (forall n : nat, P n -\> P (S n))  -\>\
               forall n : nat, P n  \*)</span>\
\

</div>

<div class="doc">

###  {.section}

The <span class="inlinecode"><span class="id"
type="tactic">induction</span></span> tactic is a straightforward
wrapper that, at its core, simply performs <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
<span class="inlinecode"><span class="id"
type="var">t\_ind</span></span>. To see this more clearly, let's
experiment a little with using <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">nat\_ind</span></span> directly, instead of the
<span class="inlinecode"><span class="id"
type="tactic">induction</span></span> tactic, to carry out some proofs.
Here, for example, is an alternate proof of a theorem that we saw in the
<span class="inlinecode"><span class="id"
type="var">Basics</span></span> chapter.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">mult\_0\_r'</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>,\
   <span class="id" type="var">n</span> × 0 = 0.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">nat\_ind</span>.\
   <span class="id" type="var">Case</span> "O". <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "S". <span class="id"
type="tactic">simpl</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">n</span> <span class="id"
type="var">IHn</span>. <span class="id" type="tactic">rewrite</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">IHn</span>.\
     <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

This proof is basically the same as the earlier one, but a few minor
differences are worth noting. First, in the induction step of the proof
(the <span class="inlinecode">"<span class="id"
type="var">S</span>"</span> case), we have to do a little bookkeeping
manually (the <span class="inlinecode"><span class="id"
type="tactic">intros</span></span>) that <span class="inlinecode"><span
class="id" type="tactic">induction</span></span> does automatically.
<div class="paragraph">

</div>

Second, we do not introduce <span class="inlinecode"><span class="id"
type="var">n</span></span> into the context before applying <span
class="inlinecode"><span class="id" type="var">nat\_ind</span></span> —
the conclusion of <span class="inlinecode"><span class="id"
type="var">nat\_ind</span></span> is a quantified formula, and <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
needs this conclusion to exactly match the shape of the goal state,
including the quantifier. The <span class="inlinecode"><span class="id"
type="tactic">induction</span></span> tactic works either with a
variable in the context or a quantified variable in the goal.
<div class="paragraph">

</div>

Third, the <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> tactic automatically chooses variable
names for us (in the second subgoal, here), whereas <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> lets us specify (with the <span
class="inlinecode"><span class="id" type="keyword">as</span>...</span>
clause) what names should be used. The automatic choice is actually a
little unfortunate, since it re-uses the name <span
class="inlinecode"><span class="id" type="var">n</span></span> for a
variable that is different from the <span class="inlinecode"><span
class="id" type="var">n</span></span> in the original theorem. This is
why the <span class="inlinecode"><span class="id"
type="var">Case</span></span> annotation is just <span
class="inlinecode"><span class="id" type="var">S</span></span> — if we
tried to write it out in the more explicit form that we've been using
for most proofs, we'd have to write <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">S</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span>,
which doesn't make a lot of sense! All of these conveniences make <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> nicer to use in practice than
applying induction principles like <span class="inlinecode"><span
class="id" type="var">nat\_ind</span></span> directly. But it is
important to realize that, modulo this little bit of bookkeeping,
applying <span class="inlinecode"><span class="id"
type="var">nat\_ind</span></span> is what we are really doing.
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (plus\_one\_r') {.section}

Complete this proof as we did <span class="inlinecode"><span class="id"
type="var">mult\_0\_r'</span></span> above, without using the <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> tactic.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">plus\_one\_r'</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>,\
   <span class="id" type="var">n</span> + 1 = <span class="id"
type="var">S</span> <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Coq generates induction principles for every datatype defined with <span
class="inlinecode"><span class="id"
type="keyword">Inductive</span></span>, including those that aren't
recursive. (Although we don't need induction to prove properties of
non-recursive datatypes, the idea of an induction principle still makes
sense for them: it gives a way to prove that a property holds for all
values of the type.)
<div class="paragraph">

</div>

These generated principles follow a similar pattern. If we define a type
<span class="inlinecode"><span class="id" type="var">t</span></span>
with constructors <span class="inlinecode"><span class="id"
type="var">c1</span></span> ... <span class="inlinecode"><span
class="id" type="var">cn</span></span>, Coq generates a theorem with
this shape:
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="var">t\_ind</span> :\
        <span style="font-family: arial;">∀</span><span class="id"
type="var">P</span> : <span class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>,\
             ... <span class="id" type="tactic">case</span> <span
class="id" type="keyword">for</span> <span class="id"
type="var">c1</span> ... <span style="font-family: arial;">→</span>\
             ... <span class="id" type="tactic">case</span> <span
class="id" type="keyword">for</span> <span class="id"
type="var">c2</span> ... <span style="font-family: arial;">→</span>\
             ...\
             ... <span class="id" type="tactic">case</span> <span
class="id" type="keyword">for</span> <span class="id"
type="var">cn</span> ... <span style="font-family: arial;">→</span>\
             <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> : <span class="id" type="var">t</span>, <span
class="id" type="var">P</span> <span class="id" type="var">n</span>
<div class="paragraph">

</div>

</div>

The specific shape of each case depends on the arguments to the
corresponding constructor. Before trying to write down a general rule,
let's look at some more examples. First, an example where the
constructors take no arguments:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">yesno</span> : <span class="id" type="keyword">Type</span>
:=\
   | <span class="id" type="var">yes</span> : <span class="id"
type="var">yesno</span>\
   | <span class="id" type="var">no</span> : <span class="id"
type="var">yesno</span>.\
\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">yesno\_ind</span>.\
 <span
class="comment">(\* ===\> yesno\_ind : forall P : yesno -\> Prop, \
                       P yes  -\>\
                       P no  -\>\
                       forall y : yesno, P y \*)</span>\
\

</div>

<div class="doc">

#### Exercise: 1 star, optional (rgb) {.section}

Write out the induction principle that Coq will generate for the
following datatype. Write down your answer on paper or type it into a
comment, and then compare it with what Coq prints.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">rgb</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="tactic">red</span> : <span class="id"
type="var">rgb</span>\
   | <span class="id" type="var">green</span> : <span class="id"
type="var">rgb</span>\
   | <span class="id" type="var">blue</span> : <span class="id"
type="var">rgb</span>.\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">rgb\_ind</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Here's another example, this time with one of the constructors taking
some arguments.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">natlist</span> : <span class="id" type="keyword">Type</span>
:=\
   | <span class="id" type="var">nnil</span> : <span class="id"
type="var">natlist</span>\
   | <span class="id" type="var">ncons</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">natlist</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">natlist</span>.\
\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">natlist\_ind</span>.\
 <span
class="comment">(\* ===\> (modulo a little variable renaming for clarity)\
    natlist\_ind :\
       forall P : natlist -\> Prop,\
          P nnil  -\>\
          (forall (n : nat) (l : natlist), P l -\> P (ncons n l)) -\>\
          forall n : natlist, P n \*)</span>\
\

</div>

<div class="doc">

#### Exercise: 1 star, optional (natlist1) {.section}

Suppose we had written the above definition a little differently:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">natlist1</span> : <span class="id" type="keyword">Type</span>
:=\
   | <span class="id" type="var">nnil1</span> : <span class="id"
type="var">natlist1</span>\
   | <span class="id" type="var">nsnoc1</span> : <span class="id"
type="var">natlist1</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">natlist1</span>.\
\

</div>

<div class="doc">

Now what will the induction principle look like? ☐
<div class="paragraph">

</div>

From these examples, we can extract this general rule:
<div class="paragraph">

</div>

-   The type declaration gives several constructors; each corresponds to
    one clause of the induction principle.
-   Each constructor <span class="inlinecode"><span class="id"
    type="var">c</span></span> takes argument types <span
    class="inlinecode"><span class="id"
    type="var">a1</span></span>...<span class="inlinecode"><span
    class="id" type="var">an</span></span>.
-   Each <span class="inlinecode"><span class="id"
    type="var">ai</span></span> can be either <span
    class="inlinecode"><span class="id" type="var">t</span></span> (the
    datatype we are defining) or some other type <span
    class="inlinecode"><span class="id" type="var">s</span></span>.
-   The corresponding case of the induction principle says (in English):
    -   "for all values <span class="inlinecode"><span class="id"
        type="var">x1</span></span>...<span class="inlinecode"><span
        class="id" type="var">xn</span></span> of types <span
        class="inlinecode"><span class="id"
        type="var">a1</span></span>...<span class="inlinecode"><span
        class="id" type="var">an</span></span>, if <span
        class="inlinecode"><span class="id" type="var">P</span></span>
        holds for each of the inductive arguments (each <span
        class="inlinecode"><span class="id" type="var">xi</span></span>
        of type <span class="inlinecode"><span class="id"
        type="var">t</span></span>), then <span class="inlinecode"><span
        class="id" type="var">P</span></span> holds for <span
        class="inlinecode"><span class="id" type="var">c</span></span>
        <span class="inlinecode"><span class="id"
        type="var">x1</span></span> <span class="inlinecode">...</span>
        <span class="inlinecode"><span class="id"
        type="var">xn</span></span>".

<div class="paragraph">

</div>

<div class="paragraph">

</div>

#### Exercise: 1 star, optional (byntree\_ind) {.section}

Write out the induction principle that Coq will generate for the
following datatype. Write down your answer on paper or type it into a
comment, and then compare it with what Coq prints.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">byntree</span> : <span class="id" type="keyword">Type</span>
:=\
  | <span class="id" type="var">bempty</span> : <span class="id"
type="var">byntree</span>\
  | <span class="id" type="var">bleaf</span> : <span class="id"
type="var">yesno</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">byntree</span>\
  | <span class="id" type="var">nbranch</span> : <span class="id"
type="var">yesno</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">byntree</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">byntree</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">byntree</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (ex\_set) {.section}

Here is an induction principle for an inductively defined set.
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">ExSet\_ind</span> :\
          <span style="font-family: arial;">∀</span><span class="id"
type="var">P</span> : <span class="id" type="var">ExSet</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>,\
              (<span style="font-family: arial;">∀</span><span
class="id" type="var">b</span> : <span class="id"
type="var">bool</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">con1</span> <span class="id"
type="var">b</span>)) <span style="font-family: arial;">→</span>\
              (<span style="font-family: arial;">∀</span>(<span
class="id" type="var">n</span> : <span class="id"
type="var">nat</span>) (<span class="id" type="var">e</span> : <span
class="id" type="var">ExSet</span>), <span class="id"
type="var">P</span> <span class="id" type="var">e</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> (<span class="id" type="var">con2</span> <span
class="id" type="var">n</span> <span class="id"
type="var">e</span>)) <span style="font-family: arial;">→</span>\
              <span style="font-family: arial;">∀</span><span class="id"
type="var">e</span> : <span class="id" type="var">ExSet</span>, <span
class="id" type="var">P</span> <span class="id" type="var">e</span>
<div class="paragraph">

</div>

</div>

Give an <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> definition of <span
class="inlinecode"><span class="id" type="var">ExSet</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ExSet</span> : <span class="id" type="keyword">Type</span>
:=\
   <span class="comment">(\* FILL IN HERE \*)</span>\
 .\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

What about polymorphic datatypes?
<div class="paragraph">

</div>

The inductive definition of polymorphic lists
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">list</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) : <span class="id"
type="keyword">Type</span> :=\
         | <span class="id" type="var">nil</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span>\
         | <span class="id" type="var">cons</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">list</span> <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">list</span> <span class="id" type="var">X</span>.
<div class="paragraph">

</div>

</div>

is very similar to that of <span class="inlinecode"><span class="id"
type="var">natlist</span></span>. The main difference is that, here, the
whole definition is *parameterized* on a set <span
class="inlinecode"><span class="id" type="var">X</span></span>: that is,
we are defining a *family* of inductive types <span
class="inlinecode"><span class="id" type="var">list</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span>, one for
each <span class="inlinecode"><span class="id"
type="var">X</span></span>. (Note that, wherever <span
class="inlinecode"><span class="id" type="var">list</span></span>
appears in the body of the declaration, it is always applied to the
parameter <span class="inlinecode"><span class="id"
type="var">X</span></span>.) The induction principle is likewise
parameterized on <span class="inlinecode"><span class="id"
type="var">X</span></span>:
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">list\_ind</span> :\
        <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> : <span class="id"
type="keyword">Type</span>) (<span class="id"
type="var">P</span> : <span class="id" type="var">list</span> <span
class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>),\
           <span class="id" type="var">P</span> [] <span
style="font-family: arial;">→</span>\
           (<span style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> : <span class="id" type="var">X</span>) (<span
class="id" type="var">l</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span>), <span
class="id" type="var">P</span> <span class="id"
type="var">l</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> (<span class="id"
type="var">x</span> :: <span class="id" type="var">l</span>)) <span
style="font-family: arial;">→</span>\
           <span style="font-family: arial;">∀</span><span class="id"
type="var">l</span> : <span class="id" type="var">list</span> <span
class="id" type="var">X</span>, <span class="id"
type="var">P</span> <span class="id" type="var">l</span>
<div class="paragraph">

</div>

</div>

Note the wording here (and, accordingly, the form of <span
class="inlinecode"><span class="id" type="var">list\_ind</span></span>):
The *whole* induction principle is parameterized on <span
class="inlinecode"><span class="id" type="var">X</span></span>. That is,
<span class="inlinecode"><span class="id"
type="var">list\_ind</span></span> can be thought of as a polymorphic
function that, when applied to a type <span class="inlinecode"><span
class="id" type="var">X</span></span>, gives us back an induction
principle specialized to the type <span class="inlinecode"><span
class="id" type="var">list</span></span> <span class="inlinecode"><span
class="id" type="var">X</span></span>.
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (tree) {.section}

Write out the induction principle that Coq will generate for the
following datatype. Compare your answer with what Coq prints.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">tree</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) : <span class="id"
type="keyword">Type</span> :=\
   | <span class="id" type="var">leaf</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tree</span> <span class="id" type="var">X</span>\
   | <span class="id" type="var">node</span> : <span class="id"
type="var">tree</span> <span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tree</span> <span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tree</span> <span class="id" type="var">X</span>.\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">tree\_ind</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (mytype) {.section}

Find an inductive definition that gives rise to the following induction
principle:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">mytype\_ind</span> :\
         <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> : <span class="id"
type="keyword">Type</span>) (<span class="id"
type="var">P</span> : <span class="id" type="var">mytype</span> <span
class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>),\
             (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span> : <span class="id" type="var">X</span>, <span
class="id" type="var">P</span> (<span class="id"
type="var">constr1</span> <span class="id" type="var">X</span> <span
class="id" type="var">x</span>)) <span
style="font-family: arial;">→</span>\
             (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>, <span
class="id" type="var">P</span> (<span class="id"
type="var">constr2</span> <span class="id" type="var">X</span> <span
class="id" type="var">n</span>)) <span
style="font-family: arial;">→</span>\
             (<span style="font-family: arial;">∀</span><span class="id"
type="var">m</span> : <span class="id" type="var">mytype</span> <span
class="id" type="var">X</span>, <span class="id"
type="var">P</span> <span class="id" type="var">m</span> <span
style="font-family: arial;">→</span> \
                <span style="font-family: arial;">∀</span><span
class="id" type="var">n</span> : <span class="id"
type="var">nat</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">constr3</span> <span class="id"
type="var">X</span> <span class="id" type="var">m</span> <span
class="id" type="var">n</span>)) <span
style="font-family: arial;">→</span>\
             <span style="font-family: arial;">∀</span><span class="id"
type="var">m</span> : <span class="id" type="var">mytype</span> <span
class="id" type="var">X</span>, <span class="id"
type="var">P</span> <span class="id"
type="var">m</span>                   
<div class="paragraph">

</div>

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (foo) {.section}

Find an inductive definition that gives rise to the following induction
principle:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">foo\_ind</span> :\
         <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> <span class="id" type="var">Y</span> : <span
class="id" type="keyword">Type</span>) (<span class="id"
type="var">P</span> : <span class="id" type="var">foo</span> <span
class="id" type="var">X</span> <span class="id"
type="var">Y</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>),\
              (<span style="font-family: arial;">∀</span><span
class="id" type="var">x</span> : <span class="id"
type="var">X</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">bar</span> <span class="id"
type="var">X</span> <span class="id" type="var">Y</span> <span
class="id" type="var">x</span>)) <span
style="font-family: arial;">→</span>\
              (<span style="font-family: arial;">∀</span><span
class="id" type="var">y</span> : <span class="id"
type="var">Y</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">baz</span> <span class="id"
type="var">X</span> <span class="id" type="var">Y</span> <span
class="id" type="var">y</span>)) <span
style="font-family: arial;">→</span>\
              (<span style="font-family: arial;">∀</span><span
class="id" type="var">f1</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">foo</span> <span class="id"
type="var">X</span> <span class="id" type="var">Y</span>,\
                (<span style="font-family: arial;">∀</span><span
class="id" type="var">n</span> : <span class="id"
type="var">nat</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">f1</span> <span class="id"
type="var">n</span>)) <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> (<span class="id"
type="var">quux</span> <span class="id" type="var">X</span> <span
class="id" type="var">Y</span> <span class="id"
type="var">f1</span>)) <span style="font-family: arial;">→</span>\
              <span style="font-family: arial;">∀</span><span class="id"
type="var">f2</span> : <span class="id" type="var">foo</span> <span
class="id" type="var">X</span> <span class="id"
type="var">Y</span>, <span class="id" type="var">P</span> <span
class="id" type="var">f2</span>       
<div class="paragraph">

</div>

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (foo') {.section}

Consider the following inductive definition:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">foo'</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) : <span class="id"
type="keyword">Type</span> :=\
   | <span class="id" type="var">C1</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">foo'</span> <span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">foo'</span> <span class="id" type="var">X</span>\
   | <span class="id" type="var">C2</span> : <span class="id"
type="var">foo'</span> <span class="id" type="var">X</span>.\
\

</div>

<div class="doc">

What induction principle will Coq generate for <span
class="inlinecode"><span class="id" type="var">foo'</span></span>? Fill
in the blanks, then check your answer with Coq.)
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">foo'\_ind</span> :\
         <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> : <span class="id"
type="keyword">Type</span>) (<span class="id"
type="var">P</span> : <span class="id" type="var">foo'</span> <span
class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>),\
               (<span style="font-family: arial;">∀</span>(<span
class="id" type="var">l</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">f</span> : <span class="id"
type="var">foo'</span> <span class="id" type="var">X</span>),\
                     <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span> <span
style="font-family: arial;">→</span> \
                     <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span>   ) <span
style="font-family: arial;">→</span>\
              <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span> <span
style="font-family: arial;">→</span>\
              <span style="font-family: arial;">∀</span><span class="id"
type="var">f</span> : <span class="id" type="var">foo'</span> <span
class="id" type="var">X</span>, <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span>
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Induction Hypotheses {.section}
--------------------

<div class="paragraph">

</div>

Where does the phrase "induction hypothesis" fit into this story?
<div class="paragraph">

</div>

The induction principle for numbers
<div class="paragraph">

</div>

<div class="code code-tight">

       <span style="font-family: arial;">∀</span><span class="id"
type="var">P</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>,\
             <span class="id" type="var">P</span> 0  <span
style="font-family: arial;">→</span>\
             (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>, <span
class="id" type="var">P</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> (<span class="id"
type="var">S</span> <span class="id" type="var">n</span>))  <span
style="font-family: arial;">→</span>\
             <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>, <span
class="id" type="var">P</span> <span class="id" type="var">n</span>
<div class="paragraph">

</div>

</div>

is a generic statement that holds for all propositions <span
class="inlinecode"><span class="id" type="var">P</span></span> (strictly
speaking, for all families of propositions <span
class="inlinecode"><span class="id" type="var">P</span></span> indexed
by a number <span class="inlinecode"><span class="id"
type="var">n</span></span>). Each time we use this principle, we are
choosing <span class="inlinecode"><span class="id"
type="var">P</span></span> to be a particular expression of type <span
class="inlinecode"><span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span></span>.
<div class="paragraph">

</div>

We can make the proof more explicit by giving this expression a name.
For example, instead of stating the theorem <span
class="inlinecode"><span class="id" type="var">mult\_0\_r</span></span>
as "<span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">n</span>,</span> <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">×</span> <span class="inlinecode">0</span> <span
class="inlinecode">=</span> <span class="inlinecode">0</span>," we can
write it as "<span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">n</span>,</span> <span
class="inlinecode"><span class="id" type="var">P\_m0r</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span>",
where <span class="inlinecode"><span class="id"
type="var">P\_m0r</span></span> is defined as...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">P\_m0r</span> (<span class="id" type="var">n</span>:<span
class="id" type="var">nat</span>) : <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">n</span> × 0 = 0.\
\

</div>

<div class="doc">

... or equivalently...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">P\_m0r'</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="keyword">fun</span> <span class="id"
type="var">n</span> ⇒ <span class="id" type="var">n</span> × 0 = 0.\
\

</div>

<div class="doc">

Now when we do the proof it is easier to see where <span
class="inlinecode"><span class="id" type="var">P\_m0r</span></span>
appears.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">mult\_0\_r''</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>,\
   <span class="id" type="var">P\_m0r</span> <span class="id"
type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">nat\_ind</span>.\
   <span class="id" type="var">Case</span> "n = O". <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "n = S n'".\
     <span
class="comment">(\* Note the proof state at this point! \*)</span>\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">IHn</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">P\_m0r</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">IHn</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">P\_m0r</span>.
<span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHn</span>. <span
class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

This extra naming step isn't something that we'll do in normal proofs,
but it is useful to do it explicitly for an example or two, because it
allows us to see exactly what the induction hypothesis is. If we prove
<span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">n</span>,</span> <span
class="inlinecode"><span class="id" type="var">P\_m0r</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span> by
induction on <span class="inlinecode"><span class="id"
type="var">n</span></span> (using either <span class="inlinecode"><span
class="id" type="tactic">induction</span></span> or <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
<span class="inlinecode"><span class="id"
type="var">nat\_ind</span></span>), we see that the first subgoal
requires us to prove <span class="inlinecode"><span class="id"
type="var">P\_m0r</span></span> <span class="inlinecode">0</span>
("<span class="inlinecode"><span class="id" type="var">P</span></span>
holds for zero"), while the second subgoal requires us to prove <span
class="inlinecode"><span style="font-family: arial;">∀</span></span>
<span class="inlinecode"><span class="id" type="var">n'</span>,</span>
<span class="inlinecode"><span class="id"
type="var">P\_m0r</span></span> <span class="inlinecode"><span
class="id" type="var">n'</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">P\_m0r</span></span>
<span class="inlinecode"><span class="id" type="var">n'</span></span>
<span class="inlinecode">(<span class="id" type="var">S</span></span>
<span class="inlinecode"><span class="id" type="var">n'</span>)</span>
(that is "<span class="inlinecode"><span class="id"
type="var">P</span></span> holds of <span class="inlinecode"><span
class="id" type="var">S</span></span> <span class="inlinecode"><span
class="id" type="var">n'</span></span> if it holds of <span
class="inlinecode"><span class="id" type="var">n'</span></span>" or,
more elegantly, "<span class="inlinecode"><span class="id"
type="var">P</span></span> is preserved by <span
class="inlinecode"><span class="id" type="var">S</span></span>"). The
*induction hypothesis* is the premise of this latter implication — the
assumption that <span class="inlinecode"><span class="id"
type="var">P</span></span> holds of <span class="inlinecode"><span
class="id" type="var">n'</span></span>, which we are allowed to use in
proving that <span class="inlinecode"><span class="id"
type="var">P</span></span> holds for <span class="inlinecode"><span
class="id" type="var">S</span></span> <span class="inlinecode"><span
class="id" type="var">n'</span></span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

More on the <span class="inlinecode"><span class="id" type="tactic">induction</span></span> Tactic {.section}
--------------------------------------------------------------------------------------------------

<div class="paragraph">

</div>

The <span class="inlinecode"><span class="id"
type="tactic">induction</span></span> tactic actually does even more
low-level bookkeeping for us than we discussed above.
<div class="paragraph">

</div>

Recall the informal statement of the induction principle for natural
numbers:
<div class="paragraph">

</div>

-   If <span class="inlinecode"><span class="id"
    type="var">P</span></span> <span class="inlinecode"><span class="id"
    type="var">n</span></span> is some proposition involving a natural
    number n, and we want to show that P holds for *all* numbers n, we
    can reason like this:
    -   show that <span class="inlinecode"><span class="id"
        type="var">P</span></span> <span class="inlinecode"><span
        class="id" type="var">O</span></span> holds
    -   show that, if <span class="inlinecode"><span class="id"
        type="var">P</span></span> <span class="inlinecode"><span
        class="id" type="var">n'</span></span> holds, then so does <span
        class="inlinecode"><span class="id" type="var">P</span></span>
        <span class="inlinecode">(<span class="id"
        type="var">S</span></span> <span class="inlinecode"><span
        class="id" type="var">n'</span>)</span>
    -   conclude that <span class="inlinecode"><span class="id"
        type="var">P</span></span> <span class="inlinecode"><span
        class="id" type="var">n</span></span> holds for all n.

So, when we begin a proof with <span class="inlinecode"><span class="id"
type="tactic">intros</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> and then <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span>, we are first telling Coq to
consider a *particular* <span class="inlinecode"><span class="id"
type="var">n</span></span> (by introducing it into the context) and then
telling it to prove something about *all* numbers (by using induction).
<div class="paragraph">

</div>

What Coq actually does in this situation, internally, is to
"re-generalize" the variable we perform induction on. For example, in
our original proof that <span class="inlinecode"><span class="id"
type="var">plus</span></span> is associative...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">plus\_assoc'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> <span class="id"
type="var">p</span> : <span class="id" type="var">nat</span>,\
   <span class="id" type="var">n</span> + (<span class="id"
type="var">m</span> + <span class="id" type="var">p</span>) = (<span
class="id" type="var">n</span> + <span class="id" type="var">m</span>) +
<span class="id" type="var">p</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span
class="comment">(\* ...we first introduce all 3 variables into the context,\
      which amounts to saying "Consider an arbitrary <span
class="inlinecode"><span class="id" type="var">n</span></span>, <span
class="inlinecode"><span class="id" type="var">m</span></span>, and\
      <span class="inlinecode"><span class="id"
type="var">p</span></span>..." \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">p</span>.\
   <span class="comment">(\* ...We now use the <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> tactic to prove <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> (that\
      is, <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode">+</span> <span
class="inlinecode">(<span class="id" type="var">m</span></span> <span
class="inlinecode">+</span> <span class="inlinecode"><span class="id"
type="var">p</span>)</span> <span class="inlinecode">=</span> <span
class="inlinecode">(<span class="id" type="var">n</span></span> <span
class="inlinecode">+</span> <span class="inlinecode"><span class="id"
type="var">m</span>)</span> <span class="inlinecode">+</span> <span
class="inlinecode"><span class="id"
type="var">p</span></span>) for \_all\_ <span class="inlinecode"><span
class="id" type="var">n</span></span>,\
      and hence also for the particular <span class="inlinecode"><span
class="id" type="var">n</span></span> that is in the context\
      at the moment. \*)</span>\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">n</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">n'</span>].\
   <span class="id" type="var">Case</span> "n = O". <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "n = S n'".\
     <span class="comment">(\* In the second subgoal generated by <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> -- the\
        "inductive step" -- we must prove that <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id"
type="var">n'</span></span> implies \
        <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">(<span class="id"
type="var">S</span></span> <span class="inlinecode"><span class="id"
type="var">n'</span>)</span> for all <span class="inlinecode"><span
class="id" type="var">n'</span></span>.  The <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> tactic \
        automatically introduces <span class="inlinecode"><span
class="id" type="var">n'</span></span> and <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id"
type="var">n'</span></span> into the context\
        for us, leaving just <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">(<span class="id"
type="var">S</span></span> <span class="inlinecode"><span class="id"
type="var">n'</span>)</span> as the goal. \*)</span>\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">IHn'</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

It also works to apply <span class="inlinecode"><span class="id"
type="tactic">induction</span></span> to a variable that is quantified
in the goal.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">plus\_comm'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> : <span class="id"
type="var">nat</span>,\
   <span class="id" type="var">n</span> + <span class="id"
type="var">m</span> = <span class="id" type="var">m</span> + <span
class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">n</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">n'</span>].\
   <span class="id" type="var">Case</span> "n = O". <span class="id"
type="tactic">intros</span> <span class="id" type="var">m</span>. <span
class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">plus\_0\_r</span>. <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "n = S n'". <span class="id"
type="tactic">intros</span> <span class="id" type="var">m</span>. <span
class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">IHn'</span>.\
     <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">plus\_n\_Sm</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Note that <span class="inlinecode"><span class="id"
type="tactic">induction</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> leaves <span
class="inlinecode"><span class="id" type="var">m</span></span> still
bound in the goal — i.e., what we are proving inductively is a statement
beginning with <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">m</span></span>.
<div class="paragraph">

</div>

If we do <span class="inlinecode"><span class="id"
type="tactic">induction</span></span> on a variable that is quantified
in the goal *after* some other quantifiers, the <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> tactic will automatically
introduce the variables bound by these quantifiers into the context.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">plus\_comm''</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> : <span class="id"
type="var">nat</span>,\
   <span class="id" type="var">n</span> + <span class="id"
type="var">m</span> = <span class="id" type="var">m</span> + <span
class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* Let's do induction on <span
class="inlinecode"><span class="id"
type="var">m</span></span> this time, instead of <span
class="inlinecode"><span class="id"
type="var">n</span></span>... \*)</span>\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">m</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">m'</span>].\
   <span class="id" type="var">Case</span> "m = O". <span class="id"
type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">plus\_0\_r</span>. <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "m = S m'". <span class="id"
type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">IHm'</span>.\
     <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">plus\_n\_Sm</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star, optional (plus\_explicit\_prop) {.section}

Rewrite both <span class="inlinecode"><span class="id"
type="var">plus\_assoc'</span></span> and <span class="inlinecode"><span
class="id" type="var">plus\_comm'</span></span> and their proofs in the
same style as <span class="inlinecode"><span class="id"
type="var">mult\_0\_r''</span></span> above — that is, for each theorem,
give an explicit <span class="inlinecode"><span class="id"
type="keyword">Definition</span></span> of the proposition being proved
by induction, and state the theorem and proof in terms of this defined
proposition.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Generalizing Inductions. {.section}
------------------------

<div class="paragraph">

</div>

One potentially confusing feature of the <span class="inlinecode"><span
class="id" type="tactic">induction</span></span> tactic is that it
happily lets you try to set up an induction over a term that isn't
sufficiently general. The net effect of this will be to lose information
(much as <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> can do), and leave you unable to
complete the proof. Here's an example:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">one\_not\_beautiful\_FAILED</span>: ¬ <span class="id"
type="var">beautiful</span> 1.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intro</span> <span class="id"
type="var">H</span>.\
   <span class="comment">(\* Just doing an <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span> on <span class="inlinecode"><span
class="id" type="var">H</span></span> won't get us very far in the <span
class="inlinecode"><span class="id" type="var">b\_sum</span></span>\

    case. (Try it!). So we'll need induction. A naive first attempt: \*)</span>\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">H</span>.\
   <span
class="comment">(\* But now, although we get four cases, as we would expect from\
      the definition of <span class="inlinecode"><span class="id"
type="var">beautiful</span></span>, we lose all information about <span
class="inlinecode"><span class="id"
type="var">H</span></span> ! \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

The problem is that <span class="inlinecode"><span class="id"
type="tactic">induction</span></span> over a Prop only works properly
over completely general instances of the Prop, i.e. one in which all the
arguments are free (unconstrained) variables. In this respect it behaves
more like <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> than like <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span>.
<div class="paragraph">

</div>

When you're tempted to do use <span class="inlinecode"><span class="id"
type="tactic">induction</span></span> like this, it is generally an
indication that you need to be proving something more general. But in
some cases, it suffices to pull out any concrete arguments into separate
equations, like this:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">one\_not\_beautiful</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">n</span> = 1 <span
style="font-family: arial;">→</span> ¬ <span class="id"
type="var">beautiful</span> <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
  <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">E</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [| | |
<span class="id" type="var">p</span> <span class="id"
type="var">q</span> <span class="id" type="var">Hp</span> <span
class="id" type="var">IHp</span> <span class="id" type="var">Hq</span>
<span class="id" type="var">IHq</span>].\
     <span class="id" type="var">Case</span> "b\_0".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">E</span>.\
     <span class="id" type="var">Case</span> "b\_3".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">E</span>.\
     <span class="id" type="var">Case</span> "b\_5".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">E</span>.\
     <span class="id" type="var">Case</span> "b\_sum".\
       <span
class="comment">(\* the rest is a tedious case analysis \*)</span>\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">p</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">p'</span>].\
       <span class="id" type="var">SCase</span> "p = 0".\
         <span class="id" type="tactic">destruct</span> <span class="id"
type="var">q</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">q'</span>].\
         <span class="id" type="var">SSCase</span> "q = 0".\
           <span class="id" type="tactic">inversion</span> <span
class="id" type="var">E</span>.\
         <span class="id" type="var">SSCase</span> "q = S q'".\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHq</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">E</span>.\
       <span class="id" type="var">SCase</span> "p = S p'".\
         <span class="id" type="tactic">destruct</span> <span class="id"
type="var">q</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">q'</span>].\
         <span class="id" type="var">SSCase</span> "q = 0".\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHp</span>. <span class="id" type="tactic">rewrite</span>
<span class="id" type="var">plus\_0\_r</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">E</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">E</span>.\
         <span class="id" type="var">SSCase</span> "q = S q'".\
           <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">E</span>. <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">E</span>. <span class="id" type="tactic">destruct</span>
<span class="id" type="var">p'</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H0</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

There's a handy <span class="inlinecode"><span class="id"
type="var">remember</span></span> tactic that can generate the second
proof state out of the original one.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">one\_not\_beautiful'</span>: ¬ <span class="id"
type="var">beautiful</span> 1.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="var">remember</span> 1 <span class="id"
type="keyword">as</span> <span class="id" type="var">n</span> <span
class="id" type="var">eqn</span>:<span class="id" type="var">E</span>.\
   <span class="comment">(\* now carry on as above \*)</span>\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">H</span>.\
 <span class="id" type="var">Admitted</span>.\
\

</div>

<div class="doc">

Informal Proofs (Advanced) {.section}
==========================

<div class="paragraph">

</div>

Q: What is the relation between a formal proof of a proposition <span
class="inlinecode"><span class="id" type="var">P</span></span> and an
informal proof of the same proposition <span class="inlinecode"><span
class="id" type="var">P</span></span>?
<div class="paragraph">

</div>

A: The latter should *teach* the reader how to produce the former.
<div class="paragraph">

</div>

Q: How much detail is needed??
<div class="paragraph">

</div>

Unfortunately, There is no single right answer; rather, there is a range
of choices.
<div class="paragraph">

</div>

At one end of the spectrum, we can essentially give the reader the whole
formal proof (i.e., the informal proof amounts to just transcribing the
formal one into words). This gives the reader the *ability* to reproduce
the formal one for themselves, but it doesn't *teach* them anything.
<div class="paragraph">

</div>

At the other end of the spectrum, we can say "The theorem is true and
you can figure out why for yourself if you think about it hard enough."
This is also not a good teaching strategy, because usually writing the
proof requires some deep insights into the thing we're proving, and most
readers will give up before they rediscover all the same insights as we
did.
<div class="paragraph">

</div>

In the middle is the golden mean — a proof that includes all of the
essential insights (saving the reader the hard part of work that we went
through to find the proof in the first place) and clear high-level
suggestions for the more routine parts to save the reader from spending
too much time reconstructing these parts (e.g., what the IH says and
what must be shown in each case of an inductive proof), but not so much
detail that the main ideas are obscured.
<div class="paragraph">

</div>

Another key point: if we're comparing a formal proof of a proposition
<span class="inlinecode"><span class="id" type="var">P</span></span> and
an informal proof of <span class="inlinecode"><span class="id"
type="var">P</span></span>, the proposition <span
class="inlinecode"><span class="id" type="var">P</span></span> doesn't
change. That is, formal and informal proofs are *talking about the same
world* and they *must play by the same rules*.
Informal Proofs by Induction {.section}
----------------------------

<div class="paragraph">

</div>

Since we've spent much of this chapter looking "under the hood" at
formal proofs by induction, now is a good moment to talk a little about
*informal* proofs by induction.
<div class="paragraph">

</div>

In the real world of mathematical communication, written proofs range
from extremely longwinded and pedantic to extremely brief and
telegraphic. The ideal is somewhere in between, of course, but while you
are getting used to the style it is better to start out at the pedantic
end. Also, during the learning phase, it is probably helpful to have a
clear standard to compare against. With this in mind, we offer two
templates below — one for proofs by induction over *data* (i.e., where
the thing we're doing induction on lives in <span
class="inlinecode"><span class="id" type="keyword">Type</span></span>)
and one for proofs by induction over *evidence* (i.e., where the
inductively defined thing lives in <span class="inlinecode"><span
class="id" type="keyword">Prop</span></span>). In the rest of this
course, please follow one of the two for *all* of your inductive proofs.
<div class="paragraph">

</div>

### Induction Over an Inductively Defined Set {.section}

<div class="paragraph">

</div>

*Template*:
<div class="paragraph">

</div>

-   *Theorem*: \<Universally quantified proposition of the form "For all
    <span class="inlinecode"><span class="id" type="var">n</span>:<span
    class="id" type="var">S</span></span>, <span
    class="inlinecode"><span class="id" type="var">P</span>(<span
    class="id" type="var">n</span>)</span>," where <span
    class="inlinecode"><span class="id" type="var">S</span></span> is
    some inductively defined set.\>
    <div class="paragraph">

    </div>

    *Proof*: By induction on <span class="inlinecode"><span class="id"
    type="var">n</span></span>.
    <div class="paragraph">

    </div>

    \<one case for each constructor <span class="inlinecode"><span
    class="id" type="var">c</span></span> of <span
    class="inlinecode"><span class="id" type="var">S</span></span>...\>
    <div class="paragraph">

    </div>

    -   Suppose <span class="inlinecode"><span class="id"
        type="var">n</span></span> <span class="inlinecode">=</span>
        <span class="inlinecode"><span class="id"
        type="var">c</span></span> <span class="inlinecode"><span
        class="id" type="var">a1</span></span> <span
        class="inlinecode">...</span> <span class="inlinecode"><span
        class="id" type="var">ak</span></span>, where \<...and here we
        state the IH for each of the <span class="inlinecode"><span
        class="id" type="var">a</span></span>'s that has type <span
        class="inlinecode"><span class="id" type="var">S</span></span>,
        if any\>. We must show \<...and here we restate <span
        class="inlinecode"><span class="id" type="var">P</span>(<span
        class="id" type="var">c</span></span> <span
        class="inlinecode"><span class="id" type="var">a1</span></span>
        <span class="inlinecode">...</span> <span
        class="inlinecode"><span class="id"
        type="var">ak</span>)</span>\>.
        <div class="paragraph">

        </div>

        \<go on and prove <span class="inlinecode"><span class="id"
        type="var">P</span>(<span class="id" type="var">n</span>)</span>
        to finish the case...\>
        <div class="paragraph">

        </div>

    -   \<other cases similarly...\> ☐

<div class="paragraph">

</div>

*Example*:
<div class="paragraph">

</div>

-   *Theorem*: For all sets <span class="inlinecode"><span class="id"
    type="var">X</span></span>, lists <span class="inlinecode"><span
    class="id" type="var">l</span></span> <span
    class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">list</span></span> <span
    class="inlinecode"><span class="id" type="var">X</span></span>, and
    numbers <span class="inlinecode"><span class="id"
    type="var">n</span></span>, if <span class="inlinecode"><span
    class="id" type="var">length</span></span> <span
    class="inlinecode"><span class="id" type="var">l</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> then <span
    class="inlinecode"><span class="id" type="var">index</span></span>
    <span class="inlinecode">(<span class="id"
    type="var">S</span></span> <span class="inlinecode"><span class="id"
    type="var">n</span>)</span> <span class="inlinecode"><span
    class="id" type="var">l</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">None</span></span>.
    <div class="paragraph">

    </div>

    *Proof*: By induction on <span class="inlinecode"><span class="id"
    type="var">l</span></span>.
    <div class="paragraph">

    </div>

    -   Suppose <span class="inlinecode"><span class="id"
        type="var">l</span></span> <span class="inlinecode">=</span>
        <span class="inlinecode">[]</span>. We must show, for all
        numbers <span class="inlinecode"><span class="id"
        type="var">n</span></span>, that, if length <span
        class="inlinecode">[]</span> <span class="inlinecode">=</span>
        <span class="inlinecode"><span class="id"
        type="var">n</span></span>, then <span class="inlinecode"><span
        class="id" type="var">index</span></span> <span
        class="inlinecode">(<span class="id" type="var">S</span></span>
        <span class="inlinecode"><span class="id"
        type="var">n</span>)</span> <span class="inlinecode">[]</span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">None</span></span>.
        <div class="paragraph">

        </div>

        This follows immediately from the definition of index.
        <div class="paragraph">

        </div>

    -   Suppose <span class="inlinecode"><span class="id"
        type="var">l</span></span> <span class="inlinecode">=</span>
        <span class="inlinecode"><span class="id"
        type="var">x</span></span> <span class="inlinecode">::</span>
        <span class="inlinecode"><span class="id"
        type="var">l'</span></span> for some <span
        class="inlinecode"><span class="id" type="var">x</span></span>
        and <span class="inlinecode"><span class="id"
        type="var">l'</span></span>, where <span
        class="inlinecode"><span class="id"
        type="var">length</span></span> <span class="inlinecode"><span
        class="id" type="var">l'</span></span> <span
        class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">n'</span></span> implies <span
        class="inlinecode"><span class="id"
        type="var">index</span></span> <span class="inlinecode">(<span
        class="id" type="var">S</span></span> <span
        class="inlinecode"><span class="id" type="var">n'</span>)</span>
        <span class="inlinecode"><span class="id"
        type="var">l'</span></span> <span class="inlinecode">=</span>
        <span class="inlinecode"><span class="id"
        type="var">None</span></span>, for any number <span
        class="inlinecode"><span class="id" type="var">n'</span></span>.
        We must show, for all <span class="inlinecode"><span class="id"
        type="var">n</span></span>, that, if <span
        class="inlinecode"><span class="id"
        type="var">length</span></span> <span class="inlinecode">(<span
        class="id" type="var">x</span>::<span class="id"
        type="var">l'</span>)</span> <span class="inlinecode">=</span>
        <span class="inlinecode"><span class="id"
        type="var">n</span></span> then <span class="inlinecode"><span
        class="id" type="var">index</span></span> <span
        class="inlinecode">(<span class="id" type="var">S</span></span>
        <span class="inlinecode"><span class="id"
        type="var">n</span>)</span> <span class="inlinecode">(<span
        class="id" type="var">x</span>::<span class="id"
        type="var">l'</span>)</span> <span class="inlinecode">=</span>
        <span class="inlinecode"><span class="id"
        type="var">None</span></span>.
        <div class="paragraph">

        </div>

        Let <span class="inlinecode"><span class="id"
        type="var">n</span></span> be a number with <span
        class="inlinecode"><span class="id"
        type="var">length</span></span> <span class="inlinecode"><span
        class="id" type="var">l</span></span> <span
        class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">n</span></span>. Since
        <div class="paragraph">

        </div>

        <div class="code code-tight">

          <span class="id" type="var">length</span> <span class="id"
        type="var">l</span> = <span class="id"
        type="var">length</span> (<span class="id"
        type="var">x</span>::<span class="id"
        type="var">l'</span>) = <span class="id"
        type="var">S</span> (<span class="id"
        type="var">length</span> <span class="id" type="var">l'</span>),
        <div class="paragraph">

        </div>

        </div>

        it suffices to show that
        <div class="paragraph">

        </div>

        <div class="code code-tight">

          <span class="id" type="var">index</span> (<span class="id"
        type="var">S</span> (<span class="id"
        type="var">length</span> <span class="id"
        type="var">l'</span>)) <span class="id"
        type="var">l'</span> = <span class="id" type="var">None</span>.
        <div class="paragraph">

        </div>

        </div>

        But this follows directly from the induction hypothesis, picking
        <span class="inlinecode"><span class="id"
        type="var">n'</span></span> to be length <span
        class="inlinecode"><span class="id" type="var">l'</span></span>.
        ☐

<div class="paragraph">

</div>

### Induction Over an Inductively Defined Proposition {.section}

<div class="paragraph">

</div>

Since inductively defined proof objects are often called "derivation
trees," this form of proof is also known as *induction on derivations*.
<div class="paragraph">

</div>

*Template*:
<div class="paragraph">

</div>

-   *Theorem*: \<Proposition of the form "<span class="inlinecode"><span
    class="id" type="var">Q</span></span> <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">P</span></span>,"
    where <span class="inlinecode"><span class="id"
    type="var">Q</span></span> is some inductively defined proposition
    (more generally, "For all <span class="inlinecode"><span class="id"
    type="var">x</span></span> <span class="inlinecode"><span class="id"
    type="var">y</span></span> <span class="inlinecode"><span class="id"
    type="var">z</span></span>, <span class="inlinecode"><span
    class="id" type="var">Q</span></span> <span class="inlinecode"><span
    class="id" type="var">x</span></span> <span class="inlinecode"><span
    class="id" type="var">y</span></span> <span class="inlinecode"><span
    class="id" type="var">z</span></span> <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode"><span class="id" type="var">x</span></span> <span
    class="inlinecode"><span class="id" type="var">y</span></span> <span
    class="inlinecode"><span class="id" type="var">z</span></span>")\>
    <div class="paragraph">

    </div>

    *Proof*: By induction on a derivation of <span
    class="inlinecode"><span class="id" type="var">Q</span></span>.
    \<Or, more generally, "Suppose we are given <span
    class="inlinecode"><span class="id" type="var">x</span></span>,
    <span class="inlinecode"><span class="id"
    type="var">y</span></span>, and <span class="inlinecode"><span
    class="id" type="var">z</span></span>. We show that <span
    class="inlinecode"><span class="id" type="var">Q</span></span> <span
    class="inlinecode"><span class="id" type="var">x</span></span> <span
    class="inlinecode"><span class="id" type="var">y</span></span> <span
    class="inlinecode"><span class="id" type="var">z</span></span>
    implies <span class="inlinecode"><span class="id"
    type="var">P</span></span> <span class="inlinecode"><span class="id"
    type="var">x</span></span> <span class="inlinecode"><span class="id"
    type="var">y</span></span> <span class="inlinecode"><span class="id"
    type="var">z</span></span>, by induction on a derivation of <span
    class="inlinecode"><span class="id" type="var">Q</span></span> <span
    class="inlinecode"><span class="id" type="var">x</span></span> <span
    class="inlinecode"><span class="id" type="var">y</span></span> <span
    class="inlinecode"><span class="id" type="var">z</span></span>"...\>
    <div class="paragraph">

    </div>

    \<one case for each constructor <span class="inlinecode"><span
    class="id" type="var">c</span></span> of <span
    class="inlinecode"><span class="id" type="var">Q</span></span>...\>
    <div class="paragraph">

    </div>

    -   Suppose the final rule used to show <span
        class="inlinecode"><span class="id" type="var">Q</span></span>
        is <span class="inlinecode"><span class="id"
        type="var">c</span></span>. Then \<...and here we state the
        types of all of the <span class="inlinecode"><span class="id"
        type="var">a</span></span>'s together with any equalities that
        follow from the definition of the constructor and the IH for
        each of the <span class="inlinecode"><span class="id"
        type="var">a</span></span>'s that has type <span
        class="inlinecode"><span class="id" type="var">Q</span></span>,
        if there are any\>. We must show \<...and here we restate <span
        class="inlinecode"><span class="id"
        type="var">P</span></span>\>.
        <div class="paragraph">

        </div>

        \<go on and prove <span class="inlinecode"><span class="id"
        type="var">P</span></span> to finish the case...\>
        <div class="paragraph">

        </div>

    -   \<other cases similarly...\> ☐

<div class="paragraph">

</div>

*Example*
<div class="paragraph">

</div>

-   *Theorem*: The <span class="inlinecode">≤</span> relation is
    transitive — i.e., for all numbers <span class="inlinecode"><span
    class="id" type="var">n</span></span>, <span
    class="inlinecode"><span class="id" type="var">m</span></span>, and
    <span class="inlinecode"><span class="id"
    type="var">o</span></span>, if <span class="inlinecode"><span
    class="id" type="var">n</span></span> <span
    class="inlinecode">≤</span> <span class="inlinecode"><span
    class="id" type="var">m</span></span> and <span
    class="inlinecode"><span class="id" type="var">m</span></span> <span
    class="inlinecode">≤</span> <span class="inlinecode"><span
    class="id" type="var">o</span></span>, then <span
    class="inlinecode"><span class="id" type="var">n</span></span> <span
    class="inlinecode">≤</span> <span class="inlinecode"><span
    class="id" type="var">o</span></span>.
    <div class="paragraph">

    </div>

    *Proof*: By induction on a derivation of <span
    class="inlinecode"><span class="id" type="var">m</span></span> <span
    class="inlinecode">≤</span> <span class="inlinecode"><span
    class="id" type="var">o</span></span>.
    <div class="paragraph">

    </div>

    -   Suppose the final rule used to show <span
        class="inlinecode"><span class="id" type="var">m</span></span>
        <span class="inlinecode">≤</span> <span class="inlinecode"><span
        class="id" type="var">o</span></span> is <span
        class="inlinecode"><span class="id"
        type="var">le\_n</span></span>. Then <span
        class="inlinecode"><span class="id" type="var">m</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">o</span></span> and we must show that
        <span class="inlinecode"><span class="id"
        type="var">n</span></span> <span class="inlinecode">≤</span>
        <span class="inlinecode"><span class="id"
        type="var">m</span></span>, which is immediate by hypothesis.
        <div class="paragraph">

        </div>

    -   Suppose the final rule used to show <span
        class="inlinecode"><span class="id" type="var">m</span></span>
        <span class="inlinecode">≤</span> <span class="inlinecode"><span
        class="id" type="var">o</span></span> is <span
        class="inlinecode"><span class="id"
        type="var">le\_S</span></span>. Then <span
        class="inlinecode"><span class="id" type="var">o</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">S</span></span> <span
        class="inlinecode"><span class="id" type="var">o'</span></span>
        for some <span class="inlinecode"><span class="id"
        type="var">o'</span></span> with <span class="inlinecode"><span
        class="id" type="var">m</span></span> <span
        class="inlinecode">≤</span> <span class="inlinecode"><span
        class="id" type="var">o'</span></span>. We must show that <span
        class="inlinecode"><span class="id" type="var">n</span></span>
        <span class="inlinecode">≤</span> <span class="inlinecode"><span
        class="id" type="var">S</span></span> <span
        class="inlinecode"><span class="id" type="var">o'</span></span>.
        By induction hypothesis, <span class="inlinecode"><span
        class="id" type="var">n</span></span> <span
        class="inlinecode">≤</span> <span class="inlinecode"><span
        class="id" type="var">o'</span></span>.
        <div class="paragraph">

        </div>

        But then, by <span class="inlinecode"><span class="id"
        type="var">le\_S</span></span>, <span class="inlinecode"><span
        class="id" type="var">n</span></span> <span
        class="inlinecode">≤</span> <span class="inlinecode"><span
        class="id" type="var">S</span></span> <span
        class="inlinecode"><span class="id" type="var">o'</span></span>.
        ☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Induction Principles in <span class="inlinecode"><span class="id" type="keyword">Prop</span></span> (Advanced) {.section}
==============================================================================================================

<div class="paragraph">

</div>

The remainder of this chapter offers some additional details on how
induction works in Coq, the process of building proof trees, and the
"trusted computing base" that underlies Coq proofs. It can safely be
skimmed on a first reading. (As with the other advanced sections, we
recommend skimming rather than skipping over it outright: it answers
some questions that occur to many Coq users at some point, so it is
useful to have a rough idea of what's here.)
<div class="paragraph">

</div>

Earlier, we looked in detail at the induction principles that Coq
generates for inductively defined *sets*. The induction principles for
inductively defined *propositions* like <span class="inlinecode"><span
class="id" type="var">gorgeous</span></span> are a tiny bit more
complicated. As with all induction principles, we want to use the
induction principle on <span class="inlinecode"><span class="id"
type="var">gorgeous</span></span> to prove things by inductively
considering the possible shapes that something in <span
class="inlinecode"><span class="id" type="var">gorgeous</span></span>
can have — either it is evidence that <span class="inlinecode">0</span>
is gorgeous, or it is evidence that, for some <span
class="inlinecode"><span class="id" type="var">n</span></span>, <span
class="inlinecode">3+<span class="id" type="var">n</span></span> is
gorgeous, or it is evidence that, for some <span
class="inlinecode"><span class="id" type="var">n</span></span>, <span
class="inlinecode">5+<span class="id" type="var">n</span></span> is
gorgeous and it includes evidence that <span class="inlinecode"><span
class="id" type="var">n</span></span> itself is. Intuitively speaking,
however, what we want to prove are not statements about *evidence* but
statements about *numbers*. So we want an induction principle that lets
us prove properties of numbers by induction on evidence.
<div class="paragraph">

</div>

For example, from what we've said so far, you might expect the inductive
definition of <span class="inlinecode"><span class="id"
type="var">gorgeous</span></span>...
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">gorgeous</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
          <span class="id" type="var">g\_0</span> : <span class="id"
type="var">gorgeous</span> 0\
        | <span class="id" type="var">g\_plus3</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">gorgeous</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">gorgeous</span> (3+<span class="id" type="var">m</span>)\
        | <span class="id" type="var">g\_plus5</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">gorgeous</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">gorgeous</span> (5+<span class="id" type="var">m</span>).
<div class="paragraph">

</div>

</div>

...to give rise to an induction principle that looks like this...
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="var">gorgeous\_ind\_max</span> :\
        <span style="font-family: arial;">∀</span><span class="id"
type="var">P</span> : (<span style="font-family: arial;">∀</span><span
class="id" type="var">n</span> : <span class="id"
type="var">nat</span>, <span class="id" type="var">gorgeous</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>),\
             <span class="id" type="var">P</span> <span class="id"
type="var">O</span> <span class="id" type="var">g\_0</span> <span
style="font-family: arial;">→</span>\
             (<span style="font-family: arial;">∀</span>(<span
class="id" type="var">m</span> : <span class="id"
type="var">nat</span>) (<span class="id" type="var">e</span> : <span
class="id" type="var">gorgeous</span> <span class="id"
type="var">m</span>), \
                <span class="id" type="var">P</span> <span class="id"
type="var">m</span> <span class="id" type="var">e</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> (3+<span class="id" type="var">m</span>) (<span
class="id" type="var">g\_plus3</span> <span class="id"
type="var">m</span> <span class="id" type="var">e</span>) <span
style="font-family: arial;">→</span>\
             (<span style="font-family: arial;">∀</span>(<span
class="id" type="var">m</span> : <span class="id"
type="var">nat</span>) (<span class="id" type="var">e</span> : <span
class="id" type="var">gorgeous</span> <span class="id"
type="var">m</span>), \
                <span class="id" type="var">P</span> <span class="id"
type="var">m</span> <span class="id" type="var">e</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> (5+<span class="id" type="var">m</span>) (<span
class="id" type="var">g\_plus5</span> <span class="id"
type="var">m</span> <span class="id" type="var">e</span>) <span
style="font-family: arial;">→</span>\
             <span style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>) (<span
class="id" type="var">e</span> : <span class="id"
type="var">gorgeous</span> <span class="id" type="var">n</span>), <span
class="id" type="var">P</span> <span class="id"
type="var">n</span> <span class="id" type="var">e</span>
<div class="paragraph">

</div>

</div>

... because:
<div class="paragraph">

</div>

-   Since <span class="inlinecode"><span class="id"
    type="var">gorgeous</span></span> is indexed by a number <span
    class="inlinecode"><span class="id" type="var">n</span></span>
    (every <span class="inlinecode"><span class="id"
    type="var">gorgeous</span></span> object <span
    class="inlinecode"><span class="id" type="var">e</span></span> is a
    piece of evidence that some particular number <span
    class="inlinecode"><span class="id" type="var">n</span></span> is
    gorgeous), the proposition <span class="inlinecode"><span class="id"
    type="var">P</span></span> is parameterized by both <span
    class="inlinecode"><span class="id" type="var">n</span></span> and
    <span class="inlinecode"><span class="id" type="var">e</span></span>
    — that is, the induction principle can be used to prove assertions
    involving both a gorgeous number and the evidence that it is
    gorgeous.
    <div class="paragraph">

    </div>

-   Since there are three ways of giving evidence of gorgeousness (<span
    class="inlinecode"><span class="id"
    type="var">gorgeous</span></span> has three constructors), applying
    the induction principle generates three subgoals:
    <div class="paragraph">

    </div>

    -   We must prove that <span class="inlinecode"><span class="id"
        type="var">P</span></span> holds for <span
        class="inlinecode"><span class="id" type="var">O</span></span>
        and <span class="inlinecode"><span class="id"
        type="var">b\_0</span></span>.
        <div class="paragraph">

        </div>

    -   We must prove that, whenever <span class="inlinecode"><span
        class="id" type="var">n</span></span> is a gorgeous number and
        <span class="inlinecode"><span class="id"
        type="var">e</span></span> is an evidence of its gorgeousness,
        if <span class="inlinecode"><span class="id"
        type="var">P</span></span> holds of <span
        class="inlinecode"><span class="id" type="var">n</span></span>
        and <span class="inlinecode"><span class="id"
        type="var">e</span></span>, then it also holds of <span
        class="inlinecode">3+<span class="id" type="var">m</span></span>
        and <span class="inlinecode"><span class="id"
        type="var">g\_plus3</span></span> <span class="inlinecode"><span
        class="id" type="var">n</span></span> <span
        class="inlinecode"><span class="id" type="var">e</span></span>.
        <div class="paragraph">

        </div>

    -   We must prove that, whenever <span class="inlinecode"><span
        class="id" type="var">n</span></span> is a gorgeous number and
        <span class="inlinecode"><span class="id"
        type="var">e</span></span> is an evidence of its gorgeousness,
        if <span class="inlinecode"><span class="id"
        type="var">P</span></span> holds of <span
        class="inlinecode"><span class="id" type="var">n</span></span>
        and <span class="inlinecode"><span class="id"
        type="var">e</span></span>, then it also holds of <span
        class="inlinecode">5+<span class="id" type="var">m</span></span>
        and <span class="inlinecode"><span class="id"
        type="var">g\_plus5</span></span> <span class="inlinecode"><span
        class="id" type="var">n</span></span> <span
        class="inlinecode"><span class="id" type="var">e</span></span>.
        <div class="paragraph">

        </div>
-   If these subgoals can be proved, then the induction principle tells
    us that <span class="inlinecode"><span class="id"
    type="var">P</span></span> is true for *all* gorgeous numbers <span
    class="inlinecode"><span class="id" type="var">n</span></span> and
    evidence <span class="inlinecode"><span class="id"
    type="var">e</span></span> of their gorgeousness.

<div class="paragraph">

</div>

But this is a little more flexibility than we actually need or want: it
is giving us a way to prove logical assertions where the assertion
involves properties of some piece of *evidence* of gorgeousness, while
all we really care about is proving properties of *numbers* that are
gorgeous — we are interested in assertions about numbers, not about
evidence. It would therefore be more convenient to have an induction
principle for proving propositions <span class="inlinecode"><span
class="id" type="var">P</span></span> that are parameterized just by
<span class="inlinecode"><span class="id" type="var">n</span></span> and
whose conclusion establishes <span class="inlinecode"><span class="id"
type="var">P</span></span> for all gorgeous numbers <span
class="inlinecode"><span class="id" type="var">n</span></span>:
<div class="paragraph">

</div>

<div class="code code-tight">

       <span style="font-family: arial;">∀</span><span class="id"
type="var">P</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>,\
           ... <span style="font-family: arial;">→</span>\
              <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>, <span
class="id" type="var">gorgeous</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> <span class="id" type="var">n</span>
<div class="paragraph">

</div>

</div>

For this reason, Coq actually generates the following simplified
induction principle for <span class="inlinecode"><span class="id"
type="var">gorgeous</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">gorgeous\_ind</span>.\
 <span class="comment">(\* ===\>  gorgeous\_ind\
      : forall P : nat -\> Prop,\
        P 0 -\>\
        (forall n : nat, gorgeous n -\> P n -\> P (3 + n)) -\>\
        (forall n : nat, gorgeous n -\> P n -\> P (5 + n)) -\>\
        forall n : nat, gorgeous n -\> P n \*)</span>\
\

</div>

<div class="doc">

In particular, Coq has dropped the evidence term <span
class="inlinecode"><span class="id" type="var">e</span></span> as a
parameter of the the proposition <span class="inlinecode"><span
class="id" type="var">P</span></span>, and consequently has rewritten
the assumption <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode">(<span class="id" type="var">n</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">nat</span>)</span> <span class="inlinecode">(<span class="id"
type="var">e</span>:</span> <span class="inlinecode"><span class="id"
type="var">gorgeous</span></span> <span class="inlinecode"><span
class="id" type="var">n</span>),</span> <span
class="inlinecode">...</span> to be <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode">(<span class="id" type="var">n</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">nat</span>),</span> <span class="inlinecode"><span class="id"
type="var">gorgeous</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode">...</span>; i.e., we no longer require explicit
evidence of the provability of <span class="inlinecode"><span class="id"
type="var">gorgeous</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span>.
<div class="paragraph">

</div>

In English, <span class="inlinecode"><span class="id"
type="var">gorgeous\_ind</span></span> says:
<div class="paragraph">

</div>

-   Suppose, <span class="inlinecode"><span class="id"
    type="var">P</span></span> is a property of natural numbers (that
    is, <span class="inlinecode"><span class="id"
    type="var">P</span></span> <span class="inlinecode"><span class="id"
    type="var">n</span></span> is a <span class="inlinecode"><span
    class="id" type="keyword">Prop</span></span> for every <span
    class="inlinecode"><span class="id" type="var">n</span></span>). To
    show that <span class="inlinecode"><span class="id"
    type="var">P</span></span> <span class="inlinecode"><span class="id"
    type="var">n</span></span> holds whenever <span
    class="inlinecode"><span class="id" type="var">n</span></span> is
    gorgeous, it suffices to show:
    <div class="paragraph">

    </div>

    -   <span class="inlinecode"><span class="id"
        type="var">P</span></span> holds for <span
        class="inlinecode">0</span>,
        <div class="paragraph">

        </div>

    -   for any <span class="inlinecode"><span class="id"
        type="var">n</span></span>, if <span class="inlinecode"><span
        class="id" type="var">n</span></span> is gorgeous and <span
        class="inlinecode"><span class="id" type="var">P</span></span>
        holds for <span class="inlinecode"><span class="id"
        type="var">n</span></span>, then <span class="inlinecode"><span
        class="id" type="var">P</span></span> holds for <span
        class="inlinecode">3+<span class="id"
        type="var">n</span></span>,
        <div class="paragraph">

        </div>

    -   for any <span class="inlinecode"><span class="id"
        type="var">n</span></span>, if <span class="inlinecode"><span
        class="id" type="var">n</span></span> is gorgeous and <span
        class="inlinecode"><span class="id" type="var">P</span></span>
        holds for <span class="inlinecode"><span class="id"
        type="var">n</span></span>, then <span class="inlinecode"><span
        class="id" type="var">P</span></span> holds for <span
        class="inlinecode">5+<span class="id"
        type="var">n</span></span>.

<div class="paragraph">

</div>

As expected, we can apply <span class="inlinecode"><span class="id"
type="var">gorgeous\_ind</span></span> directly instead of using <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">gorgeous\_\_beautiful'</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">gorgeous</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">beautiful</span> <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">intros</span>.\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">gorgeous\_ind</span>.\
    <span class="id" type="var">Case</span> "g\_0".\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_0</span>.\
    <span class="id" type="var">Case</span> "g\_plus3".\
        <span class="id" type="tactic">intros</span>.\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_sum</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">b\_3</span>.\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">H1</span>.\
    <span class="id" type="var">Case</span> "g\_plus5".\
        <span class="id" type="tactic">intros</span>.\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_sum</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">b\_5</span>.\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">H1</span>.\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">H</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The precise form of an Inductive definition can affect the induction
principle Coq generates.
<div class="paragraph">

</div>

For example, in <span class="inlinecode"><span class="id"
type="var">Logic</span></span>, we have defined <span
class="inlinecode">≤</span> as:

</div>

<div class="code code-tight">

\
 <span class="comment">(\* Inductive le : nat -\> nat -\> Prop :=\
      | le\_n : forall n, le n n\
      | le\_S : forall n m, (le n m) -\> (le n (S m)). \*)</span>\
\

</div>

<div class="doc">

This definition can be streamlined a little by observing that the
left-hand argument <span class="inlinecode"><span class="id"
type="var">n</span></span> is the same everywhere in the definition, so
we can actually make it a "general parameter" to the whole definition,
rather than an argument to each constructor.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">le</span> (<span class="id" type="var">n</span>:<span
class="id" type="var">nat</span>) : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">le\_n</span> : <span class="id"
type="var">le</span> <span class="id" type="var">n</span> <span
class="id" type="var">n</span>\
   | <span class="id" type="var">le\_S</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">m</span>, (<span class="id" type="var">le</span> <span
class="id" type="var">n</span> <span class="id" type="var">m</span>)
<span style="font-family: arial;">→</span> (<span class="id"
type="var">le</span> <span class="id" type="var">n</span> (<span
class="id" type="var">S</span> <span class="id" type="var">m</span>)).\
\
 <span class="id" type="keyword">Notation</span> "m ≤ n" := (<span
class="id" type="var">le</span> <span class="id" type="var">m</span>
<span class="id" type="var">n</span>).\
\

</div>

<div class="doc">

The second one is better, even though it looks less symmetric. Why?
Because it gives us a simpler induction principle.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">le\_ind</span>.\
 <span class="comment">(\* ===\>  forall (n : nat) (P : nat -\> Prop),\
            P n -\>\
            (forall m : nat, n \<= m -\> P m -\> P (S m)) -\>\
            forall n0 : nat, n \<= n0 -\> P n0 \*)</span>\
\

</div>

<div class="doc">

By contrast, the induction principle that Coq calculates for the first
definition has a lot of extra quantifiers, which makes it messier to
work with when proving things by induction. Here is the induction
principle for the first <span class="inlinecode"><span class="id"
type="var">le</span></span>:

</div>

<div class="code code-tight">

\
 <span class="comment">(\* le\_ind : \
      forall P : nat -\> nat -\> Prop,\
      (forall n : nat, P n n) -\>\
      (forall n m : nat, le n m -\> P n m -\> P n (S m)) -\>\
      forall n n0 : nat, le n n0 -\> P n n0 \*)</span>\
\

</div>

<div class="doc">

Additional Exercises {.section}
====================

<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (foo\_ind\_principle) {.section}

Suppose we make the following inductive definition:
<div class="paragraph">

</div>

<div class="code code-tight">

   <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">foo</span> (<span class="id" type="var">X</span> : <span
class="id" type="keyword">Set</span>) (<span class="id"
type="var">Y</span> : <span class="id"
type="keyword">Set</span>) : <span class="id"
type="keyword">Set</span> :=\
      | <span class="id" type="var">foo1</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">foo</span> <span class="id"
type="var">X</span> <span class="id" type="var">Y</span>\
      | <span class="id" type="var">foo2</span> : <span class="id"
type="var">Y</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">foo</span> <span class="id"
type="var">X</span> <span class="id" type="var">Y</span>\
      | <span class="id" type="var">foo3</span> : <span class="id"
type="var">foo</span> <span class="id" type="var">X</span> <span
class="id" type="var">Y</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">foo</span> <span class="id" type="var">X</span> <span
class="id" type="var">Y</span>.
<div class="paragraph">

</div>

</div>

Fill in the blanks to complete the induction principle that will be
generated by Coq.
<div class="paragraph">

</div>

<div class="code code-tight">

   <span class="id" type="var">foo\_ind</span>\
         : <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> <span class="id" type="var">Y</span> : <span
class="id" type="keyword">Set</span>) (<span class="id"
type="var">P</span> : <span class="id" type="var">foo</span> <span
class="id" type="var">X</span> <span class="id"
type="var">Y</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>),   \
           (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span> : <span class="id" type="var">X</span>, <span
class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span>) <span
style="font-family: arial;">→</span>\
           (<span style="font-family: arial;">∀</span><span class="id"
type="var">y</span> : <span class="id" type="var">Y</span>, <span
class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span>) <span
style="font-family: arial;">→</span>\
           (<span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span>) <span
style="font-family: arial;">→</span>\
            <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span>
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (bar\_ind\_principle) {.section}

Consider the following induction principle:
<div class="paragraph">

</div>

<div class="code code-tight">

   <span class="id" type="var">bar\_ind</span>\
         : <span style="font-family: arial;">∀</span><span class="id"
type="var">P</span> : <span class="id" type="var">bar</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>,\
           (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>, <span
class="id" type="var">P</span> (<span class="id"
type="var">bar1</span> <span class="id" type="var">n</span>)) <span
style="font-family: arial;">→</span>\
           (<span style="font-family: arial;">∀</span><span class="id"
type="var">b</span> : <span class="id" type="var">bar</span>, <span
class="id" type="var">P</span> <span class="id"
type="var">b</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> (<span class="id"
type="var">bar2</span> <span class="id" type="var">b</span>)) <span
style="font-family: arial;">→</span>\
           (<span style="font-family: arial;">∀</span>(<span class="id"
type="var">b</span> : <span class="id" type="var">bool</span>) (<span
class="id" type="var">b0</span> : <span class="id"
type="var">bar</span>), <span class="id" type="var">P</span> <span
class="id" type="var">b0</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> (<span class="id" type="var">bar3</span> <span
class="id" type="var">b</span> <span class="id"
type="var">b0</span>)) <span style="font-family: arial;">→</span>\
           <span style="font-family: arial;">∀</span><span class="id"
type="var">b</span> : <span class="id" type="var">bar</span>, <span
class="id" type="var">P</span> <span class="id" type="var">b</span>
<div class="paragraph">

</div>

</div>

Write out the corresponding inductive set definition.
<div class="paragraph">

</div>

<div class="code code-tight">

   <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">bar</span> : <span class="id" type="keyword">Set</span> :=\
      | <span class="id" type="var">bar1</span> : <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span>\
      | <span class="id" type="var">bar2</span> : <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span>\
      | <span class="id" type="var">bar3</span> : <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span>.
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (no\_longer\_than\_ind) {.section}

Given the following inductively defined proposition:
<div class="paragraph">

</div>

<div class="code code-tight">

  <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">no\_longer\_than</span> (<span class="id"
type="var">X</span> : <span class="id"
type="keyword">Set</span>) : (<span class="id"
type="var">list</span> <span class="id" type="var">X</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
     | <span class="id" type="var">nlt\_nil</span>  : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id"
type="var">no\_longer\_than</span> <span class="id"
type="var">X</span> [] <span class="id" type="var">n</span>\
     | <span class="id" type="var">nlt\_cons</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span> <span class="id" type="var">l</span> <span
class="id" type="var">n</span>, <span class="id"
type="var">no\_longer\_than</span> <span class="id"
type="var">X</span> <span class="id" type="var">l</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> \
                                <span class="id"
type="var">no\_longer\_than</span> <span class="id"
type="var">X</span> (<span class="id" type="var">x</span>::<span
class="id" type="var">l</span>) (<span class="id"
type="var">S</span> <span class="id" type="var">n</span>)\
     | <span class="id" type="var">nlt\_succ</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l</span> <span class="id" type="var">n</span>, <span
class="id" type="var">no\_longer\_than</span> <span class="id"
type="var">X</span> <span class="id" type="var">l</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> \
                              <span class="id"
type="var">no\_longer\_than</span> <span class="id"
type="var">X</span> <span class="id" type="var">l</span> (<span
class="id" type="var">S</span> <span class="id" type="var">n</span>).
<div class="paragraph">

</div>

</div>

write the induction principle generated by Coq.
<div class="paragraph">

</div>

<div class="code code-tight">

  <span class="id" type="var">no\_longer\_than\_ind</span>\
        : <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> : <span class="id" type="keyword">Set</span>) (<span
class="id" type="var">P</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>),\
          (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>, <span
class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span>) <span
style="font-family: arial;">→</span>\
          (<span style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> : <span class="id" type="var">X</span>) (<span
class="id" type="var">l</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">n</span> : <span class="id"
type="var">nat</span>),\
           <span class="id" type="var">no\_longer\_than</span> <span
class="id" type="var">X</span> <span class="id"
type="var">l</span> <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span> <span
style="font-family: arial;">→</span> \
                                   <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span> <span
style="font-family: arial;">→</span>\
          (<span style="font-family: arial;">∀</span>(<span class="id"
type="var">l</span> : <span class="id" type="var">list</span> <span
class="id" type="var">X</span>) (<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>),\
           <span class="id" type="var">no\_longer\_than</span> <span
class="id" type="var">X</span> <span class="id"
type="var">l</span> <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span> <span
style="font-family: arial;">→</span> \
                                   <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span> <span
style="font-family: arial;">→</span>\
          <span style="font-family: arial;">∀</span>(<span class="id"
type="var">l</span> : <span class="id" type="var">list</span> <span
class="id" type="var">X</span>) (<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>), <span
class="id" type="var">no\_longer\_than</span> <span class="id"
type="var">X</span> <span class="id" type="var">l</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> \
            <span class="id"
type="var">\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_\_</span>
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Induction Principles for other Logical Propositions {.section}
---------------------------------------------------

<div class="paragraph">

</div>

Similarly, in <span class="inlinecode"><span class="id"
type="var">Logic</span></span> we have defined <span
class="inlinecode"><span class="id" type="var">eq</span></span> as:

</div>

<div class="code code-tight">

\
 <span class="comment">(\* Inductive eq (X:Type) : X -\> X -\> Prop :=\
        refl\_equal : forall x, eq X x x. \*)</span>\
\

</div>

<div class="doc">

In the Coq standard library, the definition of equality is slightly
different:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">eq'</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) (<span class="id"
type="var">x</span>:<span class="id" type="var">X</span>) : <span
class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
     <span class="id" type="var">refl\_equal'</span> : <span class="id"
type="var">eq'</span> <span class="id" type="var">X</span> <span
class="id" type="var">x</span> <span class="id" type="var">x</span>.\
\

</div>

<div class="doc">

The advantage of this definition is that the induction principle that
Coq derives for it is precisely the familiar principle of *Leibniz
equality*: what we mean when we say "<span class="inlinecode"><span
class="id" type="var">x</span></span> and <span class="inlinecode"><span
class="id" type="var">y</span></span> are equal" is that every property
on <span class="inlinecode"><span class="id" type="var">P</span></span>
that is true of <span class="inlinecode"><span class="id"
type="var">x</span></span> is also true of <span
class="inlinecode"><span class="id" type="var">y</span></span>. (One
philosophical quibble should be noted, though: Here, the "Leibniz
equality principle" is a *consequence* of the way we've defined equality
as an inductive type. Leibniz viewed things exactly the other way
around: for him, this principle itself *is the definition* of equality.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">eq'\_ind</span>.\
 <span class="comment">(\* ===\> \
      forall (X : Type) (x : X) (P : X -\> Prop),\
        P x -\> forall y : X, x =' y -\> P y \
\
    ===\>  (i.e., after a little reorganization)\
      forall (X : Type) (x : X) forall y : X, \
        x =' y -\> \
        forall P : X -\> Prop, P x -\> P y \*)</span>\
\

</div>

<div class="doc">

The induction principles for conjunction and disjunction are a good
illustration of Coq's way of generating simplified induction principles
for <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span>ly defined propositions, which we
discussed above. You try first:
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (and\_ind\_principle) {.section}

See if you can predict the induction principle for conjunction.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* Check and\_ind. \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (or\_ind\_principle) {.section}

See if you can predict the induction principle for disjunction.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* Check or\_ind. \*)</span>\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">and\_ind</span>.\
\

</div>

<div class="doc">

From the inductive definition of the proposition <span
class="inlinecode"><span class="id" type="var">and</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">Q</span></span>
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">and</span> (<span class="id" type="var">P</span> <span
class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>) : <span class="id"
type="keyword">Prop</span> :=\
        <span class="id" type="var">conj</span> : <span class="id"
type="var">P</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span> <span
style="font-family: arial;">→</span> (<span class="id"
type="var">and</span> <span class="id" type="var">P</span> <span
class="id" type="var">Q</span>).
<div class="paragraph">

</div>

</div>

we might expect Coq to generate this induction principle
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">and\_ind\_max</span> :\
        <span style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> : <span
class="id" type="keyword">Prop</span>) (<span class="id"
type="var">P0</span> : <span class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>),\
             (<span style="font-family: arial;">∀</span>(<span
class="id" type="var">a</span> : <span class="id"
type="var">P</span>) (<span class="id" type="var">b</span> : <span
class="id" type="var">Q</span>), <span class="id"
type="var">P0</span> (<span class="id" type="var">conj</span> <span
class="id" type="var">P</span> <span class="id"
type="var">Q</span> <span class="id" type="var">a</span> <span
class="id" type="var">b</span>)) <span
style="font-family: arial;">→</span>\
             <span style="font-family: arial;">∀</span><span class="id"
type="var">a</span> : <span class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Q</span>, <span class="id" type="var">P0</span> <span
class="id" type="var">a</span>
<div class="paragraph">

</div>

</div>

but actually it generates this simpler and more useful one:
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">and\_ind</span> :\
        <span style="font-family: arial;">∀</span><span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">P0</span> : <span class="id"
type="keyword">Prop</span>,\
             (<span class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">P0</span>) <span
style="font-family: arial;">→</span>\
             <span class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">P0</span>
<div class="paragraph">

</div>

</div>

In the same way, when given the inductive definition of <span
class="inlinecode"><span class="id" type="var">or</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">Q</span></span>
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">or</span> (<span class="id" type="var">P</span> <span
class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>) : <span class="id"
type="keyword">Prop</span> :=\
        | <span class="id" type="var">or\_introl</span> : <span
class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">or</span> <span class="id" type="var">P</span> <span
class="id" type="var">Q</span>\
        | <span class="id" type="var">or\_intror</span> : <span
class="id" type="var">Q</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">or</span> <span class="id" type="var">P</span> <span
class="id" type="var">Q</span>.
<div class="paragraph">

</div>

</div>

instead of the "maximal induction principle"
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">or\_ind\_max</span> :\
        <span style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> : <span
class="id" type="keyword">Prop</span>) (<span class="id"
type="var">P0</span> : <span class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>),\
             (<span style="font-family: arial;">∀</span><span class="id"
type="var">a</span> : <span class="id" type="var">P</span>, <span
class="id" type="var">P0</span> (<span class="id"
type="var">or\_introl</span> <span class="id" type="var">P</span> <span
class="id" type="var">Q</span> <span class="id"
type="var">a</span>)) <span style="font-family: arial;">→</span>\
             (<span style="font-family: arial;">∀</span><span class="id"
type="var">b</span> : <span class="id" type="var">Q</span>, <span
class="id" type="var">P0</span> (<span class="id"
type="var">or\_intror</span> <span class="id" type="var">P</span> <span
class="id" type="var">Q</span> <span class="id"
type="var">b</span>)) <span style="font-family: arial;">→</span>\
             <span style="font-family: arial;">∀</span><span class="id"
type="var">o</span> : <span class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">Q</span>, <span class="id" type="var">P0</span> <span
class="id" type="var">o</span>
<div class="paragraph">

</div>

</div>

what Coq actually generates is this:
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">or\_ind</span> :\
        <span style="font-family: arial;">∀</span><span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">P0</span> : <span class="id"
type="keyword">Prop</span>,\
             (<span class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P0</span>) <span style="font-family: arial;">→</span>\
             (<span class="id" type="var">Q</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P0</span>) <span style="font-family: arial;">→</span>\
             <span class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">P0</span>
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

#### Exercise: 1 star, optional (False\_ind\_principle) {.section}

Can you predict the induction principle for falsehood?

</div>

<div class="code code-tight">

\
 <span class="comment">(\* Check False\_ind. \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Here's the induction principle that Coq generates for existentials:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">ex\_ind</span>.\
 <span
class="comment">(\* ===\>  forall (X:Type) (P: X-\>Prop) (Q: Prop),\
          (forall witness:X, P witness -\> Q) -\> \
           ex X P -\> \
            Q \*)</span>\
\

</div>

<div class="doc">

This induction principle can be understood as follows: If we have a
function <span class="inlinecode"><span class="id"
type="var">f</span></span> that can construct evidence for <span
class="inlinecode"><span class="id" type="var">Q</span></span> given
*any* witness of type <span class="inlinecode"><span class="id"
type="var">X</span></span> together with evidence that this witness has
property <span class="inlinecode"><span class="id"
type="var">P</span></span>, then from a proof of <span
class="inlinecode"><span class="id" type="var">ex</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span> we can
extract the witness and evidence that must have been supplied to the
constructor, give these to <span class="inlinecode"><span class="id"
type="var">f</span></span>, and thus obtain a proof of <span
class="inlinecode"><span class="id" type="var">Q</span></span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Explicit Proof Objects for Induction {.section}
------------------------------------

<div class="paragraph">

</div>

Although tactic-based proofs are normally much easier to work with, the
ability to write a proof term directly is sometimes very handy,
particularly when we want Coq to do something slightly non-standard.
<div class="paragraph">

</div>

Recall the induction principle on naturals that Coq generates for us
automatically from the Inductive declation for <span
class="inlinecode"><span class="id" type="var">nat</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">nat\_ind</span>.\
 <span class="comment">(\* ===\> \
    nat\_ind : forall P : nat -\> Prop,\
       P 0 -\> \
       (forall n : nat, P n -\> P (S n)) -\> \
       forall n : nat, P n  \*)</span>\
\

</div>

<div class="doc">

There's nothing magic about this induction lemma: it's just another Coq
lemma that requires a proof. Coq generates the proof automatically
too...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">nat\_ind</span>.\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">nat\_rect</span>.\
 <span
class="comment">(\* ===\> (after some manual inlining and tidying)\
    nat\_ind =\
     fun (P : nat -\> Prop) \
         (f : P 0) \
         (f0 : forall n : nat, P n -\> P (S n)) =\>\
           fix F (n : nat) : P n :=\
              match n with\
             | 0 =\> f\
             | S n0 =\> f0 n0 (F n0)\
             end.\
 \*)</span>\
\

</div>

<div class="doc">

We can read this as follows: Suppose we have evidence <span
class="inlinecode"><span class="id" type="var">f</span></span> that
<span class="inlinecode"><span class="id" type="var">P</span></span>
holds on 0, and evidence <span class="inlinecode"><span class="id"
type="var">f0</span></span> that <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">n</span>:<span class="id"
type="var">nat</span>,</span> <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">(<span class="id" type="var">S</span></span> <span
class="inlinecode"><span class="id" type="var">n</span>)</span>. Then we
can prove that <span class="inlinecode"><span class="id"
type="var">P</span></span> holds of an arbitrary nat <span
class="inlinecode"><span class="id" type="var">n</span></span> via a
recursive function <span class="inlinecode"><span class="id"
type="var">F</span></span> (here defined using the expression form <span
class="inlinecode"><span class="id" type="keyword">Fix</span></span>
rather than by a top-level <span class="inlinecode"><span class="id"
type="keyword">Fixpoint</span></span> declaration). <span
class="inlinecode"><span class="id" type="var">F</span></span> pattern
matches on <span class="inlinecode"><span class="id"
type="var">n</span></span>:
<div class="paragraph">

</div>

-   If it finds 0, <span class="inlinecode"><span class="id"
    type="var">F</span></span> uses <span class="inlinecode"><span
    class="id" type="var">f</span></span> to show that <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode"><span class="id" type="var">n</span></span>
    holds.
-   If it finds <span class="inlinecode"><span class="id"
    type="var">S</span></span> <span class="inlinecode"><span class="id"
    type="var">n0</span></span>, <span class="inlinecode"><span
    class="id" type="var">F</span></span> applies itself recursively on
    <span class="inlinecode"><span class="id"
    type="var">n0</span></span> to obtain evidence that <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode"><span class="id" type="var">n0</span></span>
    holds; then it applies <span class="inlinecode"><span class="id"
    type="var">f0</span></span> on that evidence to show that <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode">(<span class="id" type="var">S</span></span>
    <span class="inlinecode"><span class="id"
    type="var">n</span>)</span> holds.

<span class="inlinecode"><span class="id" type="var">F</span></span> is
just an ordinary recursive function that happens to operate on evidence
in <span class="inlinecode"><span class="id"
type="keyword">Prop</span></span> rather than on terms in <span
class="inlinecode"><span class="id" type="keyword">Set</span></span>.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

We can adapt this approach to proving <span class="inlinecode"><span
class="id" type="var">nat\_ind</span></span> to help prove
*non-standard* induction principles too. Recall our desire to prove that
<div class="paragraph">

</div>

<span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">nat</span>,</span> <span class="inlinecode"><span class="id"
type="var">even</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">ev</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span>.
<div class="paragraph">

</div>

Attempts to do this by standard induction on <span
class="inlinecode"><span class="id" type="var">n</span></span> fail,
because the induction principle only lets us proceed when we can prove
that <span class="inlinecode"><span class="id"
type="var">even</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">even</span></span> <span
class="inlinecode">(<span class="id" type="var">S</span></span> <span
class="inlinecode"><span class="id" type="var">n</span>)</span> — which
is of course never provable. What we did in <span
class="inlinecode"><span class="id" type="var">Logic</span></span> was a
bit of a hack:
<div class="paragraph">

</div>

<span class="inlinecode"><span class="id"
type="keyword">Theorem</span></span> <span class="inlinecode"><span
class="id" type="var">even\_\_ev</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">nat</span>,</span> <span class="inlinecode">(<span class="id"
type="var">even</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">ev</span></span> <span
class="inlinecode"><span class="id" type="var">n</span>)</span> <span
class="inlinecode"><span style="font-family: arial;">∧</span></span>
<span class="inlinecode">(<span class="id" type="var">even</span></span>
<span class="inlinecode">(<span class="id" type="var">S</span></span>
<span class="inlinecode"><span class="id" type="var">n</span>)</span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">ev</span></span> <span
class="inlinecode">(<span class="id" type="var">S</span></span> <span
class="inlinecode"><span class="id" type="var">n</span>))</span>.
<div class="paragraph">

</div>

We can make a much better proof by defining and proving a non-standard
induction principle that goes "by twos":
<div class="paragraph">

</div>

</div>

<div class="code code-tight">

\
  <span class="id" type="keyword">Definition</span> <span class="id"
type="var">nat\_ind2</span> :\
     <span style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>),\
     <span class="id" type="var">P</span> 0 <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">P</span> 1 <span
style="font-family: arial;">→</span>\
     (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>, <span
class="id" type="var">P</span> <span class="id" type="var">n</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">P</span> (<span class="id" type="var">S</span>(<span
class="id" type="var">S</span> <span class="id" type="var">n</span>)))
<span style="font-family: arial;">→</span>\
     <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> : <span class="id" type="var">nat</span> , <span
class="id" type="var">P</span> <span class="id" type="var">n</span> :=\
        <span class="id" type="keyword">fun</span> <span class="id"
type="var">P</span> ⇒ <span class="id" type="keyword">fun</span> <span
class="id" type="var">P0</span> ⇒ <span class="id"
type="keyword">fun</span> <span class="id" type="var">P1</span> ⇒ <span
class="id" type="keyword">fun</span> <span class="id"
type="var">PSS</span> ⇒\
           <span class="id" type="var">fix</span> <span class="id"
type="var">f</span> (<span class="id" type="var">n</span>:<span
class="id" type="var">nat</span>) := <span class="id"
type="keyword">match</span> <span class="id" type="var">n</span> <span
class="id" type="keyword">with</span>\
                              0 ⇒ <span class="id" type="var">P0</span>\
                            | 1 ⇒ <span class="id" type="var">P1</span>\
                            | <span class="id" type="var">S</span>
(<span class="id" type="var">S</span> <span class="id"
type="var">n'</span>) ⇒ <span class="id" type="var">PSS</span> <span
class="id" type="var">n'</span> (<span class="id" type="var">f</span>
<span class="id" type="var">n'</span>)\
                           <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Once you get the hang of it, it is entirely straightforward to give an
explicit proof term for induction principles like this. Proving this as
a lemma using tactics is much less intuitive (try it!).
<div class="paragraph">

</div>

The <span class="inlinecode"><span class="id"
type="tactic">induction</span></span> <span
class="inlinecode">...</span> <span class="inlinecode"><span class="id"
type="keyword">using</span></span> tactic variant gives a convenient way
to specify a non-standard induction principle like this.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">even\_\_ev'</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">even</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ev</span> <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
  <span class="id" type="tactic">intros</span>.\
  <span class="id" type="tactic">induction</span> <span class="id"
type="var">n</span> <span class="id" type="keyword">as</span> [ | |<span
class="id" type="var">n'</span>] <span class="id"
type="keyword">using</span> <span class="id"
type="var">nat\_ind2</span>.\
   <span class="id" type="var">Case</span> "even 0".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ev\_0</span>.\
   <span class="id" type="var">Case</span> "even 1".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="var">Case</span> "even (S(S n'))".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ev\_SS</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHn'</span>. <span class="id" type="tactic">unfold</span>
<span class="id" type="var">even</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">even</span>
<span class="id" type="keyword">in</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">simpl</span> <span
class="id" type="keyword">in</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">H</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The Coq Trusted Computing Base {.section}
------------------------------

<div class="paragraph">

</div>

One issue that arises with any automated proof assistant is "why trust
it?": what if there is a bug in the implementation that renders all its
reasoning suspect?
<div class="paragraph">

</div>

While it is impossible to allay such concerns completely, the fact that
Coq is based on the Curry-Howard correspondence gives it a strong
foundation. Because propositions are just types and proofs are just
terms, checking that an alleged proof of a proposition is valid just
amounts to *type-checking* the term. Type checkers are relatively small
and straightforward programs, so the "trusted computing base" for Coq —
the part of the code that we have to believe is operating correctly — is
small too.
<div class="paragraph">

</div>

What must a typechecker do? Its primary job is to make sure that in each
function application the expected and actual argument types match, that
the arms of a <span class="inlinecode"><span class="id"
type="keyword">match</span></span> expression are constructor patterns
belonging to the inductive type being matched over and all arms of the
<span class="inlinecode"><span class="id"
type="keyword">match</span></span> return the same type, and so on.
<div class="paragraph">

</div>

There are a few additional wrinkles:
<div class="paragraph">

</div>

-   Since Coq types can themselves be expressions, the checker must
    normalize these (by using the computation rules) before comparing
    them.
    <div class="paragraph">

    </div>

-   The checker must make sure that <span class="inlinecode"><span
    class="id" type="keyword">match</span></span> expressions are
    *exhaustive*. That is, there must be an arm for every possible
    constructor. To see why, consider the following alleged proof
    object:
    <div class="paragraph">

    </div>

    <div class="code code-tight">

    <span class="id" type="keyword">Definition</span> <span class="id"
    type="var">or\_bogus</span> : <span
    style="font-family: arial;">∀</span><span class="id"
    type="var">P</span> <span class="id" type="var">Q</span>, <span
    class="id" type="var">P</span> <span
    style="font-family: arial;">∨</span> <span class="id"
    type="var">Q</span> <span style="font-family: arial;">→</span> <span
    class="id" type="var">P</span> :=\
       <span class="id" type="keyword">fun</span> (<span class="id"
    type="var">P</span> <span class="id" type="var">Q</span> : <span
    class="id" type="keyword">Prop</span>) (<span class="id"
    type="var">A</span> : <span class="id" type="var">P</span> <span
    style="font-family: arial;">∨</span> <span class="id"
    type="var">Q</span>) ⇒\
          <span class="id" type="keyword">match</span> <span class="id"
    type="var">A</span> <span class="id" type="keyword">with</span>\
          | <span class="id" type="var">or\_introl</span> <span
    class="id" type="var">H</span> ⇒ <span class="id"
    type="var">H</span>\
          <span class="id" type="keyword">end</span>.
    <div class="paragraph">

    </div>

    </div>

    All the types here match correctly, but the <span
    class="inlinecode"><span class="id"
    type="keyword">match</span></span> only considers one of the
    possible constructors for <span class="inlinecode"><span class="id"
    type="var">or</span></span>. Coq's exhaustiveness check will reject
    this definition.
    <div class="paragraph">

    </div>

-   The checker must make sure that each <span class="inlinecode"><span
    class="id" type="var">fix</span></span> expression terminates. It
    does this using a syntactic check to make sure that each recursive
    call is on a subexpression of the original argument. To see why this
    is essential, consider this alleged proof:
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span class="id" type="keyword">Definition</span> <span
    class="id" type="var">nat\_false</span> : <span
    style="font-family: arial;">∀</span>(<span class="id"
    type="var">n</span>:<span class="id" type="var">nat</span>), <span
    class="id" type="var">False</span> :=\
            <span class="id" type="var">fix</span> <span class="id"
    type="var">f</span> (<span class="id" type="var">n</span>:<span
    class="id" type="var">nat</span>) : <span class="id"
    type="var">False</span> := <span class="id"
    type="var">f</span> <span class="id" type="var">n</span>.
    <div class="paragraph">

    </div>

    </div>

    Again, this is perfectly well-typed, but (fortunately) Coq will
    reject it.

<div class="paragraph">

</div>

Note that the soundness of Coq depends only on the correctness of this
typechecking engine, not on the tactic machinery. If there is a bug in a
tactic implementation (and this certainly does happen!), that tactic
might construct an invalid proof term. But when you type <span
class="inlinecode"><span class="id" type="keyword">Qed</span></span>,
Coq checks the term for validity from scratch. Only lemmas whose proofs
pass the type-checker can be used in further proof developments.
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
