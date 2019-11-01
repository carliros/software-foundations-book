<div id="page">

<div id="header">

</div>

<div id="main">

MoreCoq<span class="subtitle">More About Coq's Tactics</span> {.libtitle}
=============================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">Poly</span>.\
\

</div>

<div class="doc">

This chapter introduces several more proof strategies and tactics that,
together, allow us to prove theorems about the functional programs we
have been writing. In particular, we'll reason about functions that work
with natural numbers and lists.
<div class="paragraph">

</div>

In particular, we will see:
<div class="paragraph">

</div>

-   how to use auxiliary lemmas, in both forwards and backwards
    reasoning;
-   how to reason about data constructors, which are injective and
    disjoint;
-   how to create a strong induction hypotheses (and when strengthening
    is required); and
-   how to reason by case analysis.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id" type="tactic">apply</span></span> Tactic {.section}
======================================================================================

<div class="paragraph">

</div>

We often encounter situations where the goal to be proved is exactly the
same as some hypothesis in the context or some previously proved lemma.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">silly1</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">o</span> <span class="id" type="var">p</span> :
<span class="id" type="var">nat</span>),\
      <span class="id" type="var">n</span> = <span class="id"
type="var">m</span> <span style="font-family: arial;">→</span>\
      [<span class="id" type="var">n</span>;<span class="id"
type="var">o</span>] = [<span class="id" type="var">n</span>;<span
class="id" type="var">p</span>] <span
style="font-family: arial;">→</span>\
      [<span class="id" type="var">n</span>;<span class="id"
type="var">o</span>] = [<span class="id" type="var">m</span>;<span
class="id" type="var">p</span>].\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">o</span> <span class="id" type="var">p</span>
<span class="id" type="var">eq1</span> <span class="id"
type="var">eq2</span>.\
   <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">eq1</span>.\
   <span class="comment">(\* At this point, we could finish with \
      "<span class="inlinecode"><span class="id"
type="tactic">rewrite</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">eq2</span>.</span> <span
class="inlinecode"><span class="id"
type="tactic">reflexivity</span>.</span>" as we have \
      done several times above. But we can achieve the\
      same effect in a single step by using the \
      <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> tactic instead: \*)</span>\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">eq2</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> tactic also works with *conditional*
hypotheses and lemmas: if the statement being applied is an implication,
then the premises of this implication will be added to the list of
subgoals needing to be proved.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">silly2</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">o</span> <span class="id" type="var">p</span> :
<span class="id" type="var">nat</span>),\
      <span class="id" type="var">n</span> = <span class="id"
type="var">m</span> <span style="font-family: arial;">→</span>\
      (<span style="font-family: arial;">∀</span>(<span class="id"
type="var">q</span> <span class="id" type="var">r</span> : <span
class="id" type="var">nat</span>), <span class="id" type="var">q</span>
= <span class="id" type="var">r</span> <span
style="font-family: arial;">→</span> [<span class="id"
type="var">q</span>;<span class="id" type="var">o</span>] = [<span
class="id" type="var">r</span>;<span class="id" type="var">p</span>])
<span style="font-family: arial;">→</span>\
      [<span class="id" type="var">n</span>;<span class="id"
type="var">o</span>] = [<span class="id" type="var">m</span>;<span
class="id" type="var">p</span>].\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">o</span> <span class="id" type="var">p</span>
<span class="id" type="var">eq1</span> <span class="id"
type="var">eq2</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">eq2</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">eq1</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

You may find it instructive to experiment with this proof and see if
there is a way to complete it using just <span class="inlinecode"><span
class="id" type="tactic">rewrite</span></span> instead of <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>.
<div class="paragraph">

</div>

Typically, when we use <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span>, the statement <span
class="inlinecode"><span class="id" type="var">H</span></span> will
begin with a <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> binding some *universal
variables*. When Coq matches the current goal against the conclusion of
<span class="inlinecode"><span class="id" type="var">H</span></span>, it
will try to find appropriate values for these variables. For example,
when we do <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">eq2</span></span> in the following proof, the
universal variable <span class="inlinecode"><span class="id"
type="var">q</span></span> in <span class="inlinecode"><span class="id"
type="var">eq2</span></span> gets instantiated with <span
class="inlinecode"><span class="id" type="var">n</span></span> and <span
class="inlinecode"><span class="id" type="var">r</span></span> gets
instantiated with <span class="inlinecode"><span class="id"
type="var">m</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">silly2a</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> <span class="id" type="var">m</span> : <span
class="id" type="var">nat</span>),\
      (<span class="id" type="var">n</span>,<span class="id"
type="var">n</span>) = (<span class="id" type="var">m</span>,<span
class="id" type="var">m</span>) <span
style="font-family: arial;">→</span>\
      (<span style="font-family: arial;">∀</span>(<span class="id"
type="var">q</span> <span class="id" type="var">r</span> : <span
class="id" type="var">nat</span>), (<span class="id"
type="var">q</span>,<span class="id" type="var">q</span>) = (<span
class="id" type="var">r</span>,<span class="id" type="var">r</span>)
<span style="font-family: arial;">→</span> [<span class="id"
type="var">q</span>] = [<span class="id" type="var">r</span>]) <span
style="font-family: arial;">→</span>\
      [<span class="id" type="var">n</span>] = [<span class="id"
type="var">m</span>].\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">eq1</span> <span class="id"
type="var">eq2</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">eq2</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">eq1</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (silly\_ex) {.section}

Complete the following proof without using <span
class="inlinecode"><span class="id" type="tactic">simpl</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">silly\_ex</span> :\
      (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">evenb</span> <span
class="id" type="var">n</span> = <span class="id" type="var">true</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">oddb</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>) = <span class="id"
type="var">true</span>) <span style="font-family: arial;">→</span>\
      <span class="id" type="var">evenb</span> 3 = <span class="id"
type="var">true</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">oddb</span> 4 = <span class="id"
type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

To use the <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> tactic, the (conclusion of the) fact
being applied must match the goal *exactly* — for example, <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
will not work if the left and right sides of the equality are swapped.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">silly3\_firsttry</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>),\
      <span class="id" type="var">true</span> = <span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n</span> 5 <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">beq\_nat</span> (<span class="id"
type="var">S</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>)) 7 = <span class="id"
type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">H</span>.\
   <span class="id" type="tactic">simpl</span>.\
   <span class="comment">(\* Here we cannot use <span
class="inlinecode"><span class="id"
type="tactic">apply</span></span> directly \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

In this case we can use the <span class="inlinecode"><span class="id"
type="tactic">symmetry</span></span> tactic, which switches the left and
right sides of an equality in the goal.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">silly3</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>),\
      <span class="id" type="var">true</span> = <span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n</span> 5 <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">beq\_nat</span> (<span class="id"
type="var">S</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>)) 7 = <span class="id"
type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">H</span>.\
   <span class="id" type="tactic">symmetry</span>.\
   <span class="id" type="tactic">simpl</span>. <span
class="comment">(\* Actually, this <span class="inlinecode"><span
class="id" type="tactic">simpl</span></span> is unnecessary, since \
             <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> will perform simplification first. \*)</span>\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">H</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars (apply\_exercise1) {.section}

Hint: you can use <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> with previously defined lemmas, not
just hypotheses in the context. Remember that <span
class="inlinecode"><span class="id" type="var">SearchAbout</span></span>
is your friend.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">rev\_exercise1</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">l</span> <span class="id" type="var">l'</span> : <span
class="id" type="var">list</span> <span class="id"
type="var">nat</span>),\
      <span class="id" type="var">l</span> = <span class="id"
type="var">rev</span> <span class="id" type="var">l'</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">l'</span> = <span class="id"
type="var">rev</span> <span class="id" type="var">l</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (apply\_rewrite) {.section}

Briefly explain the difference between the tactics <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
and <span class="inlinecode"><span class="id"
type="tactic">rewrite</span></span>. Are there situations where both can
usefully be applied? <span class="comment">(\* FILL IN HERE \*)</span>\
 ☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id" type="tactic">apply</span></span> <span class="inlinecode">...</span> <span class="inlinecode"><span class="id" type="keyword">with</span></span> <span class="inlinecode">...</span> Tactic {.section}
==========================================================================================================================================================================================================================================

<div class="paragraph">

</div>

The following silly example uses two rewrites in a row to get from <span
class="inlinecode">[<span class="id" type="var">a</span>,<span
class="id" type="var">b</span>]</span> to <span
class="inlinecode">[<span class="id" type="var">e</span>,<span
class="id" type="var">f</span>]</span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">trans\_eq\_example</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span> <span class="id" type="var">d</span>
<span class="id" type="var">e</span> <span class="id"
type="var">f</span> : <span class="id" type="var">nat</span>),\
      [<span class="id" type="var">a</span>;<span class="id"
type="var">b</span>] = [<span class="id" type="var">c</span>;<span
class="id" type="var">d</span>] <span
style="font-family: arial;">→</span>\
      [<span class="id" type="var">c</span>;<span class="id"
type="var">d</span>] = [<span class="id" type="var">e</span>;<span
class="id" type="var">f</span>] <span
style="font-family: arial;">→</span>\
      [<span class="id" type="var">a</span>;<span class="id"
type="var">b</span>] = [<span class="id" type="var">e</span>;<span
class="id" type="var">f</span>].\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">a</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span> <span class="id" type="var">d</span>
<span class="id" type="var">e</span> <span class="id"
type="var">f</span> <span class="id" type="var">eq1</span> <span
class="id" type="var">eq2</span>.\
   <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">eq1</span>. <span class="id" type="tactic">rewrite</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">eq2</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Since this is a common pattern, we might abstract it out as a lemma
recording once and for all the fact that equality is transitive.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">trans\_eq</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">n</span> <span class="id" type="var">m</span>
<span class="id" type="var">o</span> : <span class="id"
type="var">X</span>),\
   <span class="id" type="var">n</span> = <span class="id"
type="var">m</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">m</span> = <span class="id" type="var">o</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">n</span> = <span class="id" type="var">o</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">X</span> <span class="id" type="var">n</span> <span
class="id" type="var">m</span> <span class="id" type="var">o</span>
<span class="id" type="var">eq1</span> <span class="id"
type="var">eq2</span>. <span class="id" type="tactic">rewrite</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">eq1</span>. <span class="id" type="tactic">rewrite</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">eq2</span>.\
   <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Now, we should be able to use <span class="inlinecode"><span class="id"
type="var">trans\_eq</span></span> to prove the above example. However,
to do this we need a slight refinement of the <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
tactic.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">trans\_eq\_example'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span> <span class="id" type="var">d</span>
<span class="id" type="var">e</span> <span class="id"
type="var">f</span> : <span class="id" type="var">nat</span>),\
      [<span class="id" type="var">a</span>;<span class="id"
type="var">b</span>] = [<span class="id" type="var">c</span>;<span
class="id" type="var">d</span>] <span
style="font-family: arial;">→</span>\
      [<span class="id" type="var">c</span>;<span class="id"
type="var">d</span>] = [<span class="id" type="var">e</span>;<span
class="id" type="var">f</span>] <span
style="font-family: arial;">→</span>\
      [<span class="id" type="var">a</span>;<span class="id"
type="var">b</span>] = [<span class="id" type="var">e</span>;<span
class="id" type="var">f</span>].\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">a</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span> <span class="id" type="var">d</span>
<span class="id" type="var">e</span> <span class="id"
type="var">f</span> <span class="id" type="var">eq1</span> <span
class="id" type="var">eq2</span>.\
   <span class="comment">(\* If we simply tell Coq <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
<span class="inlinecode"><span class="id"
type="var">trans\_eq</span></span> at this point,\
      it can tell (by matching the goal against the\
      conclusion of the lemma) that it should instantiate <span
class="inlinecode"><span class="id" type="var">X</span></span>\
      with <span class="inlinecode">[<span class="id"
type="var">nat</span>]</span>, <span class="inlinecode"><span class="id"
type="var">n</span></span> with <span class="inlinecode">[<span
class="id" type="var">a</span>,<span class="id"
type="var">b</span>]</span>, and <span class="inlinecode"><span
class="id" type="var">o</span></span> with <span
class="inlinecode">[<span class="id" type="var">e</span>,<span
class="id" type="var">f</span>]</span>.\
      However, the matching process doesn't determine an\
      instantiation for <span class="inlinecode"><span class="id"
type="var">m</span></span>: we have to supply one explicitly\
      by adding <span class="inlinecode"><span class="id"
type="keyword">with</span></span> <span class="inlinecode">(<span
class="id" type="var">m</span>:=[<span class="id"
type="var">c</span>,<span class="id"
type="var">d</span>])</span> to the invocation of\
      <span class="inlinecode"><span class="id"
type="tactic">apply</span></span>. \*)</span>\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">trans\_eq</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">m</span>:=[<span class="id"
type="var">c</span>;<span class="id" type="var">d</span>]). <span
class="id" type="tactic">apply</span> <span class="id"
type="var">eq1</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">eq2</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Actually, we usually don't have to include the name <span
class="inlinecode"><span class="id" type="var">m</span></span> in the
<span class="inlinecode"><span class="id"
type="keyword">with</span></span> clause; Coq is often smart enough to
figure out which instantiation we're giving. We could instead write:
<span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">trans\_eq</span></span> <span
class="inlinecode"><span class="id" type="keyword">with</span></span>
<span class="inlinecode">[<span class="id" type="var">c</span>,<span
class="id" type="var">d</span>]</span>.
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (apply\_with\_exercise) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">trans\_eq\_exercise</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">o</span> <span class="id" type="var">p</span> :
<span class="id" type="var">nat</span>),\
      <span class="id" type="var">m</span> = (<span class="id"
type="var">minustwo</span> <span class="id" type="var">o</span>) <span
style="font-family: arial;">→</span>\
      (<span class="id" type="var">n</span> + <span class="id"
type="var">p</span>) = <span class="id" type="var">m</span> <span
style="font-family: arial;">→</span>\
      (<span class="id" type="var">n</span> + <span class="id"
type="var">p</span>) = (<span class="id" type="var">minustwo</span>
<span class="id" type="var">o</span>).\
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

The <span class="inlinecode"><span class="id" type="tactic">inversion</span></span> tactic {.section}
==========================================================================================

<div class="paragraph">

</div>

Recall the definition of natural numbers:
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">nat</span> : <span class="id" type="keyword">Type</span> :=\
        | <span class="id" type="var">O</span> : <span class="id"
type="var">nat</span>\
        | <span class="id" type="var">S</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">nat</span>.
<div class="paragraph">

</div>

</div>

It is clear from this definition that every number has one of two forms:
either it is the constructor <span class="inlinecode"><span class="id"
type="var">O</span></span> or it is built by applying the constructor
<span class="inlinecode"><span class="id" type="var">S</span></span> to
another number. But there is more here than meets the eye: implicit in
the definition (and in our informal understanding of how datatype
declarations work in other programming languages) are two other facts:
<div class="paragraph">

</div>

-   The constructor <span class="inlinecode"><span class="id"
    type="var">S</span></span> is *injective*. That is, the only way we
    can have <span class="inlinecode"><span class="id"
    type="var">S</span></span> <span class="inlinecode"><span class="id"
    type="var">n</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">S</span></span> <span
    class="inlinecode"><span class="id" type="var">m</span></span> is if
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">m</span></span>.
    <div class="paragraph">

    </div>

-   The constructors <span class="inlinecode"><span class="id"
    type="var">O</span></span> and <span class="inlinecode"><span
    class="id" type="var">S</span></span> are *disjoint*. That is, <span
    class="inlinecode"><span class="id" type="var">O</span></span> is
    not equal to <span class="inlinecode"><span class="id"
    type="var">S</span></span> <span class="inlinecode"><span class="id"
    type="var">n</span></span> for any <span class="inlinecode"><span
    class="id" type="var">n</span></span>.

<div class="paragraph">

</div>

Similar principles apply to all inductively defined types: all
constructors are injective, and the values built from distinct
constructors are never equal. For lists, the <span
class="inlinecode"><span class="id" type="var">cons</span></span>
constructor is injective and <span class="inlinecode"><span class="id"
type="var">nil</span></span> is different from every non-empty list. For
booleans, <span class="inlinecode"><span class="id"
type="var">true</span></span> and <span class="inlinecode"><span
class="id" type="var">false</span></span> are unequal. (Since neither
<span class="inlinecode"><span class="id" type="var">true</span></span>
nor <span class="inlinecode"><span class="id"
type="var">false</span></span> take any arguments, their injectivity is
not an issue.)
<div class="paragraph">

</div>

Coq provides a tactic called <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> that allows us to exploit these
principles in proofs.
<div class="paragraph">

</div>

The <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> tactic is used like this. Suppose
<span class="inlinecode"><span class="id" type="var">H</span></span> is
a hypothesis in the context (or a previously proven lemma) of the form
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">c</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ... <span
class="id" type="var">an</span> = <span class="id"
type="var">d</span> <span class="id" type="var">b1</span> <span
class="id" type="var">b2</span> ... <span class="id"
type="var">bm</span>
<div class="paragraph">

</div>

</div>

for some constructors <span class="inlinecode"><span class="id"
type="var">c</span></span> and <span class="inlinecode"><span class="id"
type="var">d</span></span> and arguments <span class="inlinecode"><span
class="id" type="var">a1</span></span> <span
class="inlinecode">...</span> <span class="inlinecode"><span class="id"
type="var">an</span></span> and <span class="inlinecode"><span
class="id" type="var">b1</span></span> <span
class="inlinecode">...</span> <span class="inlinecode"><span class="id"
type="var">bm</span></span>. Then <span class="inlinecode"><span
class="id" type="tactic">inversion</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span> instructs
Coq to "invert" this equality to extract the information it contains
about these terms:
<div class="paragraph">

</div>

-   If <span class="inlinecode"><span class="id"
    type="var">c</span></span> and <span class="inlinecode"><span
    class="id" type="var">d</span></span> are the same constructor, then
    we know, by the injectivity of this constructor, that <span
    class="inlinecode"><span class="id" type="var">a1</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">b1</span></span>, <span
    class="inlinecode"><span class="id" type="var">a2</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">b2</span></span>, etc.; <span
    class="inlinecode"><span class="id"
    type="tactic">inversion</span></span> <span class="inlinecode"><span
    class="id" type="var">H</span></span> adds these facts to the
    context, and tries to use them to rewrite the goal.
    <div class="paragraph">

    </div>

-   If <span class="inlinecode"><span class="id"
    type="var">c</span></span> and <span class="inlinecode"><span
    class="id" type="var">d</span></span> are different constructors,
    then the hypothesis <span class="inlinecode"><span class="id"
    type="var">H</span></span> is contradictory. That is, a false
    assumption has crept into the context, and this means that any goal
    whatsoever is provable! In this case, <span class="inlinecode"><span
    class="id" type="tactic">inversion</span></span> <span
    class="inlinecode"><span class="id" type="var">H</span></span> marks
    the current goal as completed and pops it off the goal stack.

<div class="paragraph">

</div>

The <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> tactic is probably easier to
understand by seeing it in action than from general descriptions like
the above. Below you will find example theorems that demonstrate the use
of <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> and exercises to test your
understanding.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">eq\_add\_S</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> <span class="id" type="var">m</span> : <span
class="id" type="var">nat</span>),\
      <span class="id" type="var">S</span> <span class="id"
type="var">n</span> = <span class="id" type="var">S</span> <span
class="id" type="var">m</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">n</span> = <span class="id"
type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">eq</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">eq</span>.
<span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">silly4</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> <span class="id" type="var">m</span> : <span
class="id" type="var">nat</span>),\
      [<span class="id" type="var">n</span>] = [<span class="id"
type="var">m</span>] <span style="font-family: arial;">→</span>\
      <span class="id" type="var">n</span> = <span class="id"
type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">o</span> <span
class="id" type="var">eq</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">eq</span>.
<span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

As a convenience, the <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> tactic can also destruct
equalities between complex values, binding multiple variables as it
goes.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">silly5</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">o</span> : <span class="id"
type="var">nat</span>),\
      [<span class="id" type="var">n</span>;<span class="id"
type="var">m</span>] = [<span class="id" type="var">o</span>;<span
class="id" type="var">o</span>] <span
style="font-family: arial;">→</span>\
      [<span class="id" type="var">n</span>] = [<span class="id"
type="var">m</span>].\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">o</span> <span class="id" type="var">eq</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">eq</span>. <span class="id" type="tactic">reflexivity</span>.
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star (sillyex1) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">sillyex1</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> : <span class="id" type="keyword">Type</span>)
(<span class="id" type="var">x</span> <span class="id"
type="var">y</span> <span class="id" type="var">z</span> : <span
class="id" type="var">X</span>) (<span class="id" type="var">l</span>
<span class="id" type="var">j</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span>),\
      <span class="id" type="var">x</span> :: <span class="id"
type="var">y</span> :: <span class="id" type="var">l</span> = <span
class="id" type="var">z</span> :: <span class="id" type="var">j</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">y</span> :: <span class="id"
type="var">l</span> = <span class="id" type="var">x</span> :: <span
class="id" type="var">j</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">x</span> = <span class="id"
type="var">y</span>.\
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
type="var">silly6</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>),\
      <span class="id" type="var">S</span> <span class="id"
type="var">n</span> = <span class="id" type="var">O</span> <span
style="font-family: arial;">→</span>\
      2 + 2 = 5.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">contra</span>. <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">contra</span>. <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">silly7</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> <span class="id" type="var">m</span> : <span
class="id" type="var">nat</span>),\
      <span class="id" type="var">false</span> = <span class="id"
type="var">true</span> <span style="font-family: arial;">→</span>\
      [<span class="id" type="var">n</span>] = [<span class="id"
type="var">m</span>].\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">contra</span>. <span class="id"
type="tactic">inversion</span> <span class="id"
type="var">contra</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star (sillyex2) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">sillyex2</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> : <span class="id" type="keyword">Type</span>)
(<span class="id" type="var">x</span> <span class="id"
type="var">y</span> <span class="id" type="var">z</span> : <span
class="id" type="var">X</span>) (<span class="id" type="var">l</span>
<span class="id" type="var">j</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span>),\
      <span class="id" type="var">x</span> :: <span class="id"
type="var">y</span> :: <span class="id" type="var">l</span> = [] <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">y</span> :: <span class="id"
type="var">l</span> = <span class="id" type="var">z</span> :: <span
class="id" type="var">j</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">x</span> = <span class="id"
type="var">z</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

While the injectivity of constructors allows us to reason <span
class="inlinecode"><span style="font-family: arial;">∀</span></span>
<span class="inlinecode">(<span class="id" type="var">n</span></span>
<span class="inlinecode"><span class="id" type="var">m</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">nat</span>),</span> <span class="inlinecode"><span
class="id" type="var">S</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">S</span></span>
<span class="inlinecode"><span class="id" type="var">m</span></span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">m</span></span>, the reverse direction of the implication is
an instance of a more general fact about constructors and functions,
which we will often find useful:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="tactic">f\_equal</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">A</span> <span class="id" type="var">B</span> : <span
class="id" type="keyword">Type</span>) (<span class="id"
type="var">f</span>: <span class="id" type="var">A</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">B</span>) (<span class="id" type="var">x</span> <span
class="id" type="var">y</span>: <span class="id" type="var">A</span>),\
     <span class="id" type="var">x</span> = <span class="id"
type="var">y</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">f</span> <span class="id" type="var">x</span> =
<span class="id" type="var">f</span> <span class="id"
type="var">y</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">A</span> <span
class="id" type="var">B</span> <span class="id" type="var">f</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y</span> <span class="id" type="var">eq</span>. <span
class="id" type="tactic">rewrite</span> <span class="id"
type="var">eq</span>. <span class="id" type="tactic">reflexivity</span>.
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (practice) {.section}

A couple more nontrivial but not-too-complicated proofs to work together
in class, or for you to work as exercises.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">beq\_nat\_0\_l</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
    <span class="id" type="var">beq\_nat</span> 0 <span class="id"
type="var">n</span> = <span class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> = 0.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">beq\_nat\_0\_r</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
    <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> 0 = <span class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> = 0.\
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

Using Tactics on Hypotheses {.section}
===========================

<div class="paragraph">

</div>

By default, most tactics work on the goal formula and leave the context
unchanged. However, most tactics also have a variant that performs a
similar operation on a statement in the context.
<div class="paragraph">

</div>

For example, the tactic <span class="inlinecode"><span class="id"
type="tactic">simpl</span></span> <span class="inlinecode"><span
class="id" type="keyword">in</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span> performs
simplification in the hypothesis named <span class="inlinecode"><span
class="id" type="var">H</span></span> in the context.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">S\_inj</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> <span class="id" type="var">m</span> : <span
class="id" type="var">nat</span>) (<span class="id" type="var">b</span>
: <span class="id" type="var">bool</span>),\
      <span class="id" type="var">beq\_nat</span> (<span class="id"
type="var">S</span> <span class="id" type="var">n</span>) (<span
class="id" type="var">S</span> <span class="id" type="var">m</span>) =
<span class="id" type="var">b</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">b</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">b</span> <span class="id" type="var">H</span>.
<span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">H</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Similarly, the tactic <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">L</span></span> <span class="inlinecode"><span
class="id" type="keyword">in</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span> matches
some conditional statement <span class="inlinecode"><span class="id"
type="var">L</span></span> (of the form <span class="inlinecode"><span
class="id" type="var">L1</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">L2</span></span>, say)
against a hypothesis <span class="inlinecode"><span class="id"
type="var">H</span></span> in the context. However, unlike ordinary
<span class="inlinecode"><span class="id"
type="tactic">apply</span></span> (which rewrites a goal matching <span
class="inlinecode"><span class="id" type="var">L2</span></span> into a
subgoal <span class="inlinecode"><span class="id"
type="var">L1</span></span>), <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">L</span></span> <span class="inlinecode"><span
class="id" type="keyword">in</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span> matches
<span class="inlinecode"><span class="id" type="var">H</span></span>
against <span class="inlinecode"><span class="id"
type="var">L1</span></span> and, if successful, replaces it with <span
class="inlinecode"><span class="id" type="var">L2</span></span>.
<div class="paragraph">

</div>

In other words, <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">L</span></span> <span class="inlinecode"><span
class="id" type="keyword">in</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span> gives us
a form of "forward reasoning" — from <span class="inlinecode"><span
class="id" type="var">L1</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">L2</span></span> and a
hypothesis matching <span class="inlinecode"><span class="id"
type="var">L1</span></span>, it gives us a hypothesis matching <span
class="inlinecode"><span class="id" type="var">L2</span></span>. By
contrast, <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">L</span></span> is "backward reasoning" — it says
that if we know <span class="inlinecode"><span class="id"
type="var">L1</span><span style="font-family: arial;">→</span><span
class="id" type="var">L2</span></span> and we are trying to prove <span
class="inlinecode"><span class="id" type="var">L2</span></span>, it
suffices to prove <span class="inlinecode"><span class="id"
type="var">L1</span></span>.
<div class="paragraph">

</div>

Here is a variant of a proof from above, using forward reasoning
throughout instead of backward reasoning.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">silly3'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>),\
   (<span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> 5 = <span class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">beq\_nat</span> (<span class="id" type="var">S</span> (<span
class="id" type="var">S</span> <span class="id" type="var">n</span>)) 7
= <span class="id" type="var">true</span>) <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">true</span> = <span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n</span> 5 <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">true</span> = <span class="id"
type="var">beq\_nat</span> (<span class="id" type="var">S</span> (<span
class="id" type="var">S</span> <span class="id" type="var">n</span>))
7.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">eq</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">symmetry</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">eq</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">symmetry</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">H</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Forward reasoning starts from what is *given* (premises, previously
proven theorems) and iteratively draws conclusions from them until the
goal is reached. Backward reasoning starts from the *goal*, and
iteratively reasons about what would imply the goal, until premises or
previously proven theorems are reached. If you've seen informal proofs
before (for example, in a math or computer science class), they probably
used forward reasoning. In general, Coq tends to favor backward
reasoning, but in some situations the forward style can be easier to use
or to think about.
<div class="paragraph">

</div>

#### Exercise: 3 stars (plus\_n\_n\_injective) {.section}

Practice using "in" variants in this exercise.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">plus\_n\_n\_injective</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
      <span class="id" type="var">n</span> + <span class="id"
type="var">n</span> = <span class="id" type="var">m</span> + <span
class="id" type="var">m</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">n</span> = <span class="id"
type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span>. <span class="id" type="tactic">induction</span>
<span class="id" type="var">n</span> <span class="id"
type="keyword">as</span> [| <span class="id" type="var">n'</span>].\
     <span
class="comment">(\* Hint: use the plus\_n\_Sm lemma \*)</span>\
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

Varying the Induction Hypothesis {.section}
================================

<div class="paragraph">

</div>

Sometimes it is important to control the exact form of the induction
hypothesis when carrying out inductive proofs in Coq. In particular, we
need to be careful about which of the assumptions we move (using <span
class="inlinecode"><span class="id" type="tactic">intros</span></span>)
from the goal to the context before invoking the <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> tactic. For example, suppose we
want to show that the <span class="inlinecode"><span class="id"
type="var">double</span></span> function is injective — i.e., that it
always maps different arguments to different results:
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">double\_injective</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span> <span class="id" type="var">m</span>, <span
class="id" type="var">double</span> <span class="id"
type="var">n</span> = <span class="id" type="var">double</span> <span
class="id" type="var">m</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> = <span class="id" type="var">m</span>.
<div class="paragraph">

</div>

</div>

The way we *start* this proof is a little bit delicate: if we begin it
with
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">n</span>.
<div class="paragraph">

</div>

</div>

all is well. But if we begin it with
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span>. <span
class="id" type="tactic">induction</span> <span class="id"
type="var">n</span>.
<div class="paragraph">

</div>

</div>

we get stuck in the middle of the inductive case...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">double\_injective\_FAILED</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
      <span class="id" type="var">double</span> <span class="id"
type="var">n</span> = <span class="id" type="var">double</span> <span
class="id" type="var">m</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">n</span> = <span class="id"
type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span>. <span
class="id" type="tactic">induction</span> <span class="id"
type="var">n</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">n'</span>].\
   <span class="id" type="var">Case</span> "n = O". <span class="id"
type="tactic">simpl</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">eq</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">m</span> <span
class="id" type="keyword">as</span> [| <span class="id"
type="var">m'</span>].\
     <span class="id" type="var">SCase</span> "m = O". <span class="id"
type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> "m = S m'". <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">eq</span>.\
   <span class="id" type="var">Case</span> "n = S n'". <span class="id"
type="tactic">intros</span> <span class="id" type="var">eq</span>. <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">m</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">m'</span>].\
     <span class="id" type="var">SCase</span> "m = O". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">eq</span>.\
     <span class="id" type="var">SCase</span> "m = S m'". <span
class="id" type="tactic">apply</span> <span class="id"
type="tactic">f\_equal</span>.\
       <span
class="comment">(\* Here we are stuck.  The induction hypothesis, <span
class="inlinecode"><span class="id" type="var">IHn'</span></span>, does\
          not give us <span class="inlinecode"><span class="id"
type="var">n'</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id"
type="var">m'</span></span> -- there is an extra <span
class="inlinecode"><span class="id" type="var">S</span></span> in the\
          way -- so the goal is not provable. \*)</span>\
       <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

What went wrong?
<div class="paragraph">

</div>

The problem is that, at the point we invoke the induction hypothesis, we
have already introduced <span class="inlinecode"><span class="id"
type="var">m</span></span> into the context — intuitively, we have told
Coq, "Let's consider some particular <span class="inlinecode"><span
class="id" type="var">n</span></span> and <span class="inlinecode"><span
class="id" type="var">m</span></span>..." and we now have to prove that,
if <span class="inlinecode"><span class="id"
type="var">double</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">double</span></span> <span class="inlinecode"><span
class="id" type="var">m</span></span> for *this particular* <span
class="inlinecode"><span class="id" type="var">n</span></span> and <span
class="inlinecode"><span class="id" type="var">m</span></span>, then
<span class="inlinecode"><span class="id" type="var">n</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">m</span></span>.
<div class="paragraph">

</div>

The next tactic, <span class="inlinecode"><span class="id"
type="tactic">induction</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> says to Coq: We are going to show
the goal by induction on <span class="inlinecode"><span class="id"
type="var">n</span></span>. That is, we are going to prove that the
proposition
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">P</span></span>
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    = "if <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">double</span></span> <span
    class="inlinecode"><span class="id" type="var">m</span></span>, then
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">m</span></span>"

<div class="paragraph">

</div>

holds for all <span class="inlinecode"><span class="id"
type="var">n</span></span> by showing
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">P</span></span>
    <span class="inlinecode"><span class="id" type="var">O</span></span>
    <div class="paragraph">

    </div>

    (i.e., "if <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">O</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">double</span></span> <span
    class="inlinecode"><span class="id" type="var">m</span></span> then
    <span class="inlinecode"><span class="id" type="var">O</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">m</span></span>")
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id" type="var">P</span></span>
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode">(<span class="id" type="var">S</span></span>
    <span class="inlinecode"><span class="id"
    type="var">n</span>)</span>
    <div class="paragraph">

    </div>

    (i.e., "if <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">double</span></span> <span
    class="inlinecode"><span class="id" type="var">m</span></span> then
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">m</span></span>" implies "if <span
    class="inlinecode"><span class="id" type="var">double</span></span>
    <span class="inlinecode">(<span class="id"
    type="var">S</span></span> <span class="inlinecode"><span class="id"
    type="var">n</span>)</span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">double</span></span>
    <span class="inlinecode"><span class="id" type="var">m</span></span>
    then <span class="inlinecode"><span class="id"
    type="var">S</span></span> <span class="inlinecode"><span class="id"
    type="var">n</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">m</span></span>").

<div class="paragraph">

</div>

If we look closely at the second statement, it is saying something
rather strange: it says that, for a *particular* <span
class="inlinecode"><span class="id" type="var">m</span></span>, if we
know
<div class="paragraph">

</div>

-   "if <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">double</span></span> <span
    class="inlinecode"><span class="id" type="var">m</span></span> then
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">m</span></span>"

<div class="paragraph">

</div>

then we can prove
<div class="paragraph">

</div>

-   "if <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode">(<span
    class="id" type="var">S</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span>)</span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">double</span></span> <span
    class="inlinecode"><span class="id" type="var">m</span></span> then
    <span class="inlinecode"><span class="id" type="var">S</span></span>
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">m</span></span>".

<div class="paragraph">

</div>

To see why this is strange, let's think of a particular <span
class="inlinecode"><span class="id" type="var">m</span></span> — say,
<span class="inlinecode">5</span>. The statement is then saying that, if
we know
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">Q</span></span>
    = "if <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode">10</span> then
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode">5</span>"

<div class="paragraph">

</div>

then we can prove
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">R</span></span>
    = "if <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode">(<span
    class="id" type="var">S</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span>)</span> <span
    class="inlinecode">=</span> <span class="inlinecode">10</span> then
    <span class="inlinecode"><span class="id" type="var">S</span></span>
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    <span class="inlinecode">=</span> <span
    class="inlinecode">5</span>".

<div class="paragraph">

</div>

But knowing <span class="inlinecode"><span class="id"
type="var">Q</span></span> doesn't give us any help with proving <span
class="inlinecode"><span class="id" type="var">R</span></span>! (If we
tried to prove <span class="inlinecode"><span class="id"
type="var">R</span></span> from <span class="inlinecode"><span
class="id" type="var">Q</span></span>, we would say something like
"Suppose <span class="inlinecode"><span class="id"
type="var">double</span></span> <span class="inlinecode">(<span
class="id" type="var">S</span></span> <span class="inlinecode"><span
class="id" type="var">n</span>)</span> <span class="inlinecode">=</span>
<span class="inlinecode">10</span>..." but then we'd be stuck: knowing
that <span class="inlinecode"><span class="id"
type="var">double</span></span> <span class="inlinecode">(<span
class="id" type="var">S</span></span> <span class="inlinecode"><span
class="id" type="var">n</span>)</span> is <span
class="inlinecode">10</span> tells us nothing about whether <span
class="inlinecode"><span class="id" type="var">double</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span> is
<span class="inlinecode">10</span>, so <span class="inlinecode"><span
class="id" type="var">Q</span></span> is useless at this point.)
<div class="paragraph">

</div>

To summarize: Trying to carry out this proof by induction on <span
class="inlinecode"><span class="id" type="var">n</span></span> when
<span class="inlinecode"><span class="id" type="var">m</span></span> is
already in the context doesn't work because we are trying to prove a
relation involving *every* <span class="inlinecode"><span class="id"
type="var">n</span></span> but just a *single* <span
class="inlinecode"><span class="id" type="var">m</span></span>.
<div class="paragraph">

</div>

The good proof of <span class="inlinecode"><span class="id"
type="var">double\_injective</span></span> leaves <span
class="inlinecode"><span class="id" type="var">m</span></span> in the
goal statement at the point where the <span class="inlinecode"><span
class="id" type="tactic">induction</span></span> tactic is invoked on
<span class="inlinecode"><span class="id" type="var">n</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">double\_injective</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
      <span class="id" type="var">double</span> <span class="id"
type="var">n</span> = <span class="id" type="var">double</span> <span
class="id" type="var">m</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">n</span> = <span class="id"
type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span>. <span class="id" type="tactic">induction</span>
<span class="id" type="var">n</span> <span class="id"
type="keyword">as</span> [| <span class="id" type="var">n'</span>].\
   <span class="id" type="var">Case</span> "n = O". <span class="id"
type="tactic">simpl</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">m</span> <span class="id"
type="var">eq</span>. <span class="id" type="tactic">destruct</span>
<span class="id" type="var">m</span> <span class="id"
type="keyword">as</span> [| <span class="id" type="var">m'</span>].\
     <span class="id" type="var">SCase</span> "m = O". <span class="id"
type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> "m = S m'". <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">eq</span>.\
   <span class="id" type="var">Case</span> "n = S n'".\
     <span
class="comment">(\* Notice that both the goal and the induction\
        hypothesis have changed: the goal asks us to prove\
        something more general (i.e., to prove the\
        statement for \_every\_ <span class="inlinecode"><span
class="id" type="var">m</span></span>), but the IH is\
        correspondingly more flexible, allowing us to\
        choose any <span class="inlinecode"><span class="id"
type="var">m</span></span> we like when we apply the IH.  \*)</span>\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">m</span> <span class="id" type="var">eq</span>.\
     <span class="comment">(\* Now we choose a particular <span
class="inlinecode"><span class="id"
type="var">m</span></span> and introduce the\
        assumption that <span class="inlinecode"><span class="id"
type="var">double</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">double</span></span> <span class="inlinecode"><span
class="id" type="var">m</span></span>.  Since we\
        are doing a case analysis on <span class="inlinecode"><span
class="id" type="var">n</span></span>, we need a case\
        analysis on <span class="inlinecode"><span class="id"
type="var">m</span></span> to keep the two "in sync." \*)</span>\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">m</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">m'</span>].\
     <span class="id" type="var">SCase</span> "m = O".\
       <span class="comment">(\* The 0 case is trivial \*)</span>\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">eq</span>.\
     <span class="id" type="var">SCase</span> "m = S m'".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="tactic">f\_equal</span>.\
       <span
class="comment">(\* At this point, since we are in the second\
          branch of the <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> <span class="inlinecode"><span
class="id" type="var">m</span></span>, the <span
class="inlinecode"><span class="id"
type="var">m'</span></span> mentioned\
          in the context at this point is actually the\
          predecessor of the one we started out talking\
          about.  Since we are also in the <span
class="inlinecode"><span class="id"
type="var">S</span></span> branch of\
          the induction, this is perfect: if we\
          instantiate the generic <span class="inlinecode"><span
class="id" type="var">m</span></span> in the IH with the\
          <span class="inlinecode"><span class="id"
type="var">m'</span></span> that we are talking about right now (this\
          instantiation is performed automatically by\
          <span class="inlinecode"><span class="id"
type="tactic">apply</span></span>), then <span class="inlinecode"><span
class="id" type="var">IHn'</span></span> gives us exactly what we\
          need to finish the proof. \*)</span>\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHn'</span>. <span class="id" type="tactic">inversion</span>
<span class="id" type="var">eq</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

What this teaches us is that we need to be careful about using induction
to try to prove something too specific: If we're proving a property of
<span class="inlinecode"><span class="id" type="var">n</span></span> and
<span class="inlinecode"><span class="id" type="var">m</span></span> by
induction on <span class="inlinecode"><span class="id"
type="var">n</span></span>, we may need to leave <span
class="inlinecode"><span class="id" type="var">m</span></span> generic.
<div class="paragraph">

</div>

The proof of this theorem (left as an exercise) has to be treated
similarly:
<div class="paragraph">

</div>

#### Exercise: 2 stars (beq\_nat\_true) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">beq\_nat\_true</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
     <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> = <span class="id" type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, advanced (beq\_nat\_true\_informal) {.section}

Give a careful informal proof of <span class="inlinecode"><span
class="id" type="var">beq\_nat\_true</span></span>, being as explicit as
possible about quantifiers.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

The strategy of doing fewer <span class="inlinecode"><span class="id"
type="tactic">intros</span></span> before an <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> doesn't always work directly;
sometimes a little *rearrangement* of quantified variables is needed.
Suppose, for example, that we wanted to prove <span
class="inlinecode"><span class="id"
type="var">double\_injective</span></span> by induction on <span
class="inlinecode"><span class="id" type="var">m</span></span> instead
of <span class="inlinecode"><span class="id" type="var">n</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">double\_injective\_take2\_FAILED</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
      <span class="id" type="var">double</span> <span class="id"
type="var">n</span> = <span class="id" type="var">double</span> <span
class="id" type="var">m</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">n</span> = <span class="id"
type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span>. <span
class="id" type="tactic">induction</span> <span class="id"
type="var">m</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">m'</span>].\
   <span class="id" type="var">Case</span> "m = O". <span class="id"
type="tactic">simpl</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">eq</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">n</span> <span
class="id" type="keyword">as</span> [| <span class="id"
type="var">n'</span>].\
     <span class="id" type="var">SCase</span> "n = O". <span class="id"
type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> "n = S n'". <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">eq</span>.\
   <span class="id" type="var">Case</span> "m = S m'". <span class="id"
type="tactic">intros</span> <span class="id" type="var">eq</span>. <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">n</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">n'</span>].\
     <span class="id" type="var">SCase</span> "n = O". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">eq</span>.\
     <span class="id" type="var">SCase</span> "n = S n'". <span
class="id" type="tactic">apply</span> <span class="id"
type="tactic">f\_equal</span>.\
         <span
class="comment">(\* Stuck again here, just like before. \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

The problem is that, to do induction on <span class="inlinecode"><span
class="id" type="var">m</span></span>, we must first introduce <span
class="inlinecode"><span class="id" type="var">n</span></span>. (If we
simply say <span class="inlinecode"><span class="id"
type="tactic">induction</span></span> <span class="inlinecode"><span
class="id" type="var">m</span></span> without introducing anything
first, Coq will automatically introduce <span class="inlinecode"><span
class="id" type="var">n</span></span> for us!)
<div class="paragraph">

</div>

What can we do about this? One possibility is to rewrite the statement
of the lemma so that <span class="inlinecode"><span class="id"
type="var">m</span></span> is quantified before <span
class="inlinecode"><span class="id" type="var">n</span></span>. This
will work, but it's not nice: We don't want to have to mangle the
statements of lemmas to fit the needs of a particular strategy for
proving them — we want to state them in the most clear and natural way.
<div class="paragraph">

</div>

What we can do instead is to first introduce all the quantified
variables and then *re-generalize* one or more of them, taking them out
of the context and putting them back at the beginning of the goal. The
<span class="inlinecode"><span class="id"
type="tactic">generalize</span></span> <span class="inlinecode"><span
class="id" type="tactic">dependent</span></span> tactic does this.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">double\_injective\_take2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
      <span class="id" type="var">double</span> <span class="id"
type="var">n</span> = <span class="id" type="var">double</span> <span
class="id" type="var">m</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">n</span> = <span class="id"
type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span>.\
   <span class="comment">(\* <span class="inlinecode"><span class="id"
type="var">n</span></span> and <span class="inlinecode"><span class="id"
type="var">m</span></span> are both in the context \*)</span>\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">n</span>.\
   <span class="comment">(\* Now <span class="inlinecode"><span
class="id"
type="var">n</span></span> is back in the goal and we can do induction on\
      <span class="inlinecode"><span class="id"
type="var">m</span></span> and get a sufficiently general IH. \*)</span>\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">m</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">m'</span>].\
   <span class="id" type="var">Case</span> "m = O". <span class="id"
type="tactic">simpl</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">n</span> <span class="id"
type="var">eq</span>. <span class="id" type="tactic">destruct</span>
<span class="id" type="var">n</span> <span class="id"
type="keyword">as</span> [| <span class="id" type="var">n'</span>].\
     <span class="id" type="var">SCase</span> "n = O". <span class="id"
type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> "n = S n'". <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">eq</span>.\
   <span class="id" type="var">Case</span> "m = S m'". <span class="id"
type="tactic">intros</span> <span class="id" type="var">n</span> <span
class="id" type="var">eq</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">n</span> <span
class="id" type="keyword">as</span> [| <span class="id"
type="var">n'</span>].\
     <span class="id" type="var">SCase</span> "n = O". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">eq</span>.\
     <span class="id" type="var">SCase</span> "n = S n'". <span
class="id" type="tactic">apply</span> <span class="id"
type="tactic">f\_equal</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHm'</span>. <span class="id" type="tactic">inversion</span>
<span class="id" type="var">eq</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Let's look at an informal proof of this theorem. Note that the
proposition we prove by induction leaves <span class="inlinecode"><span
class="id" type="var">n</span></span> quantified, corresponding to the
use of generalize dependent in our formal proof.
<div class="paragraph">

</div>

*Theorem*: For any nats <span class="inlinecode"><span class="id"
type="var">n</span></span> and <span class="inlinecode"><span class="id"
type="var">m</span></span>, if <span class="inlinecode"><span class="id"
type="var">double</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">double</span></span> <span class="inlinecode"><span
class="id" type="var">m</span></span>, then <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">m</span></span>.
<div class="paragraph">

</div>

*Proof*: Let <span class="inlinecode"><span class="id"
type="var">m</span></span> be a <span class="inlinecode"><span
class="id" type="var">nat</span></span>. We prove by induction on <span
class="inlinecode"><span class="id" type="var">m</span></span> that, for
any <span class="inlinecode"><span class="id"
type="var">n</span></span>, if <span class="inlinecode"><span class="id"
type="var">double</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">double</span></span> <span class="inlinecode"><span
class="id" type="var">m</span></span> then <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">m</span></span>.
<div class="paragraph">

</div>

-   First, suppose <span class="inlinecode"><span class="id"
    type="var">m</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode">0</span>, and suppose <span
    class="inlinecode"><span class="id" type="var">n</span></span> is a
    number such that <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">double</span></span> <span
    class="inlinecode"><span class="id" type="var">m</span></span>. We
    must show that <span class="inlinecode"><span class="id"
    type="var">n</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode">0</span>.
    <div class="paragraph">

    </div>

    Since <span class="inlinecode"><span class="id"
    type="var">m</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode">0</span>, by the definition of <span
    class="inlinecode"><span class="id" type="var">double</span></span>
    we have <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode">0</span>. There
    are two cases to consider for <span class="inlinecode"><span
    class="id" type="var">n</span></span>. If <span
    class="inlinecode"><span class="id" type="var">n</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode">0</span> we are
    done, since this is what we wanted to show. Otherwise, if <span
    class="inlinecode"><span class="id" type="var">n</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">S</span></span> <span class="inlinecode"><span
    class="id" type="var">n'</span></span> for some <span
    class="inlinecode"><span class="id" type="var">n'</span></span>, we
    derive a contradiction: by the definition of <span
    class="inlinecode"><span class="id" type="var">double</span></span>
    we would have <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">S</span></span> <span
    class="inlinecode">(<span class="id" type="var">S</span></span>
    <span class="inlinecode">(<span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">n'</span>))</span>, but this contradicts the
    assumption that <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode">0</span>.
    <div class="paragraph">

    </div>

-   Otherwise, suppose <span class="inlinecode"><span class="id"
    type="var">m</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">S</span></span> <span
    class="inlinecode"><span class="id" type="var">m'</span></span> and
    that <span class="inlinecode"><span class="id"
    type="var">n</span></span> is again a number such that <span
    class="inlinecode"><span class="id" type="var">double</span></span>
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">double</span></span> <span
    class="inlinecode"><span class="id" type="var">m</span></span>. We
    must show that <span class="inlinecode"><span class="id"
    type="var">n</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">S</span></span> <span
    class="inlinecode"><span class="id" type="var">m'</span></span>,
    with the induction hypothesis that for every number <span
    class="inlinecode"><span class="id" type="var">s</span></span>, if
    <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">s</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">double</span></span> <span
    class="inlinecode"><span class="id" type="var">m'</span></span> then
    <span class="inlinecode"><span class="id" type="var">s</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">m'</span></span>.
    <div class="paragraph">

    </div>

    By the fact that <span class="inlinecode"><span class="id"
    type="var">m</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">S</span></span> <span
    class="inlinecode"><span class="id" type="var">m'</span></span> and
    the definition of <span class="inlinecode"><span class="id"
    type="var">double</span></span>, we have <span
    class="inlinecode"><span class="id" type="var">double</span></span>
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">S</span></span> <span
    class="inlinecode">(<span class="id" type="var">S</span></span>
    <span class="inlinecode">(<span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">m'</span>))</span>. There are two cases to
    consider for <span class="inlinecode"><span class="id"
    type="var">n</span></span>.
    <div class="paragraph">

    </div>

    If <span class="inlinecode"><span class="id"
    type="var">n</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode">0</span>, then by definition <span
    class="inlinecode"><span class="id" type="var">double</span></span>
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode">0</span>,
    a contradiction. Thus, we may assume that <span
    class="inlinecode"><span class="id" type="var">n</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">S</span></span> <span class="inlinecode"><span
    class="id" type="var">n'</span></span> for some <span
    class="inlinecode"><span class="id" type="var">n'</span></span>, and
    again by the definition of <span class="inlinecode"><span class="id"
    type="var">double</span></span> we have <span
    class="inlinecode"><span class="id" type="var">S</span></span> <span
    class="inlinecode">(<span class="id" type="var">S</span></span>
    <span class="inlinecode">(<span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">n'</span>))</span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">S</span></span> <span
    class="inlinecode">(<span class="id" type="var">S</span></span>
    <span class="inlinecode">(<span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">m'</span>))</span>, which implies by inversion
    that <span class="inlinecode"><span class="id"
    type="var">double</span></span> <span class="inlinecode"><span
    class="id" type="var">n'</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">double</span></span> <span
    class="inlinecode"><span class="id" type="var">m'</span></span>.
    <div class="paragraph">

    </div>

    Instantiating the induction hypothesis with <span
    class="inlinecode"><span class="id" type="var">n'</span></span> thus
    allows us to conclude that <span class="inlinecode"><span class="id"
    type="var">n'</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">m'</span></span>, and
    it follows immediately that <span class="inlinecode"><span
    class="id" type="var">S</span></span> <span class="inlinecode"><span
    class="id" type="var">n'</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">S</span></span> <span class="inlinecode"><span
    class="id" type="var">m'</span></span>. Since <span
    class="inlinecode"><span class="id" type="var">S</span></span> <span
    class="inlinecode"><span class="id" type="var">n'</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> and <span
    class="inlinecode"><span class="id" type="var">S</span></span> <span
    class="inlinecode"><span class="id" type="var">m'</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">m</span></span>, this is just what we wanted
    to show. ☐

<div class="paragraph">

</div>

Here's another illustration of <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> and using an appropriately general
induction hypothesis. This is a slightly roundabout way of stating a
fact that we have already proved above. The extra equalities force us to
do a little more equational reasoning and exercise some of the tactics
we've seen recently.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">length\_snoc'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> : <span class="id" type="keyword">Type</span>)
(<span class="id" type="var">v</span> : <span class="id"
type="var">X</span>)\
                               (<span class="id" type="var">l</span> :
<span class="id" type="var">list</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">n</span> : <span
class="id" type="var">nat</span>),\
      <span class="id" type="var">length</span> <span class="id"
type="var">l</span> = <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">length</span> (<span class="id"
type="var">snoc</span> <span class="id" type="var">l</span> <span
class="id" type="var">v</span>) = <span class="id" type="var">S</span>
<span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">X</span> <span class="id" type="var">v</span> <span
class="id" type="var">l</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">l</span>
<span class="id" type="keyword">as</span> [| <span class="id"
type="var">v'</span> <span class="id" type="var">l'</span>].\
\
   <span class="id" type="var">Case</span> "l = []".\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">eq</span>. <span
class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">eq</span>. <span class="id"
type="tactic">reflexivity</span>.\
\
   <span class="id" type="var">Case</span> "l = v' :: l'".\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">eq</span>. <span
class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">n</span> <span
class="id" type="keyword">as</span> [| <span class="id"
type="var">n'</span>].\
     <span class="id" type="var">SCase</span> "n = 0". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">eq</span>.\
     <span class="id" type="var">SCase</span> "n = S n'".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="tactic">f\_equal</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHl'</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">eq</span>. <span class="id" type="tactic">reflexivity</span>.
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

It might be tempting to start proving the above theorem by introducing
<span class="inlinecode"><span class="id" type="var">n</span></span> and
<span class="inlinecode"><span class="id" type="var">eq</span></span> at
the outset. However, this leads to an induction hypothesis that is not
strong enough. Compare the above to the following (aborted) attempt:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">length\_snoc\_bad</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> : <span class="id" type="keyword">Type</span>)
(<span class="id" type="var">v</span> : <span class="id"
type="var">X</span>)\
                               (<span class="id" type="var">l</span> :
<span class="id" type="var">list</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">n</span> : <span
class="id" type="var">nat</span>),\
      <span class="id" type="var">length</span> <span class="id"
type="var">l</span> = <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">length</span> (<span class="id"
type="var">snoc</span> <span class="id" type="var">l</span> <span
class="id" type="var">v</span>) = <span class="id" type="var">S</span>
<span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">X</span> <span class="id" type="var">v</span> <span
class="id" type="var">l</span> <span class="id" type="var">n</span>
<span class="id" type="var">eq</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">l</span>
<span class="id" type="keyword">as</span> [| <span class="id"
type="var">v'</span> <span class="id" type="var">l'</span>].\
\
   <span class="id" type="var">Case</span> "l = []".\
     <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">eq</span>. <span class="id"
type="tactic">reflexivity</span>.\
\
   <span class="id" type="var">Case</span> "l = v' :: l'".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">n</span> <span
class="id" type="keyword">as</span> [| <span class="id"
type="var">n'</span>].\
     <span class="id" type="var">SCase</span> "n = 0". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">eq</span>.\
     <span class="id" type="var">SCase</span> "n = S n'".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="tactic">f\_equal</span>. <span class="id"
type="keyword">Abort</span>. <span
class="comment">(\* apply IHl'. \*)</span> <span
class="comment">(\* The IH doesn't apply! \*)</span>\
\

</div>

<div class="doc">

As in the double examples, the problem is that by introducing <span
class="inlinecode"><span class="id" type="var">n</span></span> before
doing induction on <span class="inlinecode"><span class="id"
type="var">l</span></span>, the induction hypothesis is specialized to
one particular natural number, namely <span class="inlinecode"><span
class="id" type="var">n</span></span>. In the induction case, however,
we need to be able to use the induction hypothesis on some other natural
number <span class="inlinecode"><span class="id"
type="var">n'</span></span>. Retaining the more general form of the
induction hypothesis thus gives us more flexibility.
<div class="paragraph">

</div>

In general, a good rule of thumb is to make the induction hypothesis as
general as possible.
<div class="paragraph">

</div>

#### Exercise: 3 stars (gen\_dep\_practice) {.section}

Prove this by induction on <span class="inlinecode"><span class="id"
type="var">l</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">index\_after\_last</span>: <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>) (<span
class="id" type="var">X</span> : <span class="id"
type="keyword">Type</span>) (<span class="id" type="var">l</span> :
<span class="id" type="var">list</span> <span class="id"
type="var">X</span>),\
      <span class="id" type="var">length</span> <span class="id"
type="var">l</span> = <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">index</span> <span class="id"
type="var">n</span> <span class="id" type="var">l</span> = <span
class="id" type="var">None</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced, optional (index\_after\_last\_informal) {.section}

Write an informal proof corresponding to your Coq proof of <span
class="inlinecode"><span class="id"
type="var">index\_after\_last</span></span>:
<div class="paragraph">

</div>

*Theorem*: For all sets <span class="inlinecode"><span class="id"
type="var">X</span></span>, lists <span class="inlinecode"><span
class="id" type="var">l</span></span> <span class="inlinecode">:</span>
<span class="inlinecode"><span class="id" type="var">list</span></span>
<span class="inlinecode"><span class="id" type="var">X</span></span>,
and numbers <span class="inlinecode"><span class="id"
type="var">n</span></span>, if <span class="inlinecode"><span class="id"
type="var">length</span></span> <span class="inlinecode"><span
class="id" type="var">l</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">n</span></span>
then <span class="inlinecode"><span class="id"
type="var">index</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode"><span class="id"
type="var">l</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">None</span></span>.
<div class="paragraph">

</div>

*Proof*: <span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (gen\_dep\_practice\_more) {.section}

Prove this by induction on <span class="inlinecode"><span class="id"
type="var">l</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">length\_snoc'''</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>) (<span
class="id" type="var">X</span> : <span class="id"
type="keyword">Type</span>)\
                               (<span class="id" type="var">v</span> :
<span class="id" type="var">X</span>) (<span class="id"
type="var">l</span> : <span class="id" type="var">list</span> <span
class="id" type="var">X</span>),\
      <span class="id" type="var">length</span> <span class="id"
type="var">l</span> = <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">length</span> (<span class="id"
type="var">snoc</span> <span class="id" type="var">l</span> <span
class="id" type="var">v</span>) = <span class="id" type="var">S</span>
<span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (app\_length\_cons) {.section}

Prove this by induction on <span class="inlinecode"><span class="id"
type="var">l1</span></span>, without using <span
class="inlinecode"><span class="id" type="var">app\_length</span></span>
from <span class="inlinecode"><span class="id"
type="var">Lists</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">app\_length\_cons</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> : <span class="id" type="keyword">Type</span>)
(<span class="id" type="var">l1</span> <span class="id"
type="var">l2</span> : <span class="id" type="var">list</span> <span
class="id" type="var">X</span>)\
                                   (<span class="id" type="var">x</span>
: <span class="id" type="var">X</span>) (<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>),\
      <span class="id" type="var">length</span> (<span class="id"
type="var">l1</span> ++ (<span class="id" type="var">x</span> :: <span
class="id" type="var">l2</span>)) = <span class="id" type="var">n</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">S</span> (<span class="id"
type="var">length</span> (<span class="id" type="var">l1</span> ++ <span
class="id" type="var">l2</span>)) = <span class="id"
type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, optional (app\_length\_twice) {.section}

Prove this by induction on <span class="inlinecode"><span class="id"
type="var">l</span></span>, without using app\_length.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">app\_length\_twice</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">n</span>:<span class="id" type="var">nat</span>)
(<span class="id" type="var">l</span>:<span class="id"
type="var">list</span> <span class="id" type="var">X</span>),\
      <span class="id" type="var">length</span> <span class="id"
type="var">l</span> = <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">length</span> (<span class="id"
type="var">l</span> ++ <span class="id" type="var">l</span>) = <span
class="id" type="var">n</span> + <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (double\_induction) {.section}

Prove the following principle of induction over two naturals.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">double\_induction</span>: <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>),\
   <span class="id" type="var">P</span> 0 0 <span
style="font-family: arial;">→</span>\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">m</span>, <span class="id" type="var">P</span> <span
class="id" type="var">m</span> 0 <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> (<span class="id" type="var">S</span> <span
class="id" type="var">m</span>) 0) <span
style="font-family: arial;">→</span>\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">P</span> 0 <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> 0 (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>)) <span
style="font-family: arial;">→</span>\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">m</span> <span class="id" type="var">n</span>, <span
class="id" type="var">P</span> <span class="id" type="var">m</span>
<span class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> (<span class="id" type="var">S</span> <span
class="id" type="var">m</span>) (<span class="id" type="var">S</span>
<span class="id" type="var">n</span>)) <span
style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">m</span> <span class="id" type="var">n</span>, <span
class="id" type="var">P</span> <span class="id" type="var">m</span>
<span class="id" type="var">n</span>.\
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

Using <span class="inlinecode"><span class="id" type="tactic">destruct</span></span> on Compound Expressions {.section}
============================================================================================================

<div class="paragraph">

</div>

We have seen many examples where the <span class="inlinecode"><span
class="id" type="tactic">destruct</span></span> tactic is used to
perform case analysis of the value of some variable. But sometimes we
need to reason by cases on the result of some *expression*. We can also
do this with <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span>.
<div class="paragraph">

</div>

Here are some examples:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">sillyfun</span> (<span class="id" type="var">n</span> : <span
class="id" type="var">nat</span>) : <span class="id"
type="var">bool</span> :=\
   <span class="id" type="keyword">if</span> <span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n</span> 3 <span
class="id" type="keyword">then</span> <span class="id"
type="var">false</span>\
   <span class="id" type="keyword">else</span> <span class="id"
type="keyword">if</span> <span class="id" type="var">beq\_nat</span>
<span class="id" type="var">n</span> 5 <span class="id"
type="keyword">then</span> <span class="id" type="var">false</span>\
   <span class="id" type="keyword">else</span> <span class="id"
type="var">false</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">sillyfun\_false</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>),\
   <span class="id" type="var">sillyfun</span> <span class="id"
type="var">n</span> = <span class="id" type="var">false</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span>. <span class="id" type="tactic">unfold</span> <span
class="id" type="var">sillyfun</span>.\
   <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n</span> 3).\
     <span class="id" type="var">Case</span> "beq\_nat n 3 = true".
<span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="var">Case</span> "beq\_nat n 3 = false".
<span class="id" type="tactic">destruct</span> (<span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n</span> 5).\
       <span class="id" type="var">SCase</span> "beq\_nat n 5 = true".
<span class="id" type="tactic">reflexivity</span>.\
       <span class="id" type="var">SCase</span> "beq\_nat n 5 = false".
<span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

After unfolding <span class="inlinecode"><span class="id"
type="var">sillyfun</span></span> in the above proof, we find that we
are stuck on <span class="inlinecode"><span class="id"
type="keyword">if</span></span> <span class="inlinecode">(<span
class="id" type="var">beq\_nat</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">3)</span> <span class="inlinecode"><span class="id"
type="keyword">then</span></span> <span class="inlinecode">...</span>
<span class="inlinecode"><span class="id"
type="keyword">else</span></span> <span class="inlinecode">...</span>.
Well, either <span class="inlinecode"><span class="id"
type="var">n</span></span> is equal to <span class="inlinecode">3</span>
or it isn't, so we use <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> <span class="inlinecode">(<span
class="id" type="var">beq\_nat</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">3)</span> to let us reason about the two cases.
<div class="paragraph">

</div>

In general, the <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> tactic can be used to perform case
analysis of the results of arbitrary computations. If <span
class="inlinecode"><span class="id" type="var">e</span></span> is an
expression whose type is some inductively defined type <span
class="inlinecode"><span class="id" type="var">T</span></span>, then,
for each constructor <span class="inlinecode"><span class="id"
type="var">c</span></span> of <span class="inlinecode"><span class="id"
type="var">T</span></span>, <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> <span class="inlinecode"><span
class="id" type="var">e</span></span> generates a subgoal in which all
occurrences of <span class="inlinecode"><span class="id"
type="var">e</span></span> (in the goal and in the context) are replaced
by <span class="inlinecode"><span class="id" type="var">c</span></span>.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

#### Exercise: 1 star (override\_shadow) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">override\_shadow</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) <span
class="id" type="var">x1</span> <span class="id" type="var">x2</span>
<span class="id" type="var">k1</span> <span class="id"
type="var">k2</span> (<span class="id" type="var">f</span> : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">X</span>),\
   (<span class="id" type="var">override</span> (<span class="id"
type="var">override</span> <span class="id" type="var">f</span> <span
class="id" type="var">k1</span> <span class="id" type="var">x2</span>)
<span class="id" type="var">k1</span> <span class="id"
type="var">x1</span>) <span class="id" type="var">k2</span> = (<span
class="id" type="var">override</span> <span class="id"
type="var">f</span> <span class="id" type="var">k1</span> <span
class="id" type="var">x1</span>) <span class="id" type="var">k2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (combine\_split) {.section}

Complete the proof below

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">combine\_split</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">X</span>
<span class="id" type="var">Y</span> (<span class="id"
type="var">l</span> : <span class="id" type="var">list</span> (<span
class="id" type="var">X</span> × <span class="id" type="var">Y</span>))
<span class="id" type="var">l1</span> <span class="id"
type="var">l2</span>,\
   <span class="id" type="tactic">split</span> <span class="id"
type="var">l</span> = (<span class="id" type="var">l1</span>, <span
class="id" type="var">l2</span>) <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">combine</span> <span class="id"
type="var">l1</span> <span class="id" type="var">l2</span> = <span
class="id" type="var">l</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Sometimes, doing a <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> on a compound expression (a
non-variable) will erase information we need to complete a proof. For
example, suppose we define a function <span class="inlinecode"><span
class="id" type="var">sillyfun1</span></span> like this:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">sillyfun1</span> (<span class="id" type="var">n</span> :
<span class="id" type="var">nat</span>) : <span class="id"
type="var">bool</span> :=\
   <span class="id" type="keyword">if</span> <span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n</span> 3 <span
class="id" type="keyword">then</span> <span class="id"
type="var">true</span>\
   <span class="id" type="keyword">else</span> <span class="id"
type="keyword">if</span> <span class="id" type="var">beq\_nat</span>
<span class="id" type="var">n</span> 5 <span class="id"
type="keyword">then</span> <span class="id" type="var">true</span>\
   <span class="id" type="keyword">else</span> <span class="id"
type="var">false</span>.\
\

</div>

<div class="doc">

And suppose that we want to convince Coq of the rather obvious
observation that <span class="inlinecode"><span class="id"
type="var">sillyfun1</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> yields <span
class="inlinecode"><span class="id" type="var">true</span></span> only
when <span class="inlinecode"><span class="id"
type="var">n</span></span> is odd. By analogy with the proofs we did
with <span class="inlinecode"><span class="id"
type="var">sillyfun</span></span> above, it is natural to start the
proof like this:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">sillyfun1\_odd\_FAILED</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>),\
      <span class="id" type="var">sillyfun1</span> <span class="id"
type="var">n</span> = <span class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">oddb</span> <span class="id"
type="var">n</span> = <span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">eq</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">sillyfun1</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">eq</span>.\
   <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n</span> 3).\
   <span class="comment">(\* stuck... \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

We get stuck at this point because the context does not contain enough
information to prove the goal! The problem is that the substitution
peformed by <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> is too brutal — it threw away every
occurrence of <span class="inlinecode"><span class="id"
type="var">beq\_nat</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">3</span>,
but we need to keep some memory of this expression and how it was
destructed, because we need to be able to reason that since, in this
branch of the case analysis, <span class="inlinecode"><span class="id"
type="var">beq\_nat</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">3</span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">true</span></span>, it must be that <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">=</span> <span class="inlinecode">3</span>, from
which it follows that <span class="inlinecode"><span class="id"
type="var">n</span></span> is odd.
<div class="paragraph">

</div>

What we would really like is to substitute away all existing occurences
of <span class="inlinecode"><span class="id"
type="var">beq\_nat</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">3</span>,
but at the same time add an equation to the context that records which
case we are in. The <span class="inlinecode"><span class="id"
type="var">eqn</span>:</span> qualifier allows us to introduce such an
equation (with whatever name we choose).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">sillyfun1\_odd</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>),\
      <span class="id" type="var">sillyfun1</span> <span class="id"
type="var">n</span> = <span class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">oddb</span> <span class="id"
type="var">n</span> = <span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">eq</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">sillyfun1</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">eq</span>.\
   <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n</span> 3) <span
class="id" type="var">eqn</span>:<span class="id"
type="var">Heqe3</span>.\
   <span
class="comment">(\* Now we have the same state as at the point where we got stuck\
     above, except that the context contains an extra equality\

    assumption, which is exactly what we need to make progress. \*)</span>\
     <span class="id" type="var">Case</span> "e3 = true". <span
class="id" type="tactic">apply</span> <span class="id"
type="var">beq\_nat\_true</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Heqe3</span>.\
       <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Heqe3</span>. <span class="id"
type="tactic">reflexivity</span>.\
     <span class="id" type="var">Case</span> "e3 = false".\
      <span
class="comment">(\* When we come to the second equality test in the body of the\
        function we are reasoning about, we can use <span
class="inlinecode"><span class="id"
type="var">eqn</span>:</span> again in the\
        same way, allow us to finish the proof. \*)</span>\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n</span> 5) <span
class="id" type="var">eqn</span>:<span class="id"
type="var">Heqe5</span>.\
         <span class="id" type="var">SCase</span> "e5 = true".\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">beq\_nat\_true</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Heqe5</span>.\
           <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Heqe5</span>. <span class="id"
type="tactic">reflexivity</span>.\
         <span class="id" type="var">SCase</span> "e5 = false". <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">eq</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (destruct\_eqn\_practice) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">bool\_fn\_applied\_thrice</span> :\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">f</span> : <span class="id" type="var">bool</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bool</span>) (<span class="id" type="var">b</span> : <span
class="id" type="var">bool</span>),\
   <span class="id" type="var">f</span> (<span class="id"
type="var">f</span> (<span class="id" type="var">f</span> <span
class="id" type="var">b</span>)) = <span class="id" type="var">f</span>
<span class="id" type="var">b</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (override\_same) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">override\_same</span> : <span
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
   (<span class="id" type="var">override</span> <span class="id"
type="var">f</span> <span class="id" type="var">k1</span> <span
class="id" type="var">x1</span>) <span class="id" type="var">k2</span> =
<span class="id" type="var">f</span> <span class="id"
type="var">k2</span>.\
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

Review {.section}
======

<div class="paragraph">

</div>

We've now seen a bunch of Coq's fundamental tactics. We'll introduce a
few more as we go along through the coming lectures, and later in the
course we'll introduce some more powerful *automation* tactics that make
Coq do more of the low-level work in many cases. But basically we've got
what we need to get work done.
<div class="paragraph">

</div>

Here are the ones we've seen:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="tactic">intros</span></span>: move hypotheses/variables from
    goal to context
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">reflexivity</span></span>: finish the proof (when the
    goal looks like <span class="inlinecode"><span class="id"
    type="var">e</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">e</span></span>)
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">apply</span></span>: prove goal using a hypothesis,
    lemma, or constructor
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">apply</span>...</span> <span class="inlinecode"><span
    class="id" type="keyword">in</span></span> <span
    class="inlinecode"><span class="id" type="var">H</span></span>:
    apply a hypothesis, lemma, or constructor to a hypothesis in the
    context (forward reasoning)
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">apply</span>...</span> <span class="inlinecode"><span
    class="id" type="keyword">with</span>...</span>: explicitly specify
    values for variables that cannot be determined by pattern matching
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">simpl</span></span>: simplify computations in the goal
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">simpl</span></span> <span class="inlinecode"><span
    class="id" type="keyword">in</span></span> <span
    class="inlinecode"><span class="id" type="var">H</span></span>: ...
    or a hypothesis
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">rewrite</span></span>: use an equality hypothesis (or
    lemma) to rewrite the goal
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">rewrite</span></span> <span
    class="inlinecode">...</span> <span class="inlinecode"><span
    class="id" type="keyword">in</span></span> <span
    class="inlinecode"><span class="id" type="var">H</span></span>: ...
    or a hypothesis
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">symmetry</span></span>: changes a goal of the form
    <span class="inlinecode"><span class="id" type="var">t</span>=<span
    class="id" type="var">u</span></span> into <span
    class="inlinecode"><span class="id" type="var">u</span>=<span
    class="id" type="var">t</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">symmetry</span></span> <span class="inlinecode"><span
    class="id" type="keyword">in</span></span> <span
    class="inlinecode"><span class="id" type="var">H</span></span>:
    changes a hypothesis of the form <span class="inlinecode"><span
    class="id" type="var">t</span>=<span class="id"
    type="var">u</span></span> into <span class="inlinecode"><span
    class="id" type="var">u</span>=<span class="id"
    type="var">t</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">unfold</span></span>: replace a defined constant by
    its right-hand side in the goal
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">unfold</span>...</span> <span class="inlinecode"><span
    class="id" type="keyword">in</span></span> <span
    class="inlinecode"><span class="id" type="var">H</span></span>: ...
    or a hypothesis
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">destruct</span>...</span> <span
    class="inlinecode"><span class="id"
    type="keyword">as</span>...</span>: case analysis on values of
    inductively defined types
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">destruct</span>...</span> <span
    class="inlinecode"><span class="id"
    type="var">eqn</span>:...</span>: specify the name of an equation to
    be added to the context, recording the result of the case analysis
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">induction</span>...</span> <span
    class="inlinecode"><span class="id"
    type="keyword">as</span>...</span>: induction on values of
    inductively defined types
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">inversion</span></span>: reason by injectivity and
    distinctness of constructors
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">assert</span></span> <span class="inlinecode">(<span
    class="id" type="var">e</span>)</span> <span
    class="inlinecode"><span class="id" type="keyword">as</span></span>
    <span class="inlinecode"><span class="id"
    type="var">H</span></span>: introduce a "local lemma" <span
    class="inlinecode"><span class="id" type="var">e</span></span> and
    call it <span class="inlinecode"><span class="id"
    type="var">H</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">generalize</span></span> <span
    class="inlinecode"><span class="id"
    type="tactic">dependent</span></span> <span class="inlinecode"><span
    class="id" type="var">x</span></span>: move the variable <span
    class="inlinecode"><span class="id" type="var">x</span></span> (and
    anything else that depends on it) from the context back to an
    explicit hypothesis in the goal formula

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Additional Exercises {.section}
====================

<div class="paragraph">

</div>

#### Exercise: 3 stars (beq\_nat\_sym) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">beq\_nat\_sym</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> <span class="id" type="var">m</span> : <span
class="id" type="var">nat</span>),\
   <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">beq\_nat</span> <span class="id"
type="var">m</span> <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced, optional (beq\_nat\_sym\_informal) {.section}

Give an informal proof of this lemma that corresponds to your formal
proof above:
<div class="paragraph">

</div>

Theorem: For any <span class="inlinecode"><span class="id"
type="var">nat</span></span>s <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode"><span class="id"
type="var">m</span></span>, <span class="inlinecode"><span class="id"
type="var">beq\_nat</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode"><span
class="id" type="var">m</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">beq\_nat</span></span> <span class="inlinecode"><span
class="id" type="var">m</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span>.
<div class="paragraph">

</div>

Proof: <span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (beq\_nat\_trans) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">beq\_nat\_trans</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> <span class="id"
type="var">p</span>,\
   <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">m</span> <span class="id" type="var">p</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">p</span> = <span
class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (split\_combine) {.section}

We have just proven that for all lists of pairs, <span
class="inlinecode"><span class="id" type="var">combine</span></span> is
the inverse of <span class="inlinecode"><span class="id"
type="tactic">split</span></span>. How would you formalize the statement
that <span class="inlinecode"><span class="id"
type="tactic">split</span></span> is the inverse of <span
class="inlinecode"><span class="id" type="var">combine</span></span>?
When is this property true?
<div class="paragraph">

</div>

Complete the definition of <span class="inlinecode"><span class="id"
type="var">split\_combine\_statement</span></span> below with a property
that states that <span class="inlinecode"><span class="id"
type="tactic">split</span></span> is the inverse of <span
class="inlinecode"><span class="id" type="var">combine</span></span>.
Then, prove that the property holds. (Be sure to leave your induction
hypothesis general by not doing <span class="inlinecode"><span
class="id" type="tactic">intros</span></span> on more things than
necessary. Hint: what property do you need of <span
class="inlinecode"><span class="id" type="var">l1</span></span> and
<span class="inlinecode"><span class="id" type="var">l2</span></span>
for <span class="inlinecode"><span class="id"
type="tactic">split</span></span> <span class="inlinecode"><span
class="id" type="var">combine</span></span> <span
class="inlinecode"><span class="id" type="var">l1</span></span> <span
class="inlinecode"><span class="id" type="var">l2</span></span> <span
class="inlinecode">=</span> <span class="inlinecode">(<span class="id"
type="var">l1</span>,<span class="id" type="var">l2</span>)</span> to be
true?)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">split\_combine\_statement</span> : <span class="id"
type="keyword">Prop</span> :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">split\_combine</span> : <span class="id"
type="var">split\_combine\_statement</span>.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (override\_permute) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">override\_permute</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) <span
class="id" type="var">x1</span> <span class="id" type="var">x2</span>
<span class="id" type="var">k1</span> <span class="id"
type="var">k2</span> <span class="id" type="var">k3</span> (<span
class="id" type="var">f</span> : <span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="var">X</span>),\
   <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">k2</span> <span class="id" type="var">k1</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span>\
   (<span class="id" type="var">override</span> (<span class="id"
type="var">override</span> <span class="id" type="var">f</span> <span
class="id" type="var">k2</span> <span class="id" type="var">x2</span>)
<span class="id" type="var">k1</span> <span class="id"
type="var">x1</span>) <span class="id" type="var">k3</span> = (<span
class="id" type="var">override</span> (<span class="id"
type="var">override</span> <span class="id" type="var">f</span> <span
class="id" type="var">k1</span> <span class="id" type="var">x1</span>)
<span class="id" type="var">k2</span> <span class="id"
type="var">x2</span>) <span class="id" type="var">k3</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (filter\_exercise) {.section}

This one is a bit challenging. Pay attention to the form of your IH.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">filter\_exercise</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> : <span class="id" type="keyword">Type</span>)
(<span class="id" type="var">test</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">bool</span>)\
                              (<span class="id" type="var">x</span> :
<span class="id" type="var">X</span>) (<span class="id"
type="var">l</span> <span class="id" type="var">lf</span> : <span
class="id" type="var">list</span> <span class="id"
type="var">X</span>),\
      <span class="id" type="var">filter</span> <span class="id"
type="var">test</span> <span class="id" type="var">l</span> = <span
class="id" type="var">x</span> :: <span class="id" type="var">lf</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">test</span> <span class="id"
type="var">x</span> = <span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, advanced (forall\_exists\_challenge) {.section}

Define two recursive <span class="inlinecode"><span class="id"
type="var">Fixpoints</span></span>, <span class="inlinecode"><span
class="id" type="var">forallb</span></span> and <span
class="inlinecode"><span class="id" type="var">existsb</span></span>.
The first checks whether every element in a list satisfies a given
predicate:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">forallb</span> <span class="id"
type="var">oddb</span> [1;3;5;7;9] = <span class="id"
type="var">true</span>\
\
       <span class="id" type="var">forallb</span> <span class="id"
type="var">negb</span> [<span class="id" type="var">false</span>;<span
class="id" type="var">false</span>] = <span class="id"
type="var">true</span>\
   \
       <span class="id" type="var">forallb</span> <span class="id"
type="var">evenb</span> [0;2;4;5] = <span class="id"
type="var">false</span>\
   \
       <span class="id" type="var">forallb</span> (<span class="id"
type="var">beq\_nat</span> 5) [] = <span class="id"
type="var">true</span>
<div class="paragraph">

</div>

</div>

The second checks whether there exists an element in the list that
satisfies a given predicate:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">existsb</span> (<span class="id"
type="var">beq\_nat</span> 5) [0;2;3;6] = <span class="id"
type="var">false</span>\
  \
       <span class="id" type="var">existsb</span> (<span class="id"
type="var">andb</span> <span class="id" type="var">true</span>) [<span
class="id" type="var">true</span>;<span class="id"
type="var">true</span>;<span class="id" type="var">false</span>] = <span
class="id" type="var">true</span>\
  \
       <span class="id" type="var">existsb</span> <span class="id"
type="var">oddb</span> [1;0;0;0;0;3] = <span class="id"
type="var">true</span>\
  \
       <span class="id" type="var">existsb</span> <span class="id"
type="var">evenb</span> [] = <span class="id" type="var">false</span>
<div class="paragraph">

</div>

</div>

Next, define a *nonrecursive* version of <span class="inlinecode"><span
class="id" type="var">existsb</span></span> — call it <span
class="inlinecode"><span class="id" type="var">existsb'</span></span> —
using <span class="inlinecode"><span class="id"
type="var">forallb</span></span> and <span class="inlinecode"><span
class="id" type="var">negb</span></span>.
<div class="paragraph">

</div>

Prove theorem <span class="inlinecode"><span class="id"
type="var">existsb\_existsb'</span></span> that <span
class="inlinecode"><span class="id" type="var">existsb'</span></span>
and <span class="inlinecode"><span class="id"
type="var">existsb</span></span> have the same behavior.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

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
