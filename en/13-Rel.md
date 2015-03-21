<div id="page">

<div id="header">

</div>

<div id="main">

Rel<span class="subtitle">Properties of Relations</span> {.libtitle}
========================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">SfLib</span>.\
\

</div>

<div class="doc">

This short, optional chapter develops some basic definitions and a few
theorems about binary relations in Coq. The key definitions are repeated
where they are actually used (in the <span class="inlinecode"><span
class="id" type="var">Smallstep</span></span> chapter), so readers who
are already comfortable with these ideas can safely skim or skip this
chapter. However, relations are also a good source of exercises for
developing facility with Coq's basic reasoning facilities, so it may be
useful to look at it just after the <span class="inlinecode"><span
class="id" type="var">Logic</span></span> chapter.
<div class="paragraph">

</div>

A (binary) *relation* on a set <span class="inlinecode"><span class="id"
type="var">X</span></span> is a family of propositions parameterized by
two elements of <span class="inlinecode"><span class="id"
type="var">X</span></span> — i.e., a proposition about pairs of elements
of <span class="inlinecode"><span class="id" type="var">X</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">relation</span> (<span class="id" type="var">X</span>: <span
class="id" type="keyword">Type</span>) := <span class="id"
type="var">X</span><span style="font-family: arial;">→</span><span
class="id" type="var">X</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>.\
\

</div>

<div class="doc">

Somewhat confusingly, the Coq standard library hijacks the generic term
"relation" for this specific instance. To maintain consistency with the
library, we will do the same. So, henceforth the Coq identifier <span
class="inlinecode"><span class="id" type="var">relation</span></span>
will always refer to a binary relation between some set and itself,
while the English word "relation" can refer either to the specific Coq
concept or the more general concept of a relation between any number of
possibly different sets. The context of the discussion should always
make clear which is meant.
<div class="paragraph">

</div>

An example relation on <span class="inlinecode"><span class="id"
type="var">nat</span></span> is <span class="inlinecode"><span
class="id" type="var">le</span></span>, the less-that-or-equal-to
relation which we usually write like this <span class="inlinecode"><span
class="id" type="var">n1</span></span> <span class="inlinecode">≤</span>
<span class="inlinecode"><span class="id" type="var">n2</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">le</span>.\
 <span
class="comment">(\* ====\> Inductive le (n : nat) : nat -\> Prop :=\
              le\_n : n \<= n\
            | le\_S : forall m : nat, n \<= m -\> n \<= S m \*)</span>\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">le</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>.\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">le</span> : <span class="id" type="var">relation</span> <span
class="id" type="var">nat</span>.\
\

</div>

<div class="doc">

Basic Properties of Relations {.section}
=============================

<div class="paragraph">

</div>

As anyone knows who has taken an undergraduate discrete math course,
there is a lot to be said about relations in general — ways of
classifying relations (are they reflexive, transitive, etc.), theorems
that can be proved generically about classes of relations, constructions
that build one relation from another, etc. For example...
<div class="paragraph">

</div>

A relation <span class="inlinecode"><span class="id"
type="var">R</span></span> on a set <span class="inlinecode"><span
class="id" type="var">X</span></span> is a *partial function* if, for
every <span class="inlinecode"><span class="id"
type="var">x</span></span>, there is at most one <span
class="inlinecode"><span class="id" type="var">y</span></span> such that
<span class="inlinecode"><span class="id" type="var">R</span></span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span> —
i.e., if <span class="inlinecode"><span class="id"
type="var">R</span></span> <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode"><span class="id"
type="var">y1</span></span> and <span class="inlinecode"><span
class="id" type="var">R</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="var">y2</span></span> together imply <span
class="inlinecode"><span class="id" type="var">y1</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">y2</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">partial\_function</span> {<span class="id"
type="var">X</span>: <span class="id" type="keyword">Type</span>} (<span
class="id" type="var">R</span>: <span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">x</span> <span class="id" type="var">y1</span> <span
class="id" type="var">y2</span> : <span class="id" type="var">X</span>,
<span class="id" type="var">R</span> <span class="id"
type="var">x</span> <span class="id" type="var">y1</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">x</span> <span
class="id" type="var">y2</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">y1</span> = <span class="id" type="var">y2</span>.\
\

</div>

<div class="doc">

For example, the <span class="inlinecode"><span class="id"
type="var">next\_nat</span></span> relation defined earlier is a partial
function.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">next\_nat</span>.\
 <span
class="comment">(\* ====\> Inductive next\_nat (n : nat) : nat -\> Prop := \
            nn : next\_nat n (S n) \*)</span>\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">next\_nat</span> : <span class="id"
type="var">relation</span> <span class="id" type="var">nat</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">next\_nat\_partial\_function</span> :\
    <span class="id" type="var">partial\_function</span> <span
class="id" type="var">next\_nat</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">partial\_function</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">y1</span> <span
class="id" type="var">y2</span> <span class="id" type="var">H1</span>
<span class="id" type="var">H2</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H1</span>. <span class="id" type="tactic">inversion</span>
<span class="id" type="var">H2</span>.\
   <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

However, the <span class="inlinecode">≤</span> relation on numbers is
not a partial function. In short: Assume, for a contradiction, that
<span class="inlinecode">≤</span> is a partial function. But then, since
<span class="inlinecode">0</span> <span class="inlinecode">≤</span>
<span class="inlinecode">0</span> and <span class="inlinecode">0</span>
<span class="inlinecode">≤</span> <span class="inlinecode">1</span>, it
follows that <span class="inlinecode">0</span> <span
class="inlinecode">=</span> <span class="inlinecode">1</span>. This is
nonsense, so our assumption was contradictory.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">le\_not\_a\_partial\_function</span> :\
   ¬ (<span class="id" type="var">partial\_function</span> <span
class="id" type="var">le</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">not</span>. <span class="id" type="tactic">unfold</span>
<span class="id" type="var">partial\_function</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">Hc</span>.\
   <span class="id" type="tactic">assert</span> (0 = 1) <span class="id"
type="keyword">as</span> <span class="id" type="var">Nonsense</span>.\
    <span class="id" type="var">Case</span> "Proof of assertion".\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">Hc</span> <span class="id" type="keyword">with</span> (<span
class="id" type="var">x</span> := 0).\
      <span class="id" type="tactic">apply</span> <span class="id"
type="var">le\_n</span>.\
      <span class="id" type="tactic">apply</span> <span class="id"
type="var">le\_S</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">le\_n</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Nonsense</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional {.section}

Show that the <span class="inlinecode"><span class="id"
type="var">total\_relation</span></span> defined in earlier is not a
partial function.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional {.section}

Show that the <span class="inlinecode"><span class="id"
type="var">empty\_relation</span></span> defined earlier is a partial
function.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

A *reflexive* relation on a set <span class="inlinecode"><span
class="id" type="var">X</span></span> is one for which every element of
<span class="inlinecode"><span class="id" type="var">X</span></span> is
related to itself.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">reflexive</span> {<span class="id" type="var">X</span>: <span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">R</span>: <span class="id" type="var">relation</span> <span
class="id" type="var">X</span>) :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">a</span> : <span class="id" type="var">X</span>, <span
class="id" type="var">R</span> <span class="id" type="var">a</span>
<span class="id" type="var">a</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">le\_reflexive</span> :\
   <span class="id" type="var">reflexive</span> <span class="id"
type="var">le</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">reflexive</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">n</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">le\_n</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

A relation <span class="inlinecode"><span class="id"
type="var">R</span></span> is *transitive* if <span
class="inlinecode"><span class="id" type="var">R</span></span> <span
class="inlinecode"><span class="id" type="var">a</span></span> <span
class="inlinecode"><span class="id" type="var">c</span></span> holds
whenever <span class="inlinecode"><span class="id"
type="var">R</span></span> <span class="inlinecode"><span class="id"
type="var">a</span></span> <span class="inlinecode"><span class="id"
type="var">b</span></span> and <span class="inlinecode"><span class="id"
type="var">R</span></span> <span class="inlinecode"><span class="id"
type="var">b</span></span> <span class="inlinecode"><span class="id"
type="var">c</span></span> do.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">transitive</span> {<span class="id" type="var">X</span>:
<span class="id" type="keyword">Type</span>} (<span class="id"
type="var">R</span>: <span class="id" type="var">relation</span> <span
class="id" type="var">X</span>) :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">a</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span> : <span class="id" type="var">X</span>,
(<span class="id" type="var">R</span> <span class="id"
type="var">a</span> <span class="id" type="var">b</span>) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">R</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span>) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">R</span> <span class="id" type="var">a</span> <span
class="id" type="var">c</span>).\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">le\_trans</span> :\
   <span class="id" type="var">transitive</span> <span class="id"
type="var">le</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">o</span> <span class="id" type="var">Hnm</span>
<span class="id" type="var">Hmo</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">Hmo</span>.\
   <span class="id" type="var">Case</span> "le\_n". <span class="id"
type="tactic">apply</span> <span class="id" type="var">Hnm</span>.\
   <span class="id" type="var">Case</span> "le\_S". <span class="id"
type="tactic">apply</span> <span class="id" type="var">le\_S</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">IHHmo</span>. <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">lt\_trans</span>:\
   <span class="id" type="var">transitive</span> <span class="id"
type="var">lt</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">lt</span>. <span class="id" type="tactic">unfold</span> <span
class="id" type="var">transitive</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">o</span> <span class="id" type="var">Hnm</span>
<span class="id" type="var">Hmo</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">le\_S</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hnm</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">le\_trans</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">a</span> := (<span class="id"
type="var">S</span> <span class="id" type="var">n</span>)) (<span
class="id" type="var">b</span> := (<span class="id" type="var">S</span>
<span class="id" type="var">m</span>)) (<span class="id"
type="var">c</span> := <span class="id" type="var">o</span>).\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">Hnm</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">Hmo</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional {.section}

We can also prove <span class="inlinecode"><span class="id"
type="var">lt\_trans</span></span> more laboriously by induction,
without using le\_trans. Do this.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">lt\_trans'</span> :\
   <span class="id" type="var">transitive</span> <span class="id"
type="var">lt</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span
class="comment">(\* Prove this by induction on evidence that <span
class="inlinecode"><span class="id"
type="var">m</span></span> is less than <span class="inlinecode"><span
class="id" type="var">o</span></span>. \*)</span>\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">lt</span>. <span class="id" type="tactic">unfold</span> <span
class="id" type="var">transitive</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">o</span> <span class="id" type="var">Hnm</span>
<span class="id" type="var">Hmo</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">Hmo</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">m'</span> <span class="id"
type="var">Hm'o</span>].\
     <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional {.section}

Prove the same thing again by induction on <span
class="inlinecode"><span class="id" type="var">o</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">lt\_trans''</span> :\
   <span class="id" type="var">transitive</span> <span class="id"
type="var">lt</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">lt</span>. <span class="id" type="tactic">unfold</span> <span
class="id" type="var">transitive</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">o</span> <span class="id" type="var">Hnm</span>
<span class="id" type="var">Hmo</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">o</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">o'</span>].\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

The transitivity of <span class="inlinecode"><span class="id"
type="var">le</span></span>, in turn, can be used to prove some facts
that will be useful later (e.g., for the proof of antisymmetry below)...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">le\_Sn\_le</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>, <span class="id"
type="var">S</span> <span class="id" type="var">n</span> ≤ <span
class="id" type="var">m</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> ≤ <span class="id" type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">le\_trans</span>
<span class="id" type="keyword">with</span> (<span class="id"
type="var">S</span> <span class="id" type="var">n</span>).\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">le\_S</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">le\_n</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">H</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star, optional {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">le\_S\_n</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   (<span class="id" type="var">S</span> <span class="id"
type="var">n</span> ≤ <span class="id" type="var">S</span> <span
class="id" type="var">m</span>) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">n</span> ≤ <span class="id" type="var">m</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (le\_Sn\_n\_inf) {.section}

Provide an informal proof of the following theorem:
<div class="paragraph">

</div>

Theorem: For every <span class="inlinecode"><span class="id"
type="var">n</span></span>, <span class="inlinecode">\~(<span class="id"
type="var">S</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode">≤</span> <span
class="inlinecode"><span class="id" type="var">n</span>)</span>
<div class="paragraph">

</div>

A formal proof of this is an optional exercise below, but try the
informal proof without doing the formal proof first.
<div class="paragraph">

</div>

Proof: <span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">le\_Sn\_n</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
   ¬ (<span class="id" type="var">S</span> <span class="id"
type="var">n</span> ≤ <span class="id" type="var">n</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Reflexivity and transitivity are the main concepts we'll need for later
chapters, but, for a bit of additional practice working with relations
in Coq, here are a few more common ones.
<div class="paragraph">

</div>

A relation <span class="inlinecode"><span class="id"
type="var">R</span></span> is *symmetric* if <span
class="inlinecode"><span class="id" type="var">R</span></span> <span
class="inlinecode"><span class="id" type="var">a</span></span> <span
class="inlinecode"><span class="id" type="var">b</span></span> implies
<span class="inlinecode"><span class="id" type="var">R</span></span>
<span class="inlinecode"><span class="id" type="var">b</span></span>
<span class="inlinecode"><span class="id" type="var">a</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">symmetric</span> {<span class="id" type="var">X</span>: <span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">R</span>: <span class="id" type="var">relation</span> <span
class="id" type="var">X</span>) :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">a</span> <span class="id" type="var">b</span> : <span
class="id" type="var">X</span>, (<span class="id" type="var">R</span>
<span class="id" type="var">a</span> <span class="id"
type="var">b</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">R</span> <span class="id" type="var">b</span>
<span class="id" type="var">a</span>).\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">le\_not\_symmetric</span> :\
   ¬ (<span class="id" type="var">symmetric</span> <span class="id"
type="var">le</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

A relation <span class="inlinecode"><span class="id"
type="var">R</span></span> is *antisymmetric* if <span
class="inlinecode"><span class="id" type="var">R</span></span> <span
class="inlinecode"><span class="id" type="var">a</span></span> <span
class="inlinecode"><span class="id" type="var">b</span></span> and <span
class="inlinecode"><span class="id" type="var">R</span></span> <span
class="inlinecode"><span class="id" type="var">b</span></span> <span
class="inlinecode"><span class="id" type="var">a</span></span> together
imply <span class="inlinecode"><span class="id"
type="var">a</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">b</span></span> — that
is, if the only "cycles" in <span class="inlinecode"><span class="id"
type="var">R</span></span> are trivial ones.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">antisymmetric</span> {<span class="id" type="var">X</span>:
<span class="id" type="keyword">Type</span>} (<span class="id"
type="var">R</span>: <span class="id" type="var">relation</span> <span
class="id" type="var">X</span>) :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">a</span> <span class="id" type="var">b</span> : <span
class="id" type="var">X</span>, (<span class="id" type="var">R</span>
<span class="id" type="var">a</span> <span class="id"
type="var">b</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">R</span> <span class="id" type="var">b</span>
<span class="id" type="var">a</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">a</span> = <span class="id" type="var">b</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">le\_antisymmetric</span> :\
   <span class="id" type="var">antisymmetric</span> <span class="id"
type="var">le</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">le\_step</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> <span class="id"
type="var">p</span>,\
   <span class="id" type="var">n</span> \< <span class="id"
type="var">m</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">m</span> ≤ <span class="id"
type="var">S</span> <span class="id" type="var">p</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">n</span> ≤ <span class="id"
type="var">p</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

A relation is an *equivalence* if it's reflexive, symmetric, and
transitive.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">equivalence</span> {<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>} (<span
class="id" type="var">R</span>: <span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) :=\
   (<span class="id" type="var">reflexive</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">∧</span> (<span
class="id" type="var">symmetric</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">∧</span> (<span
class="id" type="var">transitive</span> <span class="id"
type="var">R</span>).\
\

</div>

<div class="doc">

A relation is a *partial order* when it's reflexive, *anti*-symmetric,
and transitive. In the Coq standard library it's called just "order" for
short.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">order</span> {<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">R</span>: <span class="id" type="var">relation</span> <span
class="id" type="var">X</span>) :=\
   (<span class="id" type="var">reflexive</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">∧</span> (<span
class="id" type="var">antisymmetric</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">∧</span> (<span
class="id" type="var">transitive</span> <span class="id"
type="var">R</span>).\
\

</div>

<div class="doc">

A preorder is almost like a partial order, but doesn't have to be
antisymmetric.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">preorder</span> {<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">R</span>: <span class="id" type="var">relation</span> <span
class="id" type="var">X</span>) :=\
   (<span class="id" type="var">reflexive</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">∧</span> (<span
class="id" type="var">transitive</span> <span class="id"
type="var">R</span>).\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">le\_order</span> :\
   <span class="id" type="var">order</span> <span class="id"
type="var">le</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">order</span>. <span class="id" type="tactic">split</span>.\
     <span class="id" type="var">Case</span> "refl". <span class="id"
type="tactic">apply</span> <span class="id"
type="var">le\_reflexive</span>.\
     <span class="id" type="tactic">split</span>.\
       <span class="id" type="var">Case</span> "antisym". <span
class="id" type="tactic">apply</span> <span class="id"
type="var">le\_antisymmetric</span>.\
       <span class="id" type="var">Case</span> "transitive.". <span
class="id" type="tactic">apply</span> <span class="id"
type="var">le\_trans</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Reflexive, Transitive Closure {.section}
=============================

<div class="paragraph">

</div>

The *reflexive, transitive closure* of a relation <span
class="inlinecode"><span class="id" type="var">R</span></span> is the
smallest relation that contains <span class="inlinecode"><span
class="id" type="var">R</span></span> and that is both reflexive and
transitive. Formally, it is defined like this in the Relations module of
the Coq standard library:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">clos\_refl\_trans</span> {<span class="id"
type="var">A</span>: <span class="id" type="keyword">Type</span>} (<span
class="id" type="var">R</span>: <span class="id"
type="var">relation</span> <span class="id" type="var">A</span>) : <span
class="id" type="var">relation</span> <span class="id"
type="var">A</span> :=\
     | <span class="id" type="var">rt\_step</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">y</span>, <span class="id"
type="var">R</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">clos\_refl\_trans</span> <span class="id" type="var">R</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y</span>\
     | <span class="id" type="var">rt\_refl</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span class="id"
type="var">clos\_refl\_trans</span> <span class="id" type="var">R</span>
<span class="id" type="var">x</span> <span class="id"
type="var">x</span>\
     | <span class="id" type="var">rt\_trans</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">y</span> <span class="id"
type="var">z</span>,\
           <span class="id" type="var">clos\_refl\_trans</span> <span
class="id" type="var">R</span> <span class="id" type="var">x</span>
<span class="id" type="var">y</span> <span
style="font-family: arial;">→</span>\
           <span class="id" type="var">clos\_refl\_trans</span> <span
class="id" type="var">R</span> <span class="id" type="var">y</span>
<span class="id" type="var">z</span> <span
style="font-family: arial;">→</span>\
           <span class="id" type="var">clos\_refl\_trans</span> <span
class="id" type="var">R</span> <span class="id" type="var">x</span>
<span class="id" type="var">z</span>.\
\

</div>

<div class="doc">

For example, the reflexive and transitive closure of the <span
class="inlinecode"><span class="id" type="var">next\_nat</span></span>
relation coincides with the <span class="inlinecode"><span class="id"
type="var">le</span></span> relation.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">next\_nat\_closure\_is\_le</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   (<span class="id" type="var">n</span> ≤ <span class="id"
type="var">m</span>) <span style="font-family: arial;">↔</span> ((<span
class="id" type="var">clos\_refl\_trans</span> <span class="id"
type="var">next\_nat</span>) <span class="id" type="var">n</span> <span
class="id" type="var">m</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span>. <span
class="id" type="tactic">split</span>.\
     <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
       <span class="id" type="tactic">intro</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">induction</span>
<span class="id" type="var">H</span>.\
       <span class="id" type="var">SCase</span> "le\_n". <span
class="id" type="tactic">apply</span> <span class="id"
type="var">rt\_refl</span>.\
       <span class="id" type="var">SCase</span> "le\_S".\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">rt\_trans</span> <span class="id" type="keyword">with</span>
<span class="id" type="var">m</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHle</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">rt\_step</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">nn</span>.\
     <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
       <span class="id" type="tactic">intro</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">induction</span>
<span class="id" type="var">H</span>.\
       <span class="id" type="var">SCase</span> "rt\_step". <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">le\_S</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">le\_n</span>.\
       <span class="id" type="var">SCase</span> "rt\_refl". <span
class="id" type="tactic">apply</span> <span class="id"
type="var">le\_n</span>.\
       <span class="id" type="var">SCase</span> "rt\_trans".\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">le\_trans</span> <span class="id" type="keyword">with</span>
<span class="id" type="var">y</span>.\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHclos\_refl\_trans1</span>.\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHclos\_refl\_trans2</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The above definition of reflexive, transitive closure is natural — it
says, explicitly, that the reflexive and transitive closure of <span
class="inlinecode"><span class="id" type="var">R</span></span> is the
least relation that includes <span class="inlinecode"><span class="id"
type="var">R</span></span> and that is closed under rules of reflexivity
and transitivity. But it turns out that this definition is not very
convenient for doing proofs — the "nondeterminism" of the <span
class="inlinecode"><span class="id" type="var">rt\_trans</span></span>
rule can sometimes lead to tricky inductions.
<div class="paragraph">

</div>

Here is a more useful definition...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">refl\_step\_closure</span> {<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>} (<span
class="id" type="var">R</span>: <span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) : <span
class="id" type="var">relation</span> <span class="id"
type="var">X</span> :=\
   | <span class="id" type="var">rsc\_refl</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> : <span class="id" type="var">X</span>), <span
class="id" type="var">refl\_step\_closure</span> <span class="id"
type="var">R</span> <span class="id" type="var">x</span> <span
class="id" type="var">x</span>\
   | <span class="id" type="var">rsc\_step</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span> : <span class="id" type="var">X</span>),\
                     <span class="id" type="var">R</span> <span
class="id" type="var">x</span> <span class="id" type="var">y</span>
<span style="font-family: arial;">→</span>\
                     <span class="id"
type="var">refl\_step\_closure</span> <span class="id"
type="var">R</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span> <span
style="font-family: arial;">→</span>\
                     <span class="id"
type="var">refl\_step\_closure</span> <span class="id"
type="var">R</span> <span class="id" type="var">x</span> <span
class="id" type="var">z</span>.\
\

</div>

<div class="doc">

(Note that, aside from the naming of the constructors, this definition
is the same as the <span class="inlinecode"><span class="id"
type="var">multi</span></span> step relation used in many other
chapters.)
<div class="paragraph">

</div>

(The following <span class="inlinecode"><span class="id"
type="keyword">Tactic</span></span> <span class="inlinecode"><span
class="id" type="keyword">Notation</span></span> definitions are
explained in another chapter. You can ignore them if you haven't read
the explanation yet.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Tactic Notation</span> "rt\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "rt\_step" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"rt\_refl"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "rt\_trans" ].\
\
 <span class="id" type="keyword">Tactic Notation</span> "rsc\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "rsc\_refl" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"rsc\_step" ].\
\

</div>

<div class="doc">

Our new definition of reflexive, transitive closure "bundles" the <span
class="inlinecode"><span class="id" type="var">rt\_step</span></span>
and <span class="inlinecode"><span class="id"
type="var">rt\_trans</span></span> rules into the single rule step. The
left-hand premise of this step is a single use of <span
class="inlinecode"><span class="id" type="var">R</span></span>, leading
to a much simpler induction principle.
<div class="paragraph">

</div>

Before we go on, we should check that the two definitions do indeed
define the same relation...
<div class="paragraph">

</div>

First, we prove two lemmas showing that <span class="inlinecode"><span
class="id" type="var">refl\_step\_closure</span></span> mimics the
behavior of the two "missing" <span class="inlinecode"><span class="id"
type="var">clos\_refl\_trans</span></span> constructors.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">rsc\_R</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">R</span>:<span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">x</span> <span class="id" type="var">y</span> :
<span class="id" type="var">X</span>),\
        <span class="id" type="var">R</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">refl\_step\_closure</span> <span class="id"
type="var">R</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">X</span> <span class="id" type="var">R</span> <span
class="id" type="var">x</span> <span class="id" type="var">y</span>
<span class="id" type="var">H</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">rsc\_step</span> <span class="id" type="keyword">with</span>
<span class="id" type="var">y</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">rsc\_refl</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (rsc\_trans) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">rsc\_trans</span> :\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">R</span>: <span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">x</span> <span class="id" type="var">y</span>
<span class="id" type="var">z</span> : <span class="id"
type="var">X</span>),\
       <span class="id" type="var">refl\_step\_closure</span> <span
class="id" type="var">R</span> <span class="id" type="var">x</span>
<span class="id" type="var">y</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">refl\_step\_closure</span> <span
class="id" type="var">R</span> <span class="id" type="var">y</span>
<span class="id" type="var">z</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">refl\_step\_closure</span> <span
class="id" type="var">R</span> <span class="id" type="var">x</span>
<span class="id" type="var">z</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Then we use these facts to prove that the two definitions of reflexive,
transitive closure do indeed define the same relation.
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (rtc\_rsc\_coincide) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">rtc\_rsc\_coincide</span> :\
          <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">R</span>: <span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">x</span> <span class="id" type="var">y</span> :
<span class="id" type="var">X</span>),\
   <span class="id" type="var">clos\_refl\_trans</span> <span class="id"
type="var">R</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">refl\_step\_closure</span> <span class="id"
type="var">R</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>.\
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

</div>

</div>

<div id="footer">

------------------------------------------------------------------------

[Index](http://www.cis.upenn.edu/~bcpierce/sf/current/coqindex.html)

</div>

</div>
