<div id="page">

<div id="header">

</div>

<div id="main">

UseAuto<span class="subtitle">Theory and Practice of Automation in Coq Proofs</span> {.libtitle}
====================================================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span
class="comment">(\* Chapter maintained by Arthur Chargueraud \*)</span>\
\

</div>

<div class="doc">

In a machine-checked proof, every single detail has to be justified.
This can result in huge proof scripts. Fortunately, Coq comes with a
proof-search mechanism and with several decision procedures that enable
the system to automatically synthesize simple pieces of proof.
Automation is very powerful when set up appropriately. The purpose of
this chapter is to explain the basics of working of automation.
<div class="paragraph">

</div>

The chapter is organized in two parts. The first part focuses on a
general mechanism called "proof search." In short, proof search consists
in naively trying to apply lemmas and assumptions in all possible ways.
The second part describes "decision procedures", which are tactics that
are very good at solving proof obligations that fall in some particular
fragment of the logic of Coq.
<div class="paragraph">

</div>

Many of the examples used in this chapter consist of small lemmas that
have been made up to illustrate particular aspects of automation. These
examples are completely independent from the rest of the Software
Foundations course. This chapter also contains some bigger examples
which are used to explain how to use automation in realistic proofs.
These examples are taken from other chapters of the course (mostly from
STLC), and the proofs that we present make use of the tactics from the
library <span class="inlinecode"><span class="id"
type="var">LibTactics.v</span></span>, which is presented in the chapter
<span class="inlinecode"><span class="id"
type="var">UseTactics</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id"
type="var">LibTactics</span>.\
\

</div>

<div class="doc">

Basic Features of Proof Search {.section}
==============================

<div class="paragraph">

</div>

The idea of proof search is to replace a sequence of tactics applying
lemmas and assumptions with a call to a single tactic, for example <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>.
This form of proof automation saves a lot of effort. It typically leads
to much shorter proof scripts, and to scripts that are typically more
robust to change. If one makes a little change to a definition, a proof
that exploits automation probably won't need to be modified at all. Of
course, using too much automation is a bad idea. When a proof script no
longer records the main arguments of a proof, it becomes difficult to
fix it when it gets broken after a change in a definition. Overall, a
reasonable use of automation is generally a big win, as it saves a lot
of time both in building proof scripts and in subsequently maintaining
those proof scripts.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Strength of Proof Search {.section}
------------------------

<div class="paragraph">

</div>

We are going to study four proof-search tactics: <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>,
<span class="inlinecode"><span class="id"
type="tactic">eauto</span></span>, <span class="inlinecode"><span
class="id" type="var">iauto</span></span> and <span
class="inlinecode"><span class="id" type="var">jauto</span></span>. The
tactics <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> and <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> are builtin in Coq. The
tactic <span class="inlinecode"><span class="id"
type="var">iauto</span></span> is a shorthand for the builtin tactic
<span class="inlinecode"><span class="id"
type="tactic">try</span></span> <span class="inlinecode"><span
class="id" type="var">solve</span></span> <span
class="inlinecode">[<span class="id"
type="tactic">intuition</span></span> <span class="inlinecode"><span
class="id" type="tactic">eauto</span>]</span>. The tactic <span
class="inlinecode"><span class="id" type="var">jauto</span></span> is
defined in the library <span class="inlinecode"><span class="id"
type="var">LibTactics</span></span>, and simply performs some
preprocessing of the goal before calling <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span>. The goal of this chapter
is to explain the general principles of proof search and to give rule of
thumbs for guessing which of the four tactics mentioned above is best
suited for solving a given goal.
<div class="paragraph">

</div>

Proof search is a compromise between efficiency and expressiveness, that
is, a tradeoff between how complex goals the tactic can solve and how
much time the tactic requires for terminating. The tactic <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
builds proofs only by using the basic tactics <span
class="inlinecode"><span class="id"
type="tactic">reflexivity</span></span>, <span class="inlinecode"><span
class="id" type="tactic">assumption</span></span>, and <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>.
The tactic <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> can also exploit <span
class="inlinecode"><span class="id" type="tactic">eapply</span></span>.
The tactic <span class="inlinecode"><span class="id"
type="var">jauto</span></span> extends <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> by being able to open
conjunctions and existentials that occur in the context. The tactic
<span class="inlinecode"><span class="id" type="var">iauto</span></span>
is able to deal with conjunctions, disjunctions, and negation in a quite
clever way; however it is not able to open existentials from the
context. Also, <span class="inlinecode"><span class="id"
type="var">iauto</span></span> usually becomes very slow when the goal
involves several disjunctions.
<div class="paragraph">

</div>

Note that proof search tactics never perform any rewriting step (tactics
<span class="inlinecode"><span class="id"
type="tactic">rewrite</span></span>, <span class="inlinecode"><span
class="id" type="tactic">subst</span></span>), nor any case analysis on
an arbitrary data structure or predicate (tactics <span
class="inlinecode"><span class="id" type="tactic">destruct</span></span>
and <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span>), nor any proof by induction
(tactic <span class="inlinecode"><span class="id"
type="tactic">induction</span></span>). So, proof search is really
intended to automate the final steps from the various branches of a
proof. It is not able to discover the overall structure of a proof.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Basics {.section}
------

<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> is able to solve a goal that can be
proved using a sequence of <span class="inlinecode"><span class="id"
type="tactic">intros</span></span>, <span class="inlinecode"><span
class="id" type="tactic">apply</span></span>, <span
class="inlinecode"><span class="id"
type="tactic">assumption</span></span>, and <span
class="inlinecode"><span class="id"
type="tactic">reflexivity</span></span>. Two examples follow. The first
one shows the ability for <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> to call <span class="inlinecode"><span
class="id" type="tactic">reflexivity</span></span> at any time. In fact,
calling <span class="inlinecode"><span class="id"
type="tactic">reflexivity</span></span> is always the first thing that
<span class="inlinecode"><span class="id"
type="tactic">auto</span></span> tries to do.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_by\_reflexivity</span> :\
   2 + 3 = 5.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The second example illustrates a proof where a sequence of two calls to
<span class="inlinecode"><span class="id"
type="tactic">apply</span></span> are needed. The goal is to prove that
if <span class="inlinecode"><span class="id" type="var">Q</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span>
implies <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> for any <span class="inlinecode"><span
class="id" type="var">n</span></span> and if <span
class="inlinecode"><span class="id" type="var">Q</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> holds for
any <span class="inlinecode"><span class="id"
type="var">n</span></span>, then <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode">2</span>
holds.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_by\_apply</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">Q</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">n</span>) <span
style="font-family: arial;">→</span>\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">Q</span> <span
class="id" type="var">n</span>) <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">P</span> 2.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

We can ask <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> to tell us what proof it came up with,
by invoking <span class="inlinecode"><span class="id"
type="var">info\_auto</span></span> in place of <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_by\_apply'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">Q</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">n</span>) <span
style="font-family: arial;">→</span>\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">Q</span> <span
class="id" type="var">n</span>) <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">P</span> 2.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="var">info\_auto</span>. <span class="id"
type="keyword">Qed</span>.\
   <span class="comment">(\* The output is: <span
class="inlinecode"><span class="id" type="tactic">intro</span></span>
<span class="inlinecode"><span class="id" type="var">P</span>;</span>
<span class="inlinecode"><span class="id"
type="tactic">intro</span></span> <span class="inlinecode"><span
class="id" type="var">Q</span>;</span> <span class="inlinecode"><span
class="id" type="tactic">intro</span></span> <span
class="inlinecode"><span class="id"
type="var">H</span>;</span> \*)</span>\
   <span class="comment">(\* followed with <span
class="inlinecode"><span class="id" type="tactic">intro</span></span>
<span class="inlinecode"><span class="id" type="var">H0</span>;</span>
<span class="inlinecode"><span class="id"
type="var">simple</span></span> <span class="inlinecode"><span
class="id" type="tactic">apply</span></span> <span
class="inlinecode"><span class="id" type="var">H</span>;</span> <span
class="inlinecode"><span class="id" type="var">simple</span></span>
<span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">H0</span></span>. \*)</span>\
   <span class="comment">(\* i.e., the sequence <span
class="inlinecode"><span class="id" type="tactic">intros</span></span>
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span class="id" type="var">Q</span></span>
<span class="inlinecode"><span class="id" type="var">H</span></span>
<span class="inlinecode"><span class="id" type="var">H0</span>;</span>
<span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">H</span>;</span> <span class="inlinecode"><span
class="id" type="tactic">apply</span></span> <span
class="inlinecode"><span class="id"
type="var">H0</span></span>. \*)</span>\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> can invoke <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
but not <span class="inlinecode"><span class="id"
type="tactic">eapply</span></span>. So, <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> cannot exploit lemmas whose
instantiation cannot be directly deduced from the proof goal. To exploit
such lemmas, one needs to invoke the tactic <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span>,
which is able to call <span class="inlinecode"><span class="id"
type="tactic">eapply</span></span>.
<div class="paragraph">

</div>

In the following example, the first hypothesis asserts that <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> is true
when <span class="inlinecode"><span class="id"
type="var">Q</span></span> <span class="inlinecode"><span class="id"
type="var">m</span></span> is true for some <span
class="inlinecode"><span class="id" type="var">m</span></span>, and the
goal is to prove that <span class="inlinecode"><span class="id"
type="var">Q</span></span> <span class="inlinecode">1</span> implies
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode">2</span>. This implication follows direction
from the hypothesis by instantiating <span class="inlinecode"><span
class="id" type="var">m</span></span> as the value <span
class="inlinecode">1</span>. The following proof script shows that <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span>
successfully solves the goal, whereas <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> is not able to do so.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_by\_eapply</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> <span class="id" type="var">m</span>, <span
class="id" type="var">Q</span> <span class="id" type="var">m</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">n</span>) <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">Q</span> 1 <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> 2.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="tactic">eauto</span>.
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Remark: Again, we can use <span class="inlinecode"><span class="id"
type="var">info\_eauto</span></span> to see what proof <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span>
comes up with.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Conjunctions {.section}
------------

<div class="paragraph">

</div>

So far, we've seen that <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> is stronger than <span
class="inlinecode"><span class="id" type="tactic">auto</span></span> in
the sense that it can deal with <span class="inlinecode"><span
class="id" type="tactic">eapply</span></span>. In the same way, we are
going to see how <span class="inlinecode"><span class="id"
type="var">jauto</span></span> and <span class="inlinecode"><span
class="id" type="var">iauto</span></span> are stronger than <span
class="inlinecode"><span class="id" type="tactic">auto</span></span> and
<span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> in the sense that they provide better
support for conjunctions.
<div class="paragraph">

</div>

The tactics <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> and <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> can prove a goal of the
form <span class="inlinecode"><span class="id"
type="var">F</span></span> <span class="inlinecode"><span
style="font-family: arial;">∧</span></span> <span
class="inlinecode"><span class="id" type="var">F'</span></span>, where
<span class="inlinecode"><span class="id" type="var">F</span></span> and
<span class="inlinecode"><span class="id" type="var">F'</span></span>
are two propositions, as soon as both <span class="inlinecode"><span
class="id" type="var">F</span></span> and <span class="inlinecode"><span
class="id" type="var">F'</span></span> can be proved in the current
context. An example follows.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_conj\_goal</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>) (<span class="id" type="var">F</span> :
<span class="id" type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">P</span> <span
class="id" type="var">n</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">F</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">F</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">P</span> 2.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

However, when an assumption is a conjunction, <span
class="inlinecode"><span class="id" type="tactic">auto</span></span> and
<span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> are not able to exploit this
conjunction. It can be quite surprising at first that <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span>
can prove very complex goals but that it fails to prove that <span
class="inlinecode"><span class="id" type="var">F</span></span> <span
class="inlinecode"><span style="font-family: arial;">∧</span></span>
<span class="inlinecode"><span class="id" type="var">F'</span></span>
implies <span class="inlinecode"><span class="id"
type="var">F</span></span>. The tactics <span class="inlinecode"><span
class="id" type="var">iauto</span></span> and <span
class="inlinecode"><span class="id" type="var">jauto</span></span> are
able to decompose conjunctions from the context. Here is an example.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_conj\_hyp</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">F</span> <span class="id" type="var">F'</span> : <span
class="id" type="keyword">Prop</span>),\
   <span class="id" type="var">F</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">F'</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">F</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="tactic">eauto</span>.
<span class="id" type="var">jauto</span>. <span
class="comment">(\* or <span class="inlinecode"><span class="id"
type="var">iauto</span></span> \*)</span> <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="var">jauto</span></span> is implemented by first calling a
pre-processing tactic called <span class="inlinecode"><span class="id"
type="var">jauto\_set</span></span>, and then calling <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span>.
So, to understand how <span class="inlinecode"><span class="id"
type="var">jauto</span></span> works, one can directly call the tactic
<span class="inlinecode"><span class="id"
type="var">jauto\_set</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_conj\_hyp'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">F</span> <span class="id" type="var">F'</span> : <span
class="id" type="keyword">Prop</span>),\
   <span class="id" type="var">F</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">F'</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">F</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span>. <span class="id"
type="var">jauto\_set</span>. <span class="id"
type="tactic">eauto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Next is a more involved goal that can be solved by <span
class="inlinecode"><span class="id" type="var">iauto</span></span> and
<span class="inlinecode"><span class="id"
type="var">jauto</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_conj\_more</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">R</span> : <span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="keyword">Prop</span>) (<span class="id"
type="var">F</span> : <span class="id" type="keyword">Prop</span>),\
   (<span class="id" type="var">F</span> <span
style="font-family: arial;">∧</span> (<span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>, (<span class="id"
type="var">Q</span> <span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">R</span> <span class="id" type="var">n</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">n</span>)) <span
style="font-family: arial;">→</span>\
   (<span class="id" type="var">F</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> 2) <span style="font-family: arial;">→</span>\
   <span class="id" type="var">Q</span> 1 <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">P</span> 2 <span
style="font-family: arial;">∧</span> <span class="id"
type="var">F</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="var">jauto</span>. <span class="comment">(\* or <span
class="inlinecode"><span class="id"
type="var">iauto</span></span> \*)</span> <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The strategy of <span class="inlinecode"><span class="id"
type="var">iauto</span></span> and <span class="inlinecode"><span
class="id" type="var">jauto</span></span> is to run a global analysis of
the top-level conjunctions, and then call <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span>. For this reason, those
tactics are not good at dealing with conjunctions that occur as the
conclusion of some universally quantified hypothesis. The following
example illustrates a general weakness of Coq proof search mechanisms.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_conj\_hyp\_forall</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">P</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Q</span> <span class="id" type="var">n</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> 2.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">auto</span>. <span class="id"
type="tactic">eauto</span>. <span class="id" type="var">iauto</span>.
<span class="id" type="var">jauto</span>.\
   <span
class="comment">(\* Nothing works, so we have to do some of the work by hand \*)</span>\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">destruct</span> (<span class="id" type="var">H</span> 2).
<span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

This situation is slightly disappointing, since automation is able to
prove the following goal, which is very similar. The only difference is
that the universal quantification has been distributed over the
conjunction.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solved\_by\_jauto</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>) (<span class="id" type="var">F</span> :
<span class="id" type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">P</span> <span
class="id" type="var">n</span>) <span
style="font-family: arial;">∧</span> (<span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">Q</span> <span
class="id" type="var">n</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> 2.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="var">jauto</span>. <span class="comment">(\* or <span
class="inlinecode"><span class="id"
type="var">iauto</span></span> \*)</span> <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Disjunctions {.section}
------------

<div class="paragraph">

</div>

The tactics <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> and <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> can handle disjunctions
that occur in the goal.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_disj\_goal</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">F</span> <span class="id" type="var">F'</span> : <span
class="id" type="keyword">Prop</span>),\
   <span class="id" type="var">F</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">F</span> <span style="font-family: arial;">∨</span> <span
class="id" type="var">F'</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

However, only <span class="inlinecode"><span class="id"
type="var">iauto</span></span> is able to automate reasoning on the
disjunctions that appear in the context. For example, <span
class="inlinecode"><span class="id" type="var">iauto</span></span> can
prove that <span class="inlinecode"><span class="id"
type="var">F</span></span> <span class="inlinecode"><span
style="font-family: arial;">∨</span></span> <span
class="inlinecode"><span class="id" type="var">F'</span></span> entails
<span class="inlinecode"><span class="id" type="var">F'</span></span>
<span class="inlinecode"><span
style="font-family: arial;">∨</span></span> <span
class="inlinecode"><span class="id" type="var">F</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_disj\_hyp</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">F</span> <span class="id" type="var">F'</span> : <span
class="id" type="keyword">Prop</span>),\
   <span class="id" type="var">F</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">F'</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">F'</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">F</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="tactic">eauto</span>.
<span class="id" type="var">jauto</span>. <span class="id"
type="var">iauto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

More generally, <span class="inlinecode"><span class="id"
type="var">iauto</span></span> can deal with complex combinations of
conjunctions, disjunctions, and negations. Here is an example.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_tauto</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">F1</span> <span class="id" type="var">F2</span> <span
class="id" type="var">F3</span> : <span class="id"
type="keyword">Prop</span>),\
   ((¬<span class="id" type="var">F1</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">F3</span>) <span style="font-family: arial;">∨</span> (<span
class="id" type="var">F2</span> <span
style="font-family: arial;">∧</span> ¬<span class="id"
type="var">F3</span>)) <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">F2</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">F1</span>) <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">F2</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">F3</span>) <span style="font-family: arial;">→</span>\
   ¬<span class="id" type="var">F2</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="var">iauto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

However, the ability of <span class="inlinecode"><span class="id"
type="var">iauto</span></span> to automatically perform a case analysis
on disjunctions comes with a downside: <span class="inlinecode"><span
class="id" type="var">iauto</span></span> may be very slow. If the
context involves several hypotheses with disjunctions, <span
class="inlinecode"><span class="id" type="var">iauto</span></span>
typically generates an exponential number of subgoals on which <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span> is
called. One major advantage of <span class="inlinecode"><span class="id"
type="var">jauto</span></span> compared with <span
class="inlinecode"><span class="id" type="var">iauto</span></span> is
that it never spends time performing this kind of case analyses.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Existentials {.section}
------------

<div class="paragraph">

</div>

The tactics <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span>, <span class="inlinecode"><span
class="id" type="var">iauto</span></span>, and <span
class="inlinecode"><span class="id" type="var">jauto</span></span> can
prove goals whose conclusion is an existential. For example, if the goal
is <span class="inlinecode"><span
style="font-family: arial;">∃</span></span> <span
class="inlinecode"><span class="id" type="var">x</span>,</span> <span
class="inlinecode"><span class="id" type="var">f</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span>, the
tactic <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> introduces an existential variable,
say <span class="inlinecode">?25</span>, in place of <span
class="inlinecode"><span class="id" type="var">x</span></span>. The
remaining goal is <span class="inlinecode"><span class="id"
type="var">f</span></span> <span class="inlinecode">?25</span>, and
<span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> tries to solve this goal, allowing
itself to instantiate <span class="inlinecode">?25</span> with any
appropriate value. For example, if an assumption <span
class="inlinecode"><span class="id" type="var">f</span></span> <span
class="inlinecode">2</span> is available, then the variable <span
class="inlinecode">?25</span> gets instantiated with <span
class="inlinecode">2</span> and the goal is solved, as shown below.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_exists\_goal</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">f</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   <span class="id" type="var">f</span> 2 <span
style="font-family: arial;">→</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">x</span>, <span class="id" type="var">f</span> <span
class="id" type="var">x</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">auto</span>. <span
class="comment">(\* observe that <span class="inlinecode"><span
class="id"
type="tactic">auto</span></span> does not deal with existentials, \*)</span>\
   <span class="id" type="tactic">eauto</span>. <span
class="comment">(\* whereas <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span>, <span class="inlinecode"><span
class="id" type="var">iauto</span></span> and <span
class="inlinecode"><span class="id"
type="var">jauto</span></span> solve the goal \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

A major strength of <span class="inlinecode"><span class="id"
type="var">jauto</span></span> over the other proof search tactics is
that it is able to exploit the existentially-quantified hypotheses,
i.e., those of the form <span class="inlinecode"><span
style="font-family: arial;">∃</span></span> <span
class="inlinecode"><span class="id" type="var">x</span>,</span> <span
class="inlinecode"><span class="id" type="var">P</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">solving\_exists\_hyp</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">f</span> <span class="id" type="var">g</span> : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span class="id" type="var">f</span> <span
class="id" type="var">x</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">g</span> <span class="id" type="var">x</span>) <span
style="font-family: arial;">→</span>\
   (<span style="font-family: arial;">∃</span><span class="id"
type="var">a</span>, <span class="id" type="var">f</span> <span
class="id" type="var">a</span>) <span
style="font-family: arial;">→</span>\
   (<span style="font-family: arial;">∃</span><span class="id"
type="var">a</span>, <span class="id" type="var">g</span> <span
class="id" type="var">a</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">auto</span>. <span class="id"
type="tactic">eauto</span>. <span class="id" type="var">iauto</span>.
<span class="comment">(\* All of these tactics fail, \*)</span>\
   <span class="id" type="var">jauto</span>. <span
class="comment">(\* whereas <span class="inlinecode"><span class="id"
type="var">jauto</span></span> succeeds. \*)</span>\
   <span class="comment">(\* For the details, run <span
class="inlinecode"><span class="id" type="tactic">intros</span>.</span>
<span class="inlinecode"><span class="id"
type="var">jauto\_set</span>.</span> <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Negation {.section}
--------

<div class="paragraph">

</div>

The tactics <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> and <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> suffer from some
limitations with respect to the manipulation of negations, mostly
related to the fact that negation, written <span
class="inlinecode">¬</span> <span class="inlinecode"><span class="id"
type="var">P</span></span>, is defined as <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">False</span></span> but
that the unfolding of this definition is not performed automatically.
Consider the following example.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">negation\_study\_1</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   <span class="id" type="var">P</span> 0 <span
style="font-family: arial;">→</span> (<span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, ¬ <span class="id" type="var">P</span> <span
class="id" type="var">x</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">False</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">H0</span> <span
class="id" type="var">HX</span>.\
   <span class="id" type="tactic">eauto</span>. <span
class="comment">(\* It fails to see that <span class="inlinecode"><span
class="id" type="var">HX</span></span> applies \*)</span>\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">not</span> <span class="id" type="keyword">in</span> ×. <span
class="id" type="tactic">eauto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

For this reason, the tactics <span class="inlinecode"><span class="id"
type="var">iauto</span></span> and <span class="inlinecode"><span
class="id" type="var">jauto</span></span> systematically invoke <span
class="inlinecode"><span class="id" type="tactic">unfold</span></span>
<span class="inlinecode"><span class="id" type="var">not</span></span>
<span class="inlinecode"><span class="id"
type="keyword">in</span></span> <span class="inlinecode">×</span> as
part of their pre-processing. So, they are able to solve the previous
goal right away.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">negation\_study\_2</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   <span class="id" type="var">P</span> 0 <span
style="font-family: arial;">→</span> (<span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, ¬ <span class="id" type="var">P</span> <span
class="id" type="var">x</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">False</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="var">jauto</span>. <span class="comment">(\* or <span
class="inlinecode"><span class="id"
type="var">iauto</span></span> \*)</span> <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

We will come back later on to the behavior of proof search with respect
to the unfolding of definitions.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Equalities {.section}
----------

<div class="paragraph">

</div>

Coq's proof-search feature is not good at exploiting equalities. It can
do very basic operations, like exploiting reflexivity and symmetry, but
that's about it. Here is a simple example that <span
class="inlinecode"><span class="id" type="tactic">auto</span></span> can
solve, by first calling <span class="inlinecode"><span class="id"
type="tactic">symmetry</span></span> and then applying the hypothesis.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">equality\_by\_auto</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">f</span> <span class="id" type="var">g</span> : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span class="id" type="var">f</span> <span
class="id" type="var">x</span> = <span class="id" type="var">g</span>
<span class="id" type="var">x</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">g</span> 2 = <span class="id" type="var">f</span> 2.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

To automate more advanced reasoning on equalities, one should rather try
to use the tactic <span class="inlinecode"><span class="id"
type="tactic">congruence</span></span>, which is presented at the end of
this chapter in the "Decision Procedures" section.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

How Proof Search Works {.section}
======================

</div>

<div class="code code-space">

\

</div>

<div class="doc">

Search Depth {.section}
------------

<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> works as follows. It first tries to
call <span class="inlinecode"><span class="id"
type="tactic">reflexivity</span></span> and <span
class="inlinecode"><span class="id"
type="tactic">assumption</span></span>. If one of these calls solves the
goal, the job is done. Otherwise <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> tries to apply the most
recently introduced assumption that can be applied to the goal without
producing and error. This application produces subgoals. There are two
possible cases. If the sugboals produced can be solved by a recursive
call to <span class="inlinecode"><span class="id"
type="tactic">auto</span></span>, then the job is done. Otherwise, if
this application produces at least one subgoal that <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
cannot solve, then <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> starts over by trying to apply the
second most recently introduced assumption. It continues in a similar
fashion until it finds a proof or until no assumption remains to be
tried.
<div class="paragraph">

</div>

It is very important to have a clear idea of the backtracking process
involved in the execution of the <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> tactic; otherwise its
behavior can be quite puzzling. For example, <span
class="inlinecode"><span class="id" type="tactic">auto</span></span> is
not able to solve the following triviality.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">search\_depth\_0</span> :\
   <span class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">True</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">True</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">True</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

The reason <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> fails to solve the goal is because
there are too many conjunctions. If there had been only five of them,
<span class="inlinecode"><span class="id"
type="tactic">auto</span></span> would have successfully solved the
proof, but six is too many. The tactic <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> limits the number of lemmas
and hypotheses that can be applied in a proof, so as to ensure that the
proof search eventually terminates. By default, the maximal number of
steps is five. One can specify a different bound, writing for example
<span class="inlinecode"><span class="id"
type="tactic">auto</span></span> <span class="inlinecode">6</span> to
search for a proof involving at most six steps. For example, <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
<span class="inlinecode">6</span> would solve the previous lemma.
(Similarly, one can invoke <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> <span class="inlinecode">6</span> or
<span class="inlinecode"><span class="id"
type="tactic">intuition</span></span> <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> <span
class="inlinecode">6</span>.) The argument <span
class="inlinecode"><span class="id" type="var">n</span></span> of <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span> is
called the "search depth." The tactic <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> is simply defined as a
shorthand for <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> <span class="inlinecode">5</span>.
<div class="paragraph">

</div>

The behavior of <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> can be summarized as follows. It
first tries to solve the goal using <span class="inlinecode"><span
class="id" type="tactic">reflexivity</span></span> and <span
class="inlinecode"><span class="id"
type="tactic">assumption</span></span>. If this fails, it tries to apply
a hypothesis (or a lemma that has been registered in the hint database),
and this application produces a number of sugoals. The tactic <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
<span class="inlinecode">(<span class="id" type="var">n</span>-1)</span>
is then called on each of those subgoals. If all the subgoals are
solved, the job is completed, otherwise <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> tries to
apply a different hypothesis.
<div class="paragraph">

</div>

During the process, <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> calls <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
<span class="inlinecode">(<span class="id"
type="var">n</span>-1)</span>, which in turn might call <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
<span class="inlinecode">(<span class="id"
type="var">n</span>-2)</span>, and so on. The tactic <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
<span class="inlinecode">0</span> only tries <span
class="inlinecode"><span class="id"
type="tactic">reflexivity</span></span> and <span
class="inlinecode"><span class="id"
type="tactic">assumption</span></span>, and does not try to apply any
lemma. Overall, this means that when the maximal number of steps allowed
has been exceeded, the <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> tactic stops searching and backtracks
to try and investigate other paths.
<div class="paragraph">

</div>

The following lemma admits a unique proof that involves exactly three
steps. So, <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> proves this goal iff <span
class="inlinecode"><span class="id" type="var">n</span></span> is
greater than three.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">search\_depth\_1</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   <span class="id" type="var">P</span> 0 <span
style="font-family: arial;">→</span>\
   (<span class="id" type="var">P</span> 0 <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> 1) <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">P</span> 1 <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> 2) <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">P</span> 2).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">auto</span> 0. <span
class="comment">(\* does not find the proof \*)</span>\
   <span class="id" type="tactic">auto</span> 1. <span
class="comment">(\* does not find the proof \*)</span>\
   <span class="id" type="tactic">auto</span> 2. <span
class="comment">(\* does not find the proof \*)</span>\
   <span class="id" type="tactic">auto</span> 3. <span
class="comment">(\* finds the proof \*)</span>\
           <span class="comment">(\* more generally, <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
<span class="inlinecode"><span class="id"
type="var">n</span></span> solves the goal if <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">≥</span> <span
class="inlinecode">3</span> \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

We can generalize the example by introducing an assumption asserting
that <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode"><span class="id"
type="var">k</span></span> is derivable from <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">(<span class="id" type="var">k</span>-1)</span> for
all <span class="inlinecode"><span class="id"
type="var">k</span></span>, and keep the assumption <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">0</span>. The tactic <span class="inlinecode"><span
class="id" type="tactic">auto</span></span>, which is the same as <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
<span class="inlinecode">5</span>, is able to derive <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">k</span></span> for all
values of <span class="inlinecode"><span class="id"
type="var">k</span></span> less than 5. For example, it can prove <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">4</span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">search\_depth\_3</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   <span class="comment">(\* Hypothesis H1: \*)</span> (<span class="id"
type="var">P</span> 0) <span style="font-family: arial;">→</span>\
   <span class="comment">(\* Hypothesis H2: \*)</span> (<span
style="font-family: arial;">∀</span><span class="id"
type="var">k</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">k</span>-1) <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">k</span>) <span
style="font-family: arial;">→</span>\
   <span class="comment">(\* Goal:          \*)</span> (<span class="id"
type="var">P</span> 4).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

However, to prove <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">5</span>, one needs
to call at least <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> <span class="inlinecode">6</span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">search\_depth\_4</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   <span class="comment">(\* Hypothesis H1: \*)</span> (<span class="id"
type="var">P</span> 0) <span style="font-family: arial;">→</span>\
   <span class="comment">(\* Hypothesis H2: \*)</span> (<span
style="font-family: arial;">∀</span><span class="id"
type="var">k</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">k</span>-1) <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">k</span>) <span
style="font-family: arial;">→</span>\
   <span class="comment">(\* Goal:          \*)</span> (<span class="id"
type="var">P</span> 5).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="tactic">auto</span> 6.
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Because <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> looks for proofs at a limited depth,
there are cases where <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> can prove a goal <span
class="inlinecode"><span class="id" type="var">F</span></span> and can
prove a goal <span class="inlinecode"><span class="id"
type="var">F'</span></span> but cannot prove <span
class="inlinecode"><span class="id" type="var">F</span></span> <span
class="inlinecode"><span style="font-family: arial;">∧</span></span>
<span class="inlinecode"><span class="id" type="var">F'</span></span>.
In the following example, <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> can prove <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">4</span> but it is not able to prove <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">4</span> <span class="inlinecode"><span
style="font-family: arial;">∧</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">4</span>, because the splitting of the conjunction
consumes one proof step. To prove the conjunction, one needs to increase
the search depth, using at least <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> <span
class="inlinecode">6</span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">search\_depth\_5</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   <span class="comment">(\* Hypothesis H1: \*)</span> (<span class="id"
type="var">P</span> 0) <span style="font-family: arial;">→</span>\
   <span class="comment">(\* Hypothesis H2: \*)</span> (<span
style="font-family: arial;">∀</span><span class="id"
type="var">k</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">k</span>-1) <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">k</span>) <span
style="font-family: arial;">→</span>\
   <span class="comment">(\* Goal:          \*)</span> (<span class="id"
type="var">P</span> 4 <span style="font-family: arial;">∧</span> <span
class="id" type="var">P</span> 4).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="tactic">auto</span> 6.
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Backtracking {.section}
------------

<div class="paragraph">

</div>

In the previous section, we have considered proofs where at each step
there was a unique assumption that <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> could apply. In general,
<span class="inlinecode"><span class="id"
type="tactic">auto</span></span> can have several choices at every step.
The strategy of <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> consists of trying all of the
possibilities (using a depth-first search exploration).
<div class="paragraph">

</div>

To illustrate how automation works, we are going to extend the previous
example with an additional assumption asserting that <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">k</span></span> is also
derivable from <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">(<span class="id"
type="var">k</span>+1)</span>. Adding this hypothesis offers a new
possibility that <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> could consider at every step.
<div class="paragraph">

</div>

There exists a special command that one can use for tracing all the
steps that proof-search considers. To view such a trace, one should
write <span class="inlinecode"><span class="id"
type="var">debug</span></span> <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span>. (For some reason, the command <span
class="inlinecode"><span class="id" type="var">debug</span></span> <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
does not exist, so we have to use the command <span
class="inlinecode"><span class="id" type="var">debug</span></span> <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span>
instead.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">working\_of\_auto\_1</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   <span class="comment">(\* Hypothesis H1: \*)</span> (<span class="id"
type="var">P</span> 0) <span style="font-family: arial;">→</span>\
   <span class="comment">(\* Hypothesis H2: \*)</span> (<span
style="font-family: arial;">∀</span><span class="id"
type="var">k</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">k</span>+1) <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">k</span>) <span
style="font-family: arial;">→</span>\
   <span class="comment">(\* Hypothesis H3: \*)</span> (<span
style="font-family: arial;">∀</span><span class="id"
type="var">k</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">k</span>-1) <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">k</span>) <span
style="font-family: arial;">→</span>\
   <span class="comment">(\* Goal:          \*)</span> (<span class="id"
type="var">P</span> 2).\
 <span
class="comment">(\* Uncomment "debug" in the following line to see the debug trace: \*)</span>\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">P</span> <span
class="id" type="var">H1</span> <span class="id" type="var">H2</span>
<span class="id" type="var">H3</span>. <span
class="comment">(\* debug \*)</span> <span class="id"
type="tactic">eauto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The output message produced by <span class="inlinecode"><span class="id"
type="var">debug</span></span> <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> is as follows.
        depth=5 
        depth=4 apply H3
        depth=3 apply H3
        depth=3 exact H1

The depth indicates the value of <span class="inlinecode"><span
class="id" type="var">n</span></span> with which <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span> is
called. The tactics shown in the message indicate that the first thing
that <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> has tried to do is to apply <span
class="inlinecode"><span class="id" type="var">H3</span></span>. The
effect of applying <span class="inlinecode"><span class="id"
type="var">H3</span></span> is to replace the goal <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">2</span> with the goal <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode">1</span>.
Then, again, <span class="inlinecode"><span class="id"
type="var">H3</span></span> has been applied, changing the goal <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">1</span> into <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode">0</span>.
At that point, the goal was exactly the hypothesis <span
class="inlinecode"><span class="id" type="var">H1</span></span>.
<div class="paragraph">

</div>

It seems that <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> was quite lucky there, as it never
even tried to use the hypothesis <span class="inlinecode"><span
class="id" type="var">H2</span></span> at any time. The reason is that
<span class="inlinecode"><span class="id"
type="tactic">auto</span></span> always tries to use the most recently
introduced hypothesis first, and <span class="inlinecode"><span
class="id" type="var">H3</span></span> is a more recent hypothesis than
<span class="inlinecode"><span class="id" type="var">H2</span></span> in
the goal. So, let's permute the hypotheses <span
class="inlinecode"><span class="id" type="var">H2</span></span> and
<span class="inlinecode"><span class="id" type="var">H3</span></span>
and see what happens.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">working\_of\_auto\_2</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   <span class="comment">(\* Hypothesis H1: \*)</span> (<span class="id"
type="var">P</span> 0) <span style="font-family: arial;">→</span>\
   <span class="comment">(\* Hypothesis H3: \*)</span> (<span
style="font-family: arial;">∀</span><span class="id"
type="var">k</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">k</span>-1) <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">k</span>) <span
style="font-family: arial;">→</span>\
   <span class="comment">(\* Hypothesis H2: \*)</span> (<span
style="font-family: arial;">∀</span><span class="id"
type="var">k</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">k</span>+1) <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">k</span>) <span
style="font-family: arial;">→</span>\
   <span class="comment">(\* Goal:          \*)</span> (<span class="id"
type="var">P</span> 2).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">P</span> <span
class="id" type="var">H1</span> <span class="id" type="var">H3</span>
<span class="id" type="var">H2</span>. <span
class="comment">(\* debug \*)</span> <span class="id"
type="tactic">eauto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

This time, the output message suggests that the proof search
investigates many possibilities. Replacing <span
class="inlinecode"><span class="id" type="var">debug</span></span> <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span>
with <span class="inlinecode"><span class="id"
type="var">info\_eauto</span></span>, we observe that the proof that
<span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> comes up with is actually not the
simplest one. <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">H2</span>;</span> <span class="inlinecode"><span
class="id" type="tactic">apply</span></span> <span
class="inlinecode"><span class="id" type="var">H3</span>;</span> <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
<span class="inlinecode"><span class="id" type="var">H3</span>;</span>
<span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">H3</span>;</span> <span class="inlinecode"><span
class="id" type="tactic">exact</span></span> <span
class="inlinecode"><span class="id" type="var">H1</span></span> This
proof goes through the proof obligation <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode">3</span>,
even though it is not any useful. The following tree drawing describes
all the goals that automation has been through.
        |5||4||3||2||1||0| -- below, tabulation indicates the depth

        [P 2]
        -> [P 3]
           -> [P 4]
              -> [P 5]
                 -> [P 6]
                    -> [P 7]
                    -> [P 5] 
                 -> [P 4]
                    -> [P 5]
                    -> [P 3] 
              --> [P 3]
                 -> [P 4]
                    -> [P 5]
                    -> [P 3] 
                 -> [P 2]
                    -> [P 3]
                    -> [P 1] 
           -> [P 2]
              -> [P 3]
                 -> [P 4]
                    -> [P 5]
                    -> [P 3] 
                 -> [P 2]
                    -> [P 3]
                    -> [P 1] 
              -> [P 1]
                 -> [P 2]
                    -> [P 3]
                    -> [P 1] 
                 -> [P 0]
                    -> !! Done !! 

The first few lines read as follows. To prove <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">2</span>, <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> <span class="inlinecode">5</span> has
first tried to apply <span class="inlinecode"><span class="id"
type="var">H2</span></span>, producing the subgoal <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">3</span>. To solve it, <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> <span
class="inlinecode">4</span> has tried again to apply <span
class="inlinecode"><span class="id" type="var">H2</span></span>,
producing the goal <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">4</span>. Similarly,
the search goes through <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">5</span>, <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">6</span> and <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode">7</span>.
When reaching <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">7</span>, the tactic
<span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> <span class="inlinecode">0</span> is
called but as it is not allowed to try and apply any lemma, it fails.
So, we come back to the goal <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">6</span>, and try
this time to apply hypothesis <span class="inlinecode"><span class="id"
type="var">H3</span></span>, producing the subgoal <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">5</span>. Here again, <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> <span
class="inlinecode">0</span> fails to solve this goal.
<div class="paragraph">

</div>

The process goes on and on, until backtracking to <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">3</span> and trying to apply <span
class="inlinecode"><span class="id" type="var">H2</span></span> three
times in a row, going through <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">2</span> and <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">1</span> and <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode">0</span>.
This search tree explains why <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> came up with a proof starting with
<span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">H2</span></span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Adding Hints {.section}
------------

<div class="paragraph">

</div>

By default, <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> (and <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span>) only tries to apply the
hypotheses that appear in the proof context. There are two possibilities
for telling <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> to exploit a lemma that have been
proved previously: either adding the lemma as an assumption just before
calling <span class="inlinecode"><span class="id"
type="tactic">auto</span></span>, or adding the lemma as a hint, so that
it can be used by every calls to <span class="inlinecode"><span
class="id" type="tactic">auto</span></span>.
<div class="paragraph">

</div>

The first possibility is useful to have <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> exploit a lemma that only
serves at this particular point. To add the lemma as hypothesis, one can
type <span class="inlinecode"><span class="id"
type="tactic">generalize</span></span> <span class="inlinecode"><span
class="id" type="var">mylemma</span>;</span> <span
class="inlinecode"><span class="id" type="tactic">intros</span></span>,
or simply <span class="inlinecode"><span class="id"
type="var">lets</span>:</span> <span class="inlinecode"><span class="id"
type="var">mylemma</span></span> (the latter requires <span
class="inlinecode"><span class="id"
type="var">LibTactics.v</span></span>).
<div class="paragraph">

</div>

The second possibility is useful for lemmas that need to be exploited
several times. The syntax for adding a lemma as a hint is <span
class="inlinecode"><span class="id" type="keyword">Hint</span></span>
<span class="inlinecode"><span class="id"
type="keyword">Resolve</span></span> <span class="inlinecode"><span
class="id" type="var">mylemma</span></span>. For example, the lemma
asserting than any number is less than or equal to itself, <span
class="inlinecode"><span style="font-family: arial;">∀</span></span>
<span class="inlinecode"><span class="id" type="var">x</span>,</span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode">≤</span> <span class="inlinecode"><span
class="id" type="var">x</span></span>, called <span
class="inlinecode"><span class="id" type="var">Le.le\_refl</span></span>
in the Coq standard library, can be added as a hint as follows.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Resolve</span> <span class="id"
type="var">Le.le\_refl</span>.\
\

</div>

<div class="doc">

A convenient shorthand for adding all the constructors of an inductive
datatype as hints is the command <span class="inlinecode"><span
class="id" type="keyword">Hint</span></span> <span
class="inlinecode"><span class="id"
type="var">Constructors</span></span> <span class="inlinecode"><span
class="id" type="var">mydatatype</span></span>.
<div class="paragraph">

</div>

Warning: some lemmas, such as transitivity results, should not be added
as hints as they would very badly affect the performance of proof
search. The description of this problem and the presentation of a
general work-around for transitivity lemmas appear further on.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Integration of Automation in Tactics {.section}
------------------------------------

<div class="paragraph">

</div>

The library "LibTactics" introduces a convenient feature for invoking
automation after calling a tactic. In short, it suffices to add the
symbol star (<span class="inlinecode">×</span>) to the name of a tactic.
For example, <span class="inlinecode"><span class="id"
type="tactic">apply</span>×</span> <span class="inlinecode"><span
class="id" type="var">H</span></span> is equivalent to <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
<span class="inlinecode"><span class="id" type="var">H</span>;</span>
<span class="inlinecode"><span class="id"
type="var">auto\_star</span></span>, where <span
class="inlinecode"><span class="id" type="var">auto\_star</span></span>
is a tactic that can be defined as needed.
<div class="paragraph">

</div>

The definition of <span class="inlinecode"><span class="id"
type="var">auto\_star</span></span>, which determines the meaning of the
star symbol, can be modified whenever needed. Simply write:
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="keyword">Ltac</span> <span class="id"
type="var">auto\_star</span> ::= <span class="id"
type="var">a\_new\_definition</span>.
<div class="paragraph">

</div>

</div>

Observe the use of <span class="inlinecode">::=</span> instead of <span
class="inlinecode">:=</span>, which indicates that the tactic is being
rebound to a new definition. So, the default definition is as follows.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Ltac</span> <span class="id"
type="var">auto\_star</span> ::= <span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> [
<span class="id" type="var">jauto</span> ].\
\

</div>

<div class="doc">

Nearly all standard Coq tactics and all the tactics from "LibTactics"
can be called with a star symbol. For example, one can invoke <span
class="inlinecode"><span class="id" type="tactic">subst</span>×</span>,
<span class="inlinecode"><span class="id"
type="tactic">destruct</span>×</span> <span class="inlinecode"><span
class="id" type="var">H</span></span>, <span class="inlinecode"><span
class="id" type="var">inverts</span>×</span> <span
class="inlinecode"><span class="id" type="var">H</span></span>, <span
class="inlinecode"><span class="id" type="var">lets</span>×</span> <span
class="inlinecode"><span class="id" type="var">I</span>:</span> <span
class="inlinecode"><span class="id" type="var">H</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span>, <span
class="inlinecode"><span class="id"
type="var">specializes</span>×</span> <span class="inlinecode"><span
class="id" type="var">H</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span>, and so on... There are two
notable exceptions. The tactic <span class="inlinecode"><span class="id"
type="tactic">auto</span>×</span> is just another name for the tactic
<span class="inlinecode"><span class="id"
type="var">auto\_star</span></span>. And the tactic <span
class="inlinecode"><span class="id" type="tactic">apply</span>×</span>
<span class="inlinecode"><span class="id" type="var">H</span></span>
calls <span class="inlinecode"><span class="id"
type="tactic">eapply</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> (or the more powerful <span
class="inlinecode"><span class="id" type="var">applys</span></span>
<span class="inlinecode"><span class="id" type="var">H</span></span> if
needed), and then calls <span class="inlinecode"><span class="id"
type="var">auto\_star</span></span>. Note that there is no <span
class="inlinecode"><span class="id" type="tactic">eapply</span>×</span>
<span class="inlinecode"><span class="id" type="var">H</span></span>
tactic, use <span class="inlinecode"><span class="id"
type="tactic">apply</span>×</span> <span class="inlinecode"><span
class="id" type="var">H</span></span> instead.
<div class="paragraph">

</div>

In large developments, it can be convenient to use two degrees of
automation. Typically, one would use a fast tactic, like <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>,
and a slower but more powerful tactic, like <span
class="inlinecode"><span class="id" type="var">jauto</span></span>. To
allow for a smooth coexistence of the two form of automation, <span
class="inlinecode"><span class="id"
type="var">LibTactics.v</span></span> also defines a "tilde" version of
tactics, like <span class="inlinecode"><span class="id"
type="tactic">apply</span>¬</span> <span class="inlinecode"><span
class="id" type="var">H</span></span>, <span class="inlinecode"><span
class="id" type="tactic">destruct</span>¬</span> <span
class="inlinecode"><span class="id" type="var">H</span></span>, <span
class="inlinecode"><span class="id" type="tactic">subst</span>¬</span>,
<span class="inlinecode"><span class="id"
type="tactic">auto</span>¬</span> and so on. The meaning of the tilde
symbol is described by the <span class="inlinecode"><span class="id"
type="var">auto\_tilde</span></span> tactic, whose default
implementation is <span class="inlinecode"><span class="id"
type="tactic">auto</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Ltac</span> <span class="id"
type="var">auto\_tilde</span> ::= <span class="id"
type="tactic">auto</span>.\
\

</div>

<div class="doc">

In the examples that follow, only <span class="inlinecode"><span
class="id" type="var">auto\_star</span></span> is needed.
<div class="paragraph">

</div>

An alternative, possibly more efficient version of auto\_star is the
following":
<div class="paragraph">

</div>

Ltac auto\_star ::= try solve <span class="inlinecode"></span> <span
class="inlinecode"><span class="id" type="var">eassumption</span></span>
<span class="inlinecode">|</span> <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> <span
class="inlinecode">|</span> <span class="inlinecode"><span class="id"
type="var">jauto</span></span> <span class="inlinecode"></span>.
<div class="paragraph">

</div>

With the above definition, <span class="inlinecode"><span class="id"
type="var">auto\_star</span></span> first tries to solve the goal using
the assumptions; if it fails, it tries using <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>,
and if this still fails, then it calls <span class="inlinecode"><span
class="id" type="var">jauto</span></span>. Even though <span
class="inlinecode"><span class="id" type="var">jauto</span></span> is
strictly stronger than <span class="inlinecode"><span class="id"
type="var">eassumption</span></span> and <span class="inlinecode"><span
class="id" type="tactic">auto</span></span>, it makes sense to call
these tactics first, because, when the succeed, they save a lot of time,
and when they fail to prove the goal, they fail very quickly.".
<div class="paragraph">

</div>

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Examples of Use of Automation {.section}
=============================

<div class="paragraph">

</div>

Let's see how to use proof search in practice on the main theorems of
the "Software Foundations" course, proving in particular results such as
determinism, preservation and progress.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Determinism {.section}
-----------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">DeterministicImp</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Imp</span>.\
\

</div>

<div class="doc">

Recall the original proof of the determinism lemma for the IMP language,
shown below.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_deterministic</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st1</span> <span class="id" type="var">st2</span>,\
   <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st1</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st2</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">st1</span> = <span class="id"
type="var">st2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st1</span> <span class="id" type="var">st2</span>
<span class="id" type="var">E1</span> <span class="id"
type="var">E2</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>.\
   (<span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>); <span class="id"
type="tactic">intros</span> <span class="id" type="var">st2</span> <span
class="id" type="var">E2</span>; <span class="id"
type="tactic">inversion</span> <span class="id" type="var">E2</span>;
<span class="id" type="tactic">subst</span>.\
   <span class="id" type="var">Case</span> "E\_Skip". <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "E\_Ass". <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "E\_Seq".\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">EQ1</span>.\
       <span class="id" type="var">SCase</span> "Proof of assertion".
<span class="id" type="tactic">apply</span> <span class="id"
type="var">IHE1\_1</span>; <span class="id"
type="tactic">assumption</span>.\
     <span class="id" type="tactic">subst</span> <span class="id"
type="var">st'0</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHE1\_2</span>. <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "E\_IfTrue".\
     <span class="id" type="var">SCase</span> "b1 evaluates to true".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHE1</span>. <span class="id"
type="tactic">assumption</span>.\
     <span class="id" type="var">SCase</span> "b1 evaluates to false
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H5</span>.\
   <span class="id" type="var">Case</span> "E\_IfFalse".\
     <span class="id" type="var">SCase</span> "b1 evaluates to true
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H5</span>.\
     <span class="id" type="var">SCase</span> "b1 evaluates to false".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHE1</span>. <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "E\_WhileEnd".\
     <span class="id" type="var">SCase</span> "b1 evaluates to true".\
       <span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> "b1 evaluates to false
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H2</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H2</span>.\
   <span class="id" type="var">Case</span> "E\_WhileLoop".\
     <span class="id" type="var">SCase</span> "b1 evaluates to true
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H4</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H4</span>.\
     <span class="id" type="var">SCase</span> "b1 evaluates to false".\
       <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">EQ1</span>.\
         <span class="id" type="var">SSCase</span> "Proof of assertion".
<span class="id" type="tactic">apply</span> <span class="id"
type="var">IHE1\_1</span>; <span class="id"
type="tactic">assumption</span>.\
       <span class="id" type="tactic">subst</span> <span class="id"
type="var">st'0</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHE1\_2</span>. <span class="id"
type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Exercise: rewrite this proof using <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> whenever possible. (The
solution uses <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> 9 times.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_deterministic'</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st1</span> <span class="id" type="var">st2</span>,\
   <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st1</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st2</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">st1</span> = <span class="id"
type="var">st2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

In fact, using automation is not just a matter of calling <span
class="inlinecode"><span class="id" type="tactic">auto</span></span> in
place of one or two other tactics. Using automation is about rethinking
the organization of sequences of tactics so as to minimize the effort
involved in writing and maintaining the proof. This process is eased by
the use of the tactics from <span class="inlinecode"><span class="id"
type="var">LibTactics.v</span></span>. So, before trying to optimize the
way automation is used, let's first rewrite the proof of determinism:
<div class="paragraph">

</div>

-   use <span class="inlinecode"><span class="id"
    type="var">introv</span></span> <span class="inlinecode"><span
    class="id" type="var">H</span></span> instead of <span
    class="inlinecode"><span class="id"
    type="tactic">intros</span></span> <span class="inlinecode"><span
    class="id" type="var">x</span></span> <span class="inlinecode"><span
    class="id" type="var">H</span></span>,
-   use <span class="inlinecode"><span class="id"
    type="var">gen</span></span> <span class="inlinecode"><span
    class="id" type="var">x</span></span> instead of <span
    class="inlinecode"><span class="id"
    type="tactic">generalize</span></span> <span
    class="inlinecode"><span class="id"
    type="tactic">dependent</span></span> <span class="inlinecode"><span
    class="id" type="var">x</span></span>,
-   use <span class="inlinecode"><span class="id"
    type="var">inverts</span></span> <span class="inlinecode"><span
    class="id" type="var">H</span></span> instead of <span
    class="inlinecode"><span class="id"
    type="tactic">inversion</span></span> <span class="inlinecode"><span
    class="id" type="var">H</span>;</span> <span
    class="inlinecode"><span class="id"
    type="tactic">subst</span></span>,
-   use <span class="inlinecode"><span class="id"
    type="var">tryfalse</span></span> to handle contradictions, and get
    rid of the cases where <span class="inlinecode"><span class="id"
    type="var">beval</span></span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span class="id" type="var">b1</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">true</span></span> and <span
    class="inlinecode"><span class="id" type="var">beval</span></span>
    <span class="inlinecode"><span class="id"
    type="var">st</span></span> <span class="inlinecode"><span
    class="id" type="var">b1</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">false</span></span> both appear in the
    context,
-   stop using <span class="inlinecode"><span class="id"
    type="var">ceval\_cases</span></span> to label subcases.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_deterministic''</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st1</span> <span class="id" type="var">st2</span>,\
   <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st1</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st2</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">st1</span> = <span class="id"
type="var">st2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">introv</span> <span class="id"
type="var">E1</span> <span class="id" type="var">E2</span>. <span
class="id" type="var">gen</span> <span class="id"
type="var">st2</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">E1</span>; <span class="id" type="tactic">intros</span>;
<span class="id" type="var">inverts</span> <span class="id"
type="var">E2</span>; <span class="id" type="var">tryfalse</span>.\
   <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>). <span
class="id" type="tactic">auto</span>. <span class="id"
type="tactic">subst</span>. <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>). <span
class="id" type="tactic">auto</span>. <span class="id"
type="tactic">subst</span>. <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

To obtain a nice clean proof script, we have to remove the calls <span
class="inlinecode"><span class="id" type="tactic">assert</span></span>
<span class="inlinecode">(<span class="id" type="var">st'</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">st'0</span>)</span>. Such a tactic invokation is
not nice because it refers to some variables whose name has been
automatically generated. This kind of tactics tend to be very brittle.
The tactic <span class="inlinecode"><span class="id"
type="tactic">assert</span></span> <span class="inlinecode">(<span
class="id" type="var">st'</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">st'0</span>)</span> is used to assert the conclusion that we
want to derive from the induction hypothesis. So, rather than stating
this conclusion explicitly, we are going to ask Coq to instantiate the
induction hypothesis, using automation to figure out how to instantiate
it. The tactic <span class="inlinecode"><span class="id"
type="var">forwards</span></span>, described in <span
class="inlinecode"><span class="id"
type="var">LibTactics.v</span></span> precisely helps with instantiating
a fact. So, let's see how it works out on our example.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_deterministic'''</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st1</span> <span class="id" type="var">st2</span>,\
   <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st1</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st2</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">st1</span> = <span class="id"
type="var">st2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* Let's replay the proof up to the <span
class="inlinecode"><span class="id"
type="tactic">assert</span></span> tactic. \*)</span>\
   <span class="id" type="var">introv</span> <span class="id"
type="var">E1</span> <span class="id" type="var">E2</span>. <span
class="id" type="var">gen</span> <span class="id"
type="var">st2</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">E1</span>; <span class="id" type="tactic">intros</span>;
<span class="id" type="var">inverts</span> <span class="id"
type="var">E2</span>; <span class="id" type="var">tryfalse</span>.\
   <span class="id" type="tactic">auto</span>. <span class="id"
type="tactic">auto</span>.\
   <span
class="comment">(\* We duplicate the goal for comparing different proofs. \*)</span>\
   <span class="id" type="var">dup</span> 4.\
\
   <span class="comment">(\* The old proof: \*)</span>\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>). <span
class="id" type="tactic">apply</span> <span class="id"
type="var">IHE1\_1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">H1</span>.\
     <span class="comment">(\* produces <span class="inlinecode"><span
class="id" type="var">H</span>:</span> <span class="inlinecode"><span
class="id" type="var">st'</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">st'0</span></span>. \*)</span> <span class="id"
type="var">skip</span>.\
\
   <span
class="comment">(\* The new proof, without automation: \*)</span>\
   <span class="id" type="var">forwards</span>: <span class="id"
type="var">IHE1\_1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">H1</span>.\
     <span class="comment">(\* produces <span class="inlinecode"><span
class="id" type="var">H</span>:</span> <span class="inlinecode"><span
class="id" type="var">st'</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">st'0</span></span>. \*)</span> <span class="id"
type="var">skip</span>.\
\
   <span class="comment">(\* The new proof, with automation: \*)</span>\
   <span class="id" type="var">forwards</span>: <span class="id"
type="var">IHE1\_1</span>. <span class="id" type="tactic">eauto</span>.\
     <span class="comment">(\* produces <span class="inlinecode"><span
class="id" type="var">H</span>:</span> <span class="inlinecode"><span
class="id" type="var">st'</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">st'0</span></span>. \*)</span> <span class="id"
type="var">skip</span>.\
\
   <span
class="comment">(\* The new proof, with integrated automation: \*)</span>\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHE1\_1</span>.\
     <span class="comment">(\* produces <span class="inlinecode"><span
class="id" type="var">H</span>:</span> <span class="inlinecode"><span
class="id" type="var">st'</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">st'0</span></span>. \*)</span> <span class="id"
type="var">skip</span>.\
\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

To polish the proof script, it remains to factorize the calls to <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>,
using the star symbol. The proof of determinism can then be rewritten in
only four lines, including no more than 10 tactics.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_deterministic''''</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st1</span> <span class="id" type="var">st2</span>,\
   <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st1</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st2</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">st1</span> = <span class="id"
type="var">st2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">introv</span> <span class="id"
type="var">E1</span> <span class="id" type="var">E2</span>. <span
class="id" type="var">gen</span> <span class="id"
type="var">st2</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">E1</span>; <span class="id" type="tactic">intros</span>;
<span class="id" type="var">inverts</span>× <span class="id"
type="var">E2</span>; <span class="id" type="var">tryfalse</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHE1\_1</span>. <span class="id"
type="tactic">subst</span>×.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHE1\_1</span>. <span class="id"
type="tactic">subst</span>×.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">DeterministicImp</span>.\
\

</div>

<div class="doc">

Preservation for STLC {.section}
---------------------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">PreservationProgressStlc</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id"
type="var">StlcProp</span>.\
   <span class="id" type="keyword">Import</span> <span class="id"
type="var">STLC</span>.\
   <span class="id" type="keyword">Import</span> <span class="id"
type="var">STLCProp</span>.\
\

</div>

<div class="doc">

Consider the proof of perservation of STLC, shown below. This proof
already uses <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> through the triple-dot mechanism.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">preservation</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">t'</span> <span class="id"
type="var">T</span>,\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t'</span> <span
class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">t'</span> <span
class="id" type="var">T</span> <span class="id" type="var">HT</span>.
<span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">t'</span>.\
   (<span class="id" type="var">has\_type\_cases</span> (<span
class="id" type="tactic">induction</span> <span class="id"
type="var">HT</span>) <span class="id" type="var">Case</span>); <span
class="id" type="tactic">intros</span> <span class="id"
type="var">t'</span> <span class="id" type="var">HE</span>; <span
class="id" type="tactic">subst</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="var">Case</span> "T\_Var".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>.\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>.\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>; <span class="id" type="tactic">subst</span>...\
     <span
class="comment">(\* (step\_cases (inversion HE) SCase); subst...\*)</span>\
     <span
class="comment">(\* The ST\_App1 and ST\_App2 cases are immediate by induction, and\
        auto takes care of them \*)</span>\
     <span class="id" type="var">SCase</span> "ST\_AppAbs".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">substitution\_preserves\_typing</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">T~11~</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT1</span>...\
   <span class="id" type="var">Case</span> "T\_True".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>.\
   <span class="id" type="var">Case</span> "T\_False".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>.\
   <span class="id" type="var">Case</span> "T\_If".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>; <span class="id" type="tactic">subst</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Exercise: rewrite this proof using tactics from <span
class="inlinecode"><span class="id" type="var">LibTactics</span></span>
and calling automation using the star symbol rather than the triple-dot
notation. More precisely, make use of the tactics <span
class="inlinecode"><span class="id" type="var">inverts</span>×</span>
and <span class="inlinecode"><span class="id"
type="var">applys</span>×</span> to call <span class="inlinecode"><span
class="id" type="tactic">auto</span>×</span> after a call to <span
class="inlinecode"><span class="id" type="var">inverts</span></span> or
to <span class="inlinecode"><span class="id"
type="var">applys</span></span>. The solution is three lines long.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">preservation'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">t'</span> <span class="id"
type="var">T</span>,\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t'</span> <span
class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Progress for STLC {.section}
-----------------

<div class="paragraph">

</div>

Consider the proof of the progress theorem.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="tactic">progress</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">T</span>,\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">∨</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>, <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
class="id" type="var">Ht</span>.\
   <span class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   (<span class="id" type="var">has\_type\_cases</span> (<span
class="id" type="tactic">induction</span> <span class="id"
type="var">Ht</span>) <span class="id" type="var">Case</span>); <span
class="id" type="tactic">subst</span> <span
style="font-family: serif; font-size:85%;">Γ</span>...\
   <span class="id" type="var">Case</span> "T\_Var".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id"
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
         <span style="font-family: arial;">∃</span>([<span class="id"
type="var">x0</span>:=<span class="id" type="var">t~2~</span>]<span
class="id" type="var">t</span>)...\
       <span class="id" type="var">SSCase</span> "t~2~ steps".\
        <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~2~'</span> <span class="id"
type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~'</span>)...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)...\
   <span class="id" type="var">Case</span> "T\_If".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>...\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">t~1~</span>; <span class="id" type="tactic">try</span> <span
class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>...\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>. <span style="font-family: arial;">∃</span>(<span
class="id" type="var">tif</span> <span class="id" type="var">x0</span>
<span class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>)...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Exercise: optimize the above proof. Hint: make use of <span
class="inlinecode"><span class="id"
type="tactic">destruct</span>×</span> and <span class="inlinecode"><span
class="id" type="var">inverts</span>×</span>. The solution consists of
10 short lines.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">progress'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">T</span>,\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">∨</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>, <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">PreservationProgressStlc</span>.\
\

</div>

<div class="doc">

BigStep and SmallStep {.section}
---------------------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Semantics</span>.\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id"
type="var">Smallstep</span>.\
\

</div>

<div class="doc">

Consider the proof relating a small-step reduction judgment to a
big-step reduction judgment.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">multistep\_\_eval</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">v</span>,\
   <span class="id" type="var">normal\_form\_of</span> <span class="id"
type="var">t</span> <span class="id" type="var">v</span> <span
style="font-family: arial;">→</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">n</span>, <span class="id" type="var">v</span> = <span
class="id" type="var">C</span> <span class="id" type="var">n</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">v</span> <span
class="id" type="var">Hnorm</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">normal\_form\_of</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hnorm</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hnorm</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">Hs</span> <span class="id" type="var">Hnf</span>];
<span class="id" type="tactic">clear</span> <span class="id"
type="var">Hnorm</span>.\
   <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">nf\_same\_as\_value</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hnf</span>. <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">Hnf</span>. <span class="id" type="tactic">clear</span> <span
class="id" type="var">Hnf</span>.\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">n</span>. <span class="id" type="tactic">split</span>. <span
class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">multi\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Hs</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">subst</span>.\
   <span class="id" type="var">Case</span> "multi\_refl".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Const</span>.\
   <span class="id" type="var">Case</span> "multi\_step".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">step\_\_eval</span>. <span class="id"
type="var">eassumption</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHHs</span>.
<span class="id" type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Our goal is to optimize the above proof. It is generally easier to
isolate inductions into separate lemmas. So, we are going to first prove
an intermediate result that consists of the judgment over which the
induction is being performed.
<div class="paragraph">

</div>

Exercise: prove the following result, using tactics <span
class="inlinecode"><span class="id" type="var">introv</span></span>,
<span class="inlinecode"><span class="id"
type="tactic">induction</span></span> and <span class="inlinecode"><span
class="id" type="tactic">subst</span></span>, and <span
class="inlinecode"><span class="id" type="tactic">apply</span>×</span>.
The solution is 3 lines long.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">multistep\_eval\_ind</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">v</span>,\
   <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">v</span> <span style="font-family: arial;">→</span> <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">C</span> <span
class="id" type="var">n</span> = <span class="id" type="var">v</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Exercise: using the lemma above, simplify the proof of the result <span
class="inlinecode"><span class="id"
type="var">multistep\_\_eval</span></span>. You should use the tactics
<span class="inlinecode"><span class="id"
type="var">introv</span></span>, <span class="inlinecode"><span
class="id" type="var">inverts</span></span>, <span
class="inlinecode"><span class="id" type="tactic">split</span>×</span>
and <span class="inlinecode"><span class="id"
type="tactic">apply</span>×</span>. The solution is 2 lines long.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">multistep\_\_eval'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">v</span>,\
   <span class="id" type="var">normal\_form\_of</span> <span class="id"
type="var">t</span> <span class="id" type="var">v</span> <span
style="font-family: arial;">→</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">n</span>, <span class="id" type="var">v</span> = <span
class="id" type="var">C</span> <span class="id" type="var">n</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

If we try to combine the two proofs into a single one, we will likely
fail, because of a limitation of the <span class="inlinecode"><span
class="id" type="tactic">induction</span></span> tactic. Indeed, this
tactic looses information when applied to a predicate whose arguments
are not reduced to variables, such as <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒\*</span></span> <span
class="inlinecode">(<span class="id" type="var">C</span></span> <span
class="inlinecode"><span class="id" type="var">n</span>)</span>. You
will thus need to use the more powerful tactic called <span
class="inlinecode"><span class="id"
type="tactic">dependent</span></span> <span class="inlinecode"><span
class="id" type="tactic">induction</span></span>. This tactic is
available only after importing the <span class="inlinecode"><span
class="id" type="var">Program</span></span> library, as shown below.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id"
type="var">Program</span>.\
\

</div>

<div class="doc">

Exercise: prove the lemma <span class="inlinecode"><span class="id"
type="var">multistep\_\_eval</span></span> without invoking the lemma
<span class="inlinecode"><span class="id"
type="var">multistep\_eval\_ind</span></span>, that is, by inlining the
proof by induction involved in <span class="inlinecode"><span class="id"
type="var">multistep\_eval\_ind</span></span>, using the tactic <span
class="inlinecode"><span class="id"
type="tactic">dependent</span></span> <span class="inlinecode"><span
class="id" type="tactic">induction</span></span> instead of <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span>. The solution is 5 lines long.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">multistep\_\_eval''</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">v</span>,\
   <span class="id" type="var">normal\_form\_of</span> <span class="id"
type="var">t</span> <span class="id" type="var">v</span> <span
style="font-family: arial;">→</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">n</span>, <span class="id" type="var">v</span> = <span
class="id" type="var">C</span> <span class="id" type="var">n</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Semantics</span>.\
\

</div>

<div class="doc">

Preservation for STLCRef {.section}
------------------------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">PreservationProgressReferences</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id"
type="var">References</span>.\
   <span class="id" type="keyword">Import</span> <span class="id"
type="var">STLCRef</span>.\
   <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Resolve</span> <span class="id"
type="var">store\_weakening</span> <span class="id"
type="var">extends\_refl</span>.\
\

</div>

<div class="doc">

The proof of preservation for <span class="inlinecode"><span class="id"
type="var">STLCRef</span></span> can be found in chapter <span
class="inlinecode"><span class="id" type="var">References</span></span>.
It contains 58 lines (not counting the labelling of cases). The
optimized proof script is more than twice shorter. The following
material explains how to build the optimized proof script. The resulting
optimized proof script for the preservation theorem appears afterwards.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">preservation</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span> <span class="id" type="var">T</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span>,\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">ST</span> <span
class="id" type="var">t</span> <span class="id" type="var">T</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">t</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t'</span> / <span class="id" type="var">st'</span>
<span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>,\
     (<span class="id" type="var">extends</span> <span class="id"
type="var">ST'</span> <span class="id" type="var">ST</span> <span
style="font-family: arial;">∧</span>\
      <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">ST'</span> <span
class="id" type="var">t'</span> <span class="id" type="var">T</span>
<span style="font-family: arial;">∧</span>\
      <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST'</span> <span class="id"
type="var">st'</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* old: <span class="inlinecode"><span
class="id" type="keyword">Proof</span>.</span> <span
class="inlinecode"><span class="id" type="keyword">with</span></span>
<span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> <span class="inlinecode"><span
class="id" type="keyword">using</span></span> <span
class="inlinecode"><span class="id"
type="var">store\_weakening</span>,</span> <span
class="inlinecode"><span class="id"
type="var">extends\_refl</span>.</span> \
      new: <span class="inlinecode"><span class="id"
type="keyword">Proof</span>.</span>, and the two lemmas are registered as hints\
      before the proof of the lemma, possibly inside a section in\
      order to restrict the scope of the hints. \*)</span>\
\
   <span class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>. <span class="id"
type="var">introv</span> <span class="id" type="var">Ht</span>. <span
class="id" type="var">gen</span> <span class="id" type="var">t'</span>.\
   (<span class="id" type="var">has\_type\_cases</span> (<span
class="id" type="tactic">induction</span> <span class="id"
type="var">Ht</span>) <span class="id" type="var">Case</span>); <span
class="id" type="var">introv</span> <span class="id"
type="var">HST</span> <span class="id" type="var">Hstep</span>;\
     <span class="comment">(\* old: <span class="inlinecode"><span
class="id" type="tactic">subst</span>;</span> <span
class="inlinecode"><span class="id" type="tactic">try</span></span>
<span class="inlinecode">(<span class="id"
type="var">solve</span></span> <span class="inlinecode"><span class="id"
type="tactic">by</span></span> <span class="inlinecode"><span class="id"
type="tactic">inversion</span>);</span> <span class="inlinecode"><span
class="id" type="tactic">inversion</span></span> <span
class="inlinecode"><span class="id" type="var">Hstep</span>;</span>
<span class="inlinecode"><span class="id"
type="tactic">subst</span>;</span> <span class="inlinecode"><span
class="id" type="tactic">try</span></span> <span
class="inlinecode">(<span class="id" type="tactic">eauto</span></span>
<span class="inlinecode"><span class="id"
type="keyword">using</span></span> <span class="inlinecode"><span
class="id" type="var">store\_weakening</span>,</span> <span
class="inlinecode"><span class="id"
type="var">extends\_refl</span>)</span> \
        new: <span class="inlinecode"><span class="id"
type="tactic">subst</span></span> <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>;</span> <span
class="inlinecode"><span class="id" type="var">inverts</span></span>
<span class="inlinecode"><span class="id"
type="var">Hstep</span>;</span> <span class="inlinecode"><span
class="id" type="tactic">eauto</span>.</span>\
        We want to be more precise on what exactly we substitute,\
        and we do not want to call <span class="inlinecode"><span
class="id" type="tactic">try</span></span> <span
class="inlinecode">(<span class="id" type="var">solve</span></span>
<span class="inlinecode"><span class="id" type="tactic">by</span></span>
<span class="inlinecode"><span class="id"
type="tactic">inversion</span>)</span> which\
        is way to slow. \*)</span>\
    <span class="id" type="tactic">subst</span> <span
style="font-family: serif; font-size:85%;">Γ</span>; <span class="id"
type="var">inverts</span> <span class="id" type="var">Hstep</span>;
<span class="id" type="tactic">eauto</span>.\
\
   <span class="id" type="var">Case</span> "T\_App".\
   <span class="id" type="var">SCase</span> "ST\_AppAbs".\
   <span class="comment">(\* old:\
       exists ST. inversion Ht1; subst.\

      split; try split... eapply substitution\_preserves\_typing... \*)</span>\
   <span class="comment">(\* new: we use <span class="inlinecode"><span
class="id" type="var">inverts</span></span> in place of <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span> and <span class="inlinecode"><span
class="id" type="var">splits</span></span> to\
      split the conjunction, and <span class="inlinecode"><span
class="id" type="var">applys</span>×</span> in place of <span
class="inlinecode"><span class="id"
type="tactic">eapply</span>...</span> \*)</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">ST</span>. <span class="id" type="var">inverts</span> <span
class="id" type="var">Ht1</span>. <span class="id"
type="var">splits</span>×. <span class="id" type="var">applys</span>×
<span class="id" type="var">substitution\_preserves\_typing</span>.\
\
   <span class="id" type="var">SCase</span> "ST\_App1".\
   <span class="comment">(\* old:  \
       eapply IHHt1 in H0...\
       inversion H0 as <span class="inlinecode"><span class="id"
type="var">ST'</span></span> <span class="inlinecode">[<span class="id"
type="var">Hext</span></span> <span class="inlinecode">[<span class="id"
type="var">Hty</span></span> <span class="inlinecode"><span class="id"
type="var">Hsty</span>]]</span>.\
       exists ST'... \*)</span>\
   <span class="comment">(\* new: The tactic <span
class="inlinecode"><span class="id" type="tactic">eapply</span></span>
<span class="inlinecode"><span class="id" type="var">IHHt1</span></span>
<span class="inlinecode"><span class="id"
type="keyword">in</span></span> <span class="inlinecode"><span
class="id" type="var">H0</span>...</span> applies <span
class="inlinecode"><span class="id"
type="var">IHHt1</span></span> to <span class="inlinecode"><span
class="id" type="var">H0</span></span>.\
      But <span class="inlinecode"><span class="id"
type="var">H0</span></span> is only thing that <span
class="inlinecode"><span class="id"
type="var">IHHt1</span></span> could be applied to, so\
      there <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> can figure this out on its own. The tactic\
      <span class="inlinecode"><span class="id"
type="var">forwards</span></span> is used to instantiate all the arguments of <span
class="inlinecode"><span class="id" type="var">IHHt1</span></span>,\

     producing existential variables and subgoals when needed. \*)</span>\
   <span class="id" type="var">forwards</span>: <span class="id"
type="var">IHHt1</span>. <span class="id" type="tactic">eauto</span>.
<span class="id" type="tactic">eauto</span>. <span class="id"
type="tactic">eauto</span>.\
   <span
class="comment">(\* At this point, we need to decompose the hypothesis <span
class="inlinecode"><span class="id" type="var">H</span></span> that has\
      just been created by <span class="inlinecode"><span class="id"
type="var">forwards</span></span>. This is done by the first part \
      of the preprocessing phase of <span class="inlinecode"><span
class="id" type="var">jauto</span></span>. \*)</span>\
   <span class="id" type="var">jauto\_set\_hyps</span>; <span class="id"
type="tactic">intros</span>.\
   <span
class="comment">(\* It remains to decompose the goal, which is done by the second \
      part of the preprocessing phase of <span class="inlinecode"><span
class="id" type="var">jauto</span></span>. \*)</span>\
   <span class="id" type="var">jauto\_set\_goal</span>; <span class="id"
type="tactic">intros</span>.\
   <span
class="comment">(\* All the subgoals produced can then be solved by <span
class="inlinecode"><span class="id"
type="tactic">eauto</span></span>. \*)</span>\
   <span class="id" type="tactic">eauto</span>. <span class="id"
type="tactic">eauto</span>. <span class="id"
type="tactic">eauto</span>.\
\
   <span class="id" type="var">SCase</span> "ST\_App2".\
   <span class="comment">(\* old:\
       eapply IHHt2 in H5...\
       inversion H5 as <span class="inlinecode"><span class="id"
type="var">ST'</span></span> <span class="inlinecode">[<span class="id"
type="var">Hext</span></span> <span class="inlinecode">[<span class="id"
type="var">Hty</span></span> <span class="inlinecode"><span class="id"
type="var">Hsty</span>]]</span>.\
       exists ST'... \*)</span>\
   <span class="comment">(\* new: this time, we need to call <span
class="inlinecode"><span class="id"
type="var">forwards</span></span> on <span class="inlinecode"><span
class="id" type="var">IHHt2</span></span>,\
      and we call <span class="inlinecode"><span class="id"
type="var">jauto</span></span> right away, by writing <span
class="inlinecode"><span class="id" type="var">forwards</span>×</span>,\
      proving the goal in a single tactic! \*)</span>\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt2</span>.\
\
   <span
class="comment">(\* The same trick works for many of the other subgoals. \*)</span>\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt1</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt2</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt1</span>.\
\
   <span class="id" type="var">Case</span> "T\_Ref".\
   <span class="id" type="var">SCase</span> "ST\_RefValue".\
   <span class="comment">(\* old:\
       exists (snoc ST T~1~). \
       inversion HST; subst.\
       split.\
         apply extends\_snoc.\
       split.\
         replace (TRef T~1~)\
          with (TRef (store\_Tlookup (length st) (snoc ST T~1~))).\
         apply T\_Loc. \
         rewrite \<- H. rewrite length\_snoc. omega.\
         unfold store\_Tlookup. rewrite \<- H. rewrite nth\_eq\_snoc...\
         apply store\_well\_typed\_snoc; assumption. \*)</span>\
   <span
class="comment">(\* new: in this proof case, we need to perform an inversion\
      without removing the hypothesis. The tactic <span
class="inlinecode"><span class="id" type="var">inverts</span></span>
<span class="inlinecode"><span class="id"
type="var">keep</span></span> \
      serves exactly this purpose. \*)</span>\
   <span style="font-family: arial;">∃</span>(<span class="id"
type="var">snoc</span> <span class="id" type="var">ST</span> <span
class="id" type="var">T~1~</span>). <span class="id"
type="var">inverts</span> <span class="id" type="var">keep</span> <span
class="id" type="var">HST</span>. <span class="id"
type="var">splits</span>.\
   <span
class="comment">(\* The proof of the first subgoal needs not be changed \*)</span>\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">extends\_snoc</span>.\
   <span
class="comment">(\* For the second subgoal, we use the tactic <span
class="inlinecode"><span class="id"
type="var">applys\_eq</span></span> to avoid\
      a manual <span class="inlinecode"><span class="id"
type="tactic">replace</span></span> before <span
class="inlinecode"><span class="id"
type="var">T\_loc</span></span> can be applied. \*)</span>\
     <span class="id" type="var">applys\_eq</span> <span class="id"
type="var">T\_Loc</span> 1.\
   <span
class="comment">(\* To justify the inequality, there is no need to call <span
class="inlinecode"><span class="id" type="tactic">rewrite</span></span>
<span class="inlinecode"><span
style="font-family: arial;">←</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span>,\
      because the tactic <span class="inlinecode"><span class="id"
type="tactic">omega</span></span> is able to exploit <span
class="inlinecode"><span class="id"
type="var">H</span></span> on its own. \
      So, only the rewriting of <span class="inlinecode"><span
class="id" type="var">lenght\_snoc</span></span> and the call to the\
      tactic <span class="inlinecode"><span class="id"
type="tactic">omega</span></span> remain. \*)</span>\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">length\_snoc</span>. <span class="id"
type="tactic">omega</span>.\
   <span
class="comment">(\* The next proof case is hard to polish because it relies on the\
      lemma <span class="inlinecode"><span class="id"
type="var">nth\_eq\_snoc</span></span> whose statement is not automation-friendly.\
      We'll come back to this proof case further on. \*)</span>\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">store\_Tlookup</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">H</span>. <span class="id"
type="tactic">rewrite</span>× <span class="id"
type="var">nth\_eq\_snoc</span>.\
   <span class="comment">(\* Last, we replace <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
<span class="inlinecode">..;</span> <span class="inlinecode"><span
class="id" type="tactic">assumption</span></span> with <span
class="inlinecode"><span class="id" type="tactic">apply</span>×</span>
<span class="inlinecode">..</span> \*)</span>\
     <span class="id" type="tactic">apply</span>× <span class="id"
type="var">store\_well\_typed\_snoc</span>.\
\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt</span>.\
\
   <span class="id" type="var">Case</span> "T\_Deref".\
   <span class="id" type="var">SCase</span> "ST\_DerefLoc".\
   <span class="comment">(\* old:\
       exists ST. split; try split...\
       destruct HST as <span class="inlinecode"><span class="id"
type="var">\_</span></span> <span class="inlinecode"><span class="id"
type="var">Hsty</span></span>.\
       replace T~11~ with (store\_Tlookup l ST).\
       apply Hsty...\
       inversion Ht; subst... \*)</span>\
   <span class="comment">(\* new: we start by calling <span
class="inlinecode"><span style="font-family: arial;">∃</span></span>
<span class="inlinecode"><span class="id"
type="var">ST</span></span> and <span class="inlinecode"><span
class="id" type="var">splits</span>×</span>. \*)</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">ST</span>. <span class="id" type="var">splits</span>×.\
   <span class="comment">(\* new: we replace <span
class="inlinecode"><span class="id" type="tactic">destruct</span></span>
<span class="inlinecode"><span class="id" type="var">HST</span></span>
<span class="inlinecode"><span class="id"
type="keyword">as</span></span> <span class="inlinecode">[<span
class="id" type="var">\_</span></span> <span class="inlinecode"><span
class="id" type="var">Hsty</span>]</span> by the following \*)</span>\
   <span class="id" type="var">lets</span> [<span class="id"
type="var">\_</span> <span class="id" type="var">Hsty</span>]: <span
class="id" type="var">HST</span>.\
   <span class="comment">(\* new: then we use the tactic <span
class="inlinecode"><span class="id"
type="var">applys\_eq</span></span> to avoid the need to\
      perform a manual <span class="inlinecode"><span class="id"
type="tactic">replace</span></span> before applying <span
class="inlinecode"><span class="id"
type="var">Hsty</span></span>. \*)</span>\
   <span class="id" type="var">applys\_eq</span>× <span class="id"
type="var">Hsty</span> 1.\
   <span class="comment">(\* new: we then can call <span
class="inlinecode"><span class="id"
type="var">inverts</span></span> in place of <span
class="inlinecode"><span class="id" type="tactic">inversion</span>;<span
class="id" type="tactic">subst</span></span> \*)</span>\
   <span class="id" type="var">inverts</span>× <span class="id"
type="var">Ht</span>.\
\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt</span>.\
\
   <span class="id" type="var">Case</span> "T\_Assign".\
   <span class="id" type="var">SCase</span> "ST\_Assign".\
   <span class="comment">(\* old: \
       exists ST. split; try split...\
       eapply assign\_pres\_store\_typing...\
       inversion Ht1; subst... \*)</span>\
   <span class="comment">(\* new: simply using nicer tactics \*)</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">ST</span>. <span class="id" type="var">splits</span>×. <span
class="id" type="var">applys</span>× <span class="id"
type="var">assign\_pres\_store\_typing</span>. <span class="id"
type="var">inverts</span>× <span class="id" type="var">Ht1</span>.\
\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt1</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt2</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Let's come back to the proof case that was hard to optimize. The
difficulty comes from the statement of <span class="inlinecode"><span
class="id" type="var">nth\_eq\_snoc</span></span>, which takes the form
<span class="inlinecode"><span class="id" type="var">nth</span></span>
<span class="inlinecode">(<span class="id"
type="var">length</span></span> <span class="inlinecode"><span
class="id" type="var">l</span>)</span> <span class="inlinecode">(<span
class="id" type="var">snoc</span></span> <span class="inlinecode"><span
class="id" type="var">l</span></span> <span class="inlinecode"><span
class="id" type="var">x</span>)</span> <span class="inlinecode"><span
class="id" type="var">d</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">x</span></span>.
This lemma is hard to exploit because its first argument, <span
class="inlinecode"><span class="id" type="var">length</span></span>
<span class="inlinecode"><span class="id" type="var">l</span></span>,
mentions a list <span class="inlinecode"><span class="id"
type="var">l</span></span> that has to be exactly the same as the <span
class="inlinecode"><span class="id" type="var">l</span></span> occuring
in <span class="inlinecode"><span class="id"
type="var">snoc</span></span> <span class="inlinecode"><span class="id"
type="var">l</span></span> <span class="inlinecode"><span class="id"
type="var">x</span></span>. In practice, the first argument is often a
natural number <span class="inlinecode"><span class="id"
type="var">n</span></span> that is provably equal to <span
class="inlinecode"><span class="id" type="var">length</span></span>
<span class="inlinecode"><span class="id" type="var">l</span></span> yet
that is not syntactically equal to <span class="inlinecode"><span
class="id" type="var">length</span></span> <span
class="inlinecode"><span class="id" type="var">l</span></span>. There is
a simple fix for making <span class="inlinecode"><span class="id"
type="var">nth\_eq\_snoc</span></span> easy to apply: introduce the
intermediate variable <span class="inlinecode"><span class="id"
type="var">n</span></span> explicitly, so that the goal becomes <span
class="inlinecode"><span class="id" type="var">nth</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">(<span class="id" type="var">snoc</span></span> <span
class="inlinecode"><span class="id" type="var">l</span></span> <span
class="inlinecode"><span class="id" type="var">x</span>)</span> <span
class="inlinecode"><span class="id" type="var">d</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">x</span></span>, with a premise asserting <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">length</span></span> <span class="inlinecode"><span
class="id" type="var">l</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">nth\_eq\_snoc'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">A</span> : <span class="id" type="keyword">Type</span>)
(<span class="id" type="var">l</span> : <span class="id"
type="var">list</span> <span class="id" type="var">A</span>) (<span
class="id" type="var">x</span> <span class="id" type="var">d</span> :
<span class="id" type="var">A</span>) (<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>),\
   <span class="id" type="var">n</span> = <span class="id"
type="var">length</span> <span class="id" type="var">l</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nth</span> <span class="id" type="var">n</span> (<span
class="id" type="var">snoc</span> <span class="id" type="var">l</span>
<span class="id" type="var">x</span>) <span class="id"
type="var">d</span> = <span class="id" type="var">x</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span>. <span class="id"
type="tactic">subst</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">nth\_eq\_snoc</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The proof case for <span class="inlinecode"><span class="id"
type="var">ref</span></span> from the preservation theorem then becomes
much easier to prove, because <span class="inlinecode"><span class="id"
type="tactic">rewrite</span></span> <span class="inlinecode"><span
class="id" type="var">nth\_eq\_snoc'</span></span> now succeeds.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">preservation\_ref</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st</span>:<span class="id" type="var">store</span>) (<span
class="id" type="var">ST</span> : <span class="id"
type="var">store\_ty</span>) <span class="id" type="var">T~1~</span>,\
   <span class="id" type="var">length</span> <span class="id"
type="var">ST</span> = <span class="id" type="var">length</span> <span
class="id" type="var">st</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">TRef</span> <span class="id"
type="var">T~1~</span> = <span class="id" type="var">TRef</span> (<span
class="id" type="var">store\_Tlookup</span> (<span class="id"
type="var">length</span> <span class="id" type="var">st</span>) (<span
class="id" type="var">snoc</span> <span class="id" type="var">ST</span>
<span class="id" type="var">T~1~</span>)).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="var">dup</span>.\
\
   <span class="comment">(\* A first proof, with an explicit <span
class="inlinecode"><span class="id"
type="tactic">unfold</span></span> \*)</span>\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">store\_Tlookup</span>. <span class="id"
type="tactic">rewrite</span>× <span class="id"
type="var">nth\_eq\_snoc'</span>.\
\
   <span class="comment">(\* A second proof, with a call to <span
class="inlinecode"><span class="id"
type="var">fequal</span></span> \*)</span>\
   <span class="id" type="var">fequal</span>. <span class="id"
type="tactic">symmetry</span>. <span class="id"
type="tactic">apply</span>× <span class="id"
type="var">nth\_eq\_snoc'</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The optimized proof of preservation is summarized next.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">preservation'</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span> <span class="id" type="var">T</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span>,\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">ST</span> <span
class="id" type="var">t</span> <span class="id" type="var">T</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">t</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t'</span> / <span class="id" type="var">st'</span>
<span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>,\
     (<span class="id" type="var">extends</span> <span class="id"
type="var">ST'</span> <span class="id" type="var">ST</span> <span
style="font-family: arial;">∧</span>\
      <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">ST'</span> <span
class="id" type="var">t'</span> <span class="id" type="var">T</span>
<span style="font-family: arial;">∧</span>\
      <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST'</span> <span class="id"
type="var">st'</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>. <span class="id"
type="var">introv</span> <span class="id" type="var">Ht</span>. <span
class="id" type="var">gen</span> <span class="id" type="var">t'</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">Ht</span>; <span class="id" type="var">introv</span> <span
class="id" type="var">HST</span> <span class="id"
type="var">Hstep</span>; <span class="id" type="tactic">subst</span>
<span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">inverts</span> <span class="id"
type="var">Hstep</span>; <span class="id" type="tactic">eauto</span>.\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">ST</span>. <span class="id" type="var">inverts</span> <span
class="id" type="var">Ht1</span>. <span class="id"
type="var">splits</span>×. <span class="id" type="var">applys</span>×
<span class="id" type="var">substitution\_preserves\_typing</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt1</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt2</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt1</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt2</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt1</span>.\
   <span style="font-family: arial;">∃</span>(<span class="id"
type="var">snoc</span> <span class="id" type="var">ST</span> <span
class="id" type="var">T~1~</span>). <span class="id"
type="var">inverts</span> <span class="id" type="var">keep</span> <span
class="id" type="var">HST</span>. <span class="id"
type="var">splits</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">extends\_snoc</span>.\
     <span class="id" type="var">applys\_eq</span> <span class="id"
type="var">T\_Loc</span> 1.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">length\_snoc</span>. <span class="id"
type="tactic">omega</span>.\
       <span class="id" type="tactic">unfold</span> <span class="id"
type="var">store\_Tlookup</span>. <span class="id"
type="tactic">rewrite</span>× <span class="id"
type="var">nth\_eq\_snoc'</span>.\
     <span class="id" type="tactic">apply</span>× <span class="id"
type="var">store\_well\_typed\_snoc</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt</span>.\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">ST</span>. <span class="id" type="var">splits</span>×. <span
class="id" type="var">lets</span> [<span class="id" type="var">\_</span>
<span class="id" type="var">Hsty</span>]: <span class="id"
type="var">HST</span>.\
    <span class="id" type="var">applys\_eq</span>× <span class="id"
type="var">Hsty</span> 1. <span class="id" type="var">inverts</span>×
<span class="id" type="var">Ht</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt</span>.\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">ST</span>. <span class="id" type="var">splits</span>×. <span
class="id" type="var">applys</span>× <span class="id"
type="var">assign\_pres\_store\_typing</span>. <span class="id"
type="var">inverts</span>× <span class="id" type="var">Ht1</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt1</span>.\
   <span class="id" type="var">forwards</span>\*: <span class="id"
type="var">IHHt2</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Progress for STLCRef {.section}
--------------------

<div class="paragraph">

</div>

The proof of progress for <span class="inlinecode"><span class="id"
type="var">STLCRef</span></span> can be found in chapter <span
class="inlinecode"><span class="id" type="var">References</span></span>.
It contains 53 lines and the optimized proof script is, here again, half
the length.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="tactic">progress</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span class="id" type="var">st</span>,\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">ST</span> <span
class="id" type="var">t</span> <span class="id" type="var">T</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">→</span>\
   (<span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">∨</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">st'</span>, <span class="id" type="var">t</span> /
<span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span> / <span class="id" type="var">st'</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">introv</span> <span class="id"
type="var">Ht</span> <span class="id" type="var">HST</span>. <span
class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">Ht</span>; <span class="id" type="tactic">subst</span> <span
style="font-family: serif; font-size:85%;">Γ</span>; <span class="id"
type="var">tryfalse</span>; <span class="id" type="tactic">try</span>
<span class="id" type="var">solve</span> [<span class="id"
type="var">left</span>×].\
   <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span>× <span class="id" type="var">IHHt1</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">K</span>|].\
     <span class="id" type="var">inverts</span> <span class="id"
type="var">K</span>; <span class="id" type="var">inverts</span> <span
class="id" type="var">Ht1</span>.\
      <span class="id" type="tactic">destruct</span>× <span class="id"
type="var">IHHt2</span>.\
   <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span>× <span class="id" type="var">IHHt</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">K</span>|].\
     <span class="id" type="var">inverts</span> <span class="id"
type="var">K</span>; <span class="id" type="tactic">try</span> <span
class="id" type="var">solve</span> [<span class="id"
type="var">inverts</span> <span class="id" type="var">Ht</span>]. <span
class="id" type="tactic">eauto</span>.\
   <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span>× <span class="id" type="var">IHHt</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">K</span>|].\
     <span class="id" type="var">inverts</span> <span class="id"
type="var">K</span>; <span class="id" type="tactic">try</span> <span
class="id" type="var">solve</span> [<span class="id"
type="var">inverts</span> <span class="id" type="var">Ht</span>]. <span
class="id" type="tactic">eauto</span>.\
   <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span>× <span class="id" type="var">IHHt1</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">K</span>|].\
     <span class="id" type="var">inverts</span> <span class="id"
type="var">K</span>; <span class="id" type="tactic">try</span> <span
class="id" type="var">solve</span> [<span class="id"
type="var">inverts</span> <span class="id" type="var">Ht1</span>].\
      <span class="id" type="tactic">destruct</span>× <span class="id"
type="var">IHHt2</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">M</span>|].\
       <span class="id" type="var">inverts</span> <span class="id"
type="var">M</span>; <span class="id" type="tactic">try</span> <span
class="id" type="var">solve</span> [<span class="id"
type="var">inverts</span> <span class="id" type="var">Ht2</span>]. <span
class="id" type="tactic">eauto</span>.\
   <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span>× <span class="id" type="var">IHHt1</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">K</span>|].\
     <span class="id" type="var">inverts</span> <span class="id"
type="var">K</span>; <span class="id" type="tactic">try</span> <span
class="id" type="var">solve</span> [<span class="id"
type="var">inverts</span> <span class="id" type="var">Ht1</span>]. <span
class="id" type="tactic">destruct</span>× <span class="id"
type="var">n</span>.\
   <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span>× <span class="id" type="var">IHHt</span>.\
   <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span>× <span class="id" type="var">IHHt</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">K</span>|].\
     <span class="id" type="var">inverts</span> <span class="id"
type="var">K</span>; <span class="id" type="var">inverts</span> <span
class="id" type="var">Ht</span> <span class="id"
type="keyword">as</span> <span class="id" type="var">M</span>.\
       <span class="id" type="var">inverts</span> <span class="id"
type="var">HST</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">N</span>. <span class="id"
type="tactic">rewrite</span>× <span class="id" type="var">N</span> <span
class="id" type="keyword">in</span> <span class="id"
type="var">M</span>.\
   <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span>× <span class="id" type="var">IHHt1</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">K</span>|].\
     <span class="id" type="tactic">destruct</span>× <span class="id"
type="var">IHHt2</span>.\
      <span class="id" type="var">inverts</span> <span class="id"
type="var">K</span>; <span class="id" type="var">inverts</span> <span
class="id" type="var">Ht1</span> <span class="id"
type="keyword">as</span> <span class="id" type="var">M</span>.\
      <span class="id" type="var">inverts</span> <span class="id"
type="var">HST</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">N</span>. <span class="id"
type="tactic">rewrite</span>× <span class="id" type="var">N</span> <span
class="id" type="keyword">in</span> <span class="id"
type="var">M</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">PreservationProgressReferences</span>.\
\

</div>

<div class="doc">

Subtyping {.section}
---------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">SubtypingInversion</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Sub</span>.\
\

</div>

<div class="doc">

Consider the inversion lemma for typing judgment of abstractions in a
type system with subtyping.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">abs\_arrow</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">S~1~</span> <span class="id"
type="var">s~2~</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> (<span class="id" type="var">tabs</span> <span
class="id" type="var">x</span> <span class="id" type="var">S~1~</span>
<span class="id" type="var">s~2~</span>) (<span class="id"
type="var">TArrow</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>) <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">subtype</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">S~1~</span>\
   <span style="font-family: arial;">∧</span> <span class="id"
type="var">has\_type</span> (<span class="id" type="var">extend</span>
<span class="id" type="var">empty</span> <span class="id"
type="var">x</span> <span class="id" type="var">S~1~</span>) <span
class="id" type="var">s~2~</span> <span class="id"
type="var">T~2~</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">S~1~</span> <span
class="id" type="var">s~2~</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> <span
class="id" type="var">Hty</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">typing\_inversion\_abs</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hty</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">Hty</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">S~2~</span> [<span class="id"
type="var">Hsub</span> <span class="id" type="var">Hty</span>]].\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">sub\_inversion\_arrow</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hsub</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">Hsub</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">U1</span> [<span class="id" type="var">U2</span>
[<span class="id" type="var">Heq</span> [<span class="id"
type="var">Hsub1</span> <span class="id" type="var">Hsub2</span>]]]].\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heq</span>; <span class="id" type="tactic">subst</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Exercise: optimize the proof script, using <span
class="inlinecode"><span class="id" type="var">introv</span></span>,
<span class="inlinecode"><span class="id" type="var">lets</span></span>
and <span class="inlinecode"><span class="id"
type="var">inverts</span>×</span>. In particular, you will find it
useful to replace the pattern <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">K</span></span> <span class="inlinecode"><span
class="id" type="keyword">in</span></span> <span
class="inlinecode"><span class="id" type="var">H</span>.</span> <span
class="inlinecode"><span class="id" type="tactic">destruct</span></span>
<span class="inlinecode"><span class="id" type="var">H</span></span>
<span class="inlinecode"><span class="id"
type="keyword">as</span></span> <span class="inlinecode"><span
class="id" type="var">I</span></span> with <span
class="inlinecode"><span class="id" type="var">lets</span></span> <span
class="inlinecode"><span class="id" type="var">I</span>:</span> <span
class="inlinecode"><span class="id" type="var">K</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span>. The
solution is 4 lines.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">abs\_arrow'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">S~1~</span> <span class="id"
type="var">s~2~</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> (<span class="id" type="var">tabs</span> <span
class="id" type="var">x</span> <span class="id" type="var">S~1~</span>
<span class="id" type="var">s~2~</span>) (<span class="id"
type="var">TArrow</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>) <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">subtype</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">S~1~</span>\
   <span style="font-family: arial;">∧</span> <span class="id"
type="var">has\_type</span> (<span class="id" type="var">extend</span>
<span class="id" type="var">empty</span> <span class="id"
type="var">x</span> <span class="id" type="var">S~1~</span>) <span
class="id" type="var">s~2~</span> <span class="id"
type="var">T~2~</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The lemma <span class="inlinecode"><span class="id"
type="var">substitution\_preserves\_typing</span></span> has already
been used to illustrate the working of <span class="inlinecode"><span
class="id" type="var">lets</span></span> and <span
class="inlinecode"><span class="id" type="var">applys</span></span> in
chapter <span class="inlinecode"><span class="id"
type="var">UseTactics</span></span>. Optimize further this proof using
automation (with the star symbol), and using the tactic <span
class="inlinecode"><span class="id" type="var">cases\_if'</span></span>.
The solution is 33 lines, including the <span class="inlinecode"><span
class="id" type="var">Case</span></span> instructions (21 lines without
them).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">substitution\_preserves\_typing</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span> <span
class="id" type="var">v</span> <span class="id" type="var">t</span>
<span class="id" type="var">S</span>,\
   <span class="id" type="var">has\_type</span> (<span class="id"
type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span>) <span
class="id" type="var">t</span> <span class="id" type="var">S</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">v</span> <span
class="id" type="var">U</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> ([<span class="id"
type="var">x</span>:=<span class="id" type="var">v</span>]<span
class="id" type="var">t</span>) <span class="id" type="var">S</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">SubtypingInversion</span>.\
\

</div>

<div class="doc">

Advanced Topics in Proof Search {.section}
===============================

</div>

<div class="code code-space">

\

</div>

<div class="doc">

Stating Lemmas in the Right Way {.section}
-------------------------------

<div class="paragraph">

</div>

Due to its depth-first strategy, <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> can get exponentially
slower as the depth search increases, even when a short proof exists. In
general, to make proof search run reasonably fast, one should avoid
using a depth search greater than 5 or 6. Moreover, one should try to
minimize the number of applicable lemmas, and usually put first the
hypotheses whose proof usefully instantiates the existential variables.
<div class="paragraph">

</div>

In fact, the ability for <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> to solve certain goals actually
depends on the order in which the hypotheses are stated. This point is
illustrated through the following example, in which <span
class="inlinecode"><span class="id" type="var">P</span></span> is a
predicate on natural numbers. This predicate is such that <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> holds for
any <span class="inlinecode"><span class="id" type="var">n</span></span>
as soon as <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode"><span class="id"
type="var">m</span></span> holds for at least one <span
class="inlinecode"><span class="id" type="var">m</span></span> different
from zero. The goal is to prove that <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode">2</span>
implies <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">1</span>. When the
hypothesis about <span class="inlinecode"><span class="id"
type="var">P</span></span> is stated in the form <span
class="inlinecode"><span style="font-family: arial;">∀</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span>
<span class="inlinecode"><span class="id" type="var">m</span>,</span>
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span class="id" type="var">m</span></span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">m</span></span> <span
class="inlinecode">≠</span> <span class="inlinecode">0</span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span>,
then <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> works. However, with <span
class="inlinecode"><span style="font-family: arial;">∀</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span>
<span class="inlinecode"><span class="id" type="var">m</span>,</span>
<span class="inlinecode"><span class="id" type="var">m</span></span>
<span class="inlinecode">≠</span> <span class="inlinecode">0</span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">m</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span>,
the tactic <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> fails.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">order\_matters\_1</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> <span class="id" type="var">m</span>, <span
class="id" type="var">P</span> <span class="id" type="var">m</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">m</span> ≠ 0 <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> <span class="id" type="var">n</span>)
<span style="font-family: arial;">→</span> <span class="id"
type="var">P</span> 2 <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> 1.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eauto</span>. <span
class="comment">(\* Success \*)</span>\
   <span class="comment">(\* The proof: <span class="inlinecode"><span
class="id" type="tactic">intros</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span> <span
class="inlinecode"><span class="id" type="var">K</span>.</span> <span
class="inlinecode"><span class="id" type="tactic">eapply</span></span>
<span class="inlinecode"><span class="id" type="var">H</span>.</span>
<span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">K</span>.</span> <span class="inlinecode"><span
class="id" type="tactic">auto</span>.</span> \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">order\_matters\_2</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> <span class="id" type="var">m</span>, <span
class="id" type="var">m</span> ≠ 0 <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">m</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">n</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> 5 <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> 1.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eauto</span>. <span
class="comment">(\* Failure \*)</span>\
\
   <span
class="comment">(\* To understand why, let us replay the previous proof \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">H</span> <span
class="id" type="var">K</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H</span>.\
   <span class="comment">(\* The application of <span
class="inlinecode"><span class="id"
type="tactic">eapply</span></span> has left two subgoals,\
      <span class="inlinecode">?<span class="id"
type="var">X</span></span> <span class="inlinecode">≠</span> <span
class="inlinecode">0</span> and <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode">?<span
class="id" type="var">X</span></span>, where <span
class="inlinecode">?<span class="id"
type="var">X</span></span> is an existential variable. \*)</span>\
   <span class="comment">(\* Solving the first subgoal is easy for <span
class="inlinecode"><span class="id"
type="tactic">eauto</span></span>: it suffices\
      to instantiate <span class="inlinecode">?<span class="id"
type="var">X</span></span> as the value <span
class="inlinecode">1</span>, which is the simplest\
      value that satisfies <span class="inlinecode">?<span class="id"
type="var">X</span></span> <span class="inlinecode">≠</span> <span
class="inlinecode">0</span>. \*)</span>\
   <span class="id" type="tactic">eauto</span>.\
   <span class="comment">(\* But then the second goal becomes <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">1</span>, which is where we\
      started from. So, <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> gets stuck at this point. \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

It is very important to understand that the hypothesis <span
class="inlinecode"><span style="font-family: arial;">∀</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span>
<span class="inlinecode"><span class="id" type="var">m</span>,</span>
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span class="id" type="var">m</span></span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">m</span></span> <span
class="inlinecode">≠</span> <span class="inlinecode">0</span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span> is
eauto-friendly, whereas <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode"><span class="id" type="var">m</span>,</span> <span
class="inlinecode"><span class="id" type="var">m</span></span> <span
class="inlinecode">≠</span> <span class="inlinecode">0</span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span class="id" type="var">m</span></span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> really
isn't. Guessing a value of <span class="inlinecode"><span class="id"
type="var">m</span></span> for which <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode"><span
class="id" type="var">m</span></span> holds and then checking that <span
class="inlinecode"><span class="id" type="var">m</span></span> <span
class="inlinecode">≠</span> <span class="inlinecode">0</span> holds
works well because there are few values of <span
class="inlinecode"><span class="id" type="var">m</span></span> for which
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span class="id" type="var">m</span></span>
holds. So, it is likely that <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> comes up with the right one. On the
other hand, guessing a value of <span class="inlinecode"><span
class="id" type="var">m</span></span> for which <span
class="inlinecode"><span class="id" type="var">m</span></span> <span
class="inlinecode">≠</span> <span class="inlinecode">0</span> and then
checking that <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode"><span class="id"
type="var">m</span></span> holds does not work well, because there are
many values of <span class="inlinecode"><span class="id"
type="var">m</span></span> that satisfy <span class="inlinecode"><span
class="id" type="var">m</span></span> <span class="inlinecode">≠</span>
<span class="inlinecode">0</span> but not <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode"><span
class="id" type="var">m</span></span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Unfolding of Definitions During Proof-Search {.section}
--------------------------------------------

<div class="paragraph">

</div>

The use of intermediate definitions is generally encouraged in a formal
development as it usually leads to more concise and more readable
statements. Yet, definitions can make it a little harder to automate
proofs. The problem is that it is not obvious for a proof search
mechanism to know when definitions need to be unfolded. Note that a
naive strategy that consists in unfolding all definitions before calling
proof search does not scale up to large proofs, so we avoid it. This
section introduces a few techniques for avoiding to manually unfold
definitions before calling proof search.
<div class="paragraph">

</div>

To illustrate the treatment of definitions, let <span
class="inlinecode"><span class="id" type="var">P</span></span> be an
abstract predicate on natural numbers, and let <span
class="inlinecode"><span class="id" type="var">myFact</span></span> be a
definition denoting the proposition <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span> holds for any <span
class="inlinecode"><span class="id" type="var">x</span></span> less than
or equal to 3.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Axiom</span> <span class="id"
type="var">P</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">myFact</span> := <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span class="id" type="var">x</span> ≤ 3 <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> <span class="id" type="var">x</span>.\
\

</div>

<div class="doc">

Proving that <span class="inlinecode"><span class="id"
type="var">myFact</span></span> under the assumption that <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> holds for
any <span class="inlinecode"><span class="id" type="var">x</span></span>
should be trivial. Yet, <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> fails to prove it unless we unfold the
definition of <span class="inlinecode"><span class="id"
type="var">myFact</span></span> explicitly.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_hint\_unfold\_goal\_1</span> :\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span class="id" type="var">P</span> <span
class="id" type="var">x</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">myFact</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">auto</span>. <span
class="comment">(\* Proof search doesn't know what to do, \*)</span>\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">myFact</span>. <span class="id" type="tactic">auto</span>.
<span class="comment">(\* unless we unfold the definition. \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

To automate the unfolding of definitions that appear as proof
obligation, one can use the command <span class="inlinecode"><span
class="id" type="keyword">Hint</span></span> <span
class="inlinecode"><span class="id" type="keyword">Unfold</span></span>
<span class="inlinecode"><span class="id"
type="var">myFact</span></span> to tell Coq that it should always try to
unfold <span class="inlinecode"><span class="id"
type="var">myFact</span></span> when <span class="inlinecode"><span
class="id" type="var">myFact</span></span> appears in the goal.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Unfold</span> <span class="id" type="var">myFact</span>.\
\

</div>

<div class="doc">

This time, automation is able to see through the definition of <span
class="inlinecode"><span class="id" type="var">myFact</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_hint\_unfold\_goal\_2</span> :\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span class="id" type="var">P</span> <span
class="id" type="var">x</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">myFact</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

However, the <span class="inlinecode"><span class="id"
type="keyword">Hint</span></span> <span class="inlinecode"><span
class="id" type="keyword">Unfold</span></span> mechanism only works for
unfolding definitions that appear in the goal. In general, proof search
does not unfold definitions from the context. For example, assume we
want to prove that <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">3</span> holds under
the assumption that <span class="inlinecode"><span class="id"
type="var">True</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">myFact</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_hint\_unfold\_context\_1</span> :\
   (<span class="id" type="var">True</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">myFact</span>) <span style="font-family: arial;">→</span>
<span class="id" type="var">P</span> 3.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">auto</span>. <span
class="comment">(\* fails \*)</span>\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">myFact</span> <span class="id" type="keyword">in</span> ×.
<span class="id" type="tactic">auto</span>. <span
class="comment">(\* succeeds \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

There is actually one exception to the previous rule: a constant
occuring in an hypothesis is automatically unfolded if the hypothesis
can be directly applied to the current goal. For example, <span
class="inlinecode"><span class="id" type="tactic">auto</span></span> can
prove <span class="inlinecode"><span class="id"
type="var">myFact</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode">3</span>, as illustrated below.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_hint\_unfold\_context\_2</span> :\
   <span class="id" type="var">myFact</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span> 3.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Automation for Proving Absurd Goals {.section}
-----------------------------------

<div class="paragraph">

</div>

In this section, we'll see that lemmas concluding on a negation are
generally not useful as hints, and that lemmas whose conclusion is <span
class="inlinecode"><span class="id" type="var">False</span></span> can
be useful hints but having too many of them makes proof search
inefficient. We'll also see a practical work-around to the efficiency
issue.
<div class="paragraph">

</div>

Consider the following lemma, which asserts that a number less than or
equal to 3 is not greater than 3.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Parameter</span> <span class="id"
type="var">le\_not\_gt</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>,\
   (<span class="id" type="var">x</span> ≤ 3) <span
style="font-family: arial;">→</span> ¬ (<span class="id"
type="var">x</span> \> 3).\
\

</div>

<div class="doc">

Equivalently, one could state that a number greater than three is not
less than or equal to 3.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Parameter</span> <span class="id"
type="var">gt\_not\_le</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>,\
   (<span class="id" type="var">x</span> \> 3) <span
style="font-family: arial;">→</span> ¬ (<span class="id"
type="var">x</span> ≤ 3).\
\

</div>

<div class="doc">

In fact, both statements are equivalent to a third one stating that
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode">≤</span> <span class="inlinecode">3</span> and
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode">\></span> <span class="inlinecode">3</span> are
contradictory, in the sense that they imply <span
class="inlinecode"><span class="id" type="var">False</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Parameter</span> <span class="id"
type="var">le\_gt\_false</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>,\
   (<span class="id" type="var">x</span> ≤ 3) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">x</span> \> 3) <span style="font-family: arial;">→</span>
<span class="id" type="var">False</span>.\
\

</div>

<div class="doc">

The following investigation aim at figuring out which of the three
statments is the most convenient with respect to proof automation. The
following material is enclosed inside a <span class="inlinecode"><span
class="id" type="keyword">Section</span></span>, so as to restrict the
scope of the hints that we are adding. In other words, after the end of
the section, the hints added within the section will no longer be
active.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Section</span> <span class="id"
type="var">DemoAbsurd1</span>.\
\

</div>

<div class="doc">

Let's try to add the first lemma, <span class="inlinecode"><span
class="id" type="var">le\_not\_gt</span></span>, as hint, and see
whether we can prove that the proposition <span class="inlinecode"><span
style="font-family: arial;">∃</span></span> <span
class="inlinecode"><span class="id" type="var">x</span>,</span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode">≤</span> <span class="inlinecode">3</span> <span
class="inlinecode"><span style="font-family: arial;">∧</span></span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode">\></span> <span class="inlinecode">3</span> is
absurd.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Resolve</span> <span class="id"
type="var">le\_not\_gt</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_auto\_absurd\_1</span> :\
   (<span style="font-family: arial;">∃</span><span class="id"
type="var">x</span>, <span class="id" type="var">x</span> ≤ 3 <span
style="font-family: arial;">∧</span> <span class="id"
type="var">x</span> \> 3) <span style="font-family: arial;">→</span>
<span class="id" type="var">False</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="var">jauto\_set</span>. <span
class="comment">(\* decomposes the assumption \*)</span>\
   <span class="comment">(\* debug \*)</span> <span class="id"
type="tactic">eauto</span>. <span
class="comment">(\* does not see that <span class="inlinecode"><span
class="id" type="var">le\_not\_gt</span></span> could apply \*)</span>\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">le\_not\_gt</span>. <span class="id"
type="tactic">eauto</span>. <span class="id"
type="tactic">eauto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The lemma <span class="inlinecode"><span class="id"
type="var">gt\_not\_le</span></span> is symmetric to <span
class="inlinecode"><span class="id"
type="var">le\_not\_gt</span></span>, so it will not be any better. The
third lemma, <span class="inlinecode"><span class="id"
type="var">le\_gt\_false</span></span>, is a more useful hint, because
it concludes on <span class="inlinecode"><span class="id"
type="var">False</span></span>, so proof search will try to apply it
when the current goal is <span class="inlinecode"><span class="id"
type="var">False</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Resolve</span> <span class="id"
type="var">le\_gt\_false</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_auto\_absurd\_2</span> :\
   (<span style="font-family: arial;">∃</span><span class="id"
type="var">x</span>, <span class="id" type="var">x</span> ≤ 3 <span
style="font-family: arial;">∧</span> <span class="id"
type="var">x</span> \> 3) <span style="font-family: arial;">→</span>
<span class="id" type="var">False</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">dup</span>.\
\
   <span class="comment">(\* detailed version: \*)</span>\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="var">jauto\_set</span>. <span class="comment">(\* debug \*)</span>
<span class="id" type="tactic">eauto</span>.\
\
   <span class="comment">(\* short version: \*)</span>\
   <span class="id" type="var">jauto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

In summary, a lemma of the form <span class="inlinecode"><span
class="id" type="var">H1</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">H2</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">False</span></span>
is a much more effective hint than <span class="inlinecode"><span
class="id" type="var">H1</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode">¬</span> <span class="inlinecode"><span class="id"
type="var">H2</span></span>, even though the two statments are
equivalent up to the definition of the negation symbol <span
class="inlinecode">¬</span>.
<div class="paragraph">

</div>

That said, one should be careful with adding lemmas whose conclusion is
<span class="inlinecode"><span class="id" type="var">False</span></span>
as hint. The reason is that whenever reaching the goal <span
class="inlinecode"><span class="id" type="var">False</span></span>, the
proof search mechanism will potentially try to apply all the hints whose
conclusion is <span class="inlinecode"><span class="id"
type="var">False</span></span> before applying the appropriate one.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">DemoAbsurd1</span>.\
\

</div>

<div class="doc">

Adding lemmas whose conclusion is <span class="inlinecode"><span
class="id" type="var">False</span></span> as hint can be, locally, a
very effective solution. However, this approach does not scale up for
global hints. For most practical applications, it is reasonable to give
the name of the lemmas to be exploited for deriving a contradiction. The
tactic <span class="inlinecode"><span class="id"
type="var">false</span></span> <span class="inlinecode"><span class="id"
type="var">H</span></span>, provided by <span class="inlinecode"><span
class="id" type="var">LibTactics</span></span> serves that purpose:
<span class="inlinecode"><span class="id" type="var">false</span></span>
<span class="inlinecode"><span class="id" type="var">H</span></span>
replaces the goal with <span class="inlinecode"><span class="id"
type="var">False</span></span> and calls <span class="inlinecode"><span
class="id" type="tactic">eapply</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span>. Its
behavior is described next. Observe that any of the three statements
<span class="inlinecode"><span class="id"
type="var">le\_not\_gt</span></span>, <span class="inlinecode"><span
class="id" type="var">gt\_not\_le</span></span> or <span
class="inlinecode"><span class="id"
type="var">le\_gt\_false</span></span> can be used.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_false</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>,\
   (<span class="id" type="var">x</span> ≤ 3) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">x</span> \> 3) <span style="font-family: arial;">→</span> 4 =
5.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="var">dup</span> 4.\
\
   <span class="comment">(\* A failed proof: \*)</span>\
   <span class="id" type="var">false</span>. <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">le\_gt\_false</span>.\
     <span class="id" type="tactic">auto</span>. <span
class="comment">(\* here, <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> does not prove <span
class="inlinecode">?<span class="id" type="var">x</span></span> <span
class="inlinecode">≤</span> <span
class="inlinecode">3</span> by using <span class="inlinecode"><span
class="id" type="var">H</span></span> but \
              by using the lemma <span class="inlinecode"><span
class="id" type="var">le\_refl</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">x</span>,</span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode">≤</span> <span class="inlinecode"><span class="id"
type="var">x</span></span>. \*)</span>\
     <span class="comment">(\* The second subgoal becomes <span
class="inlinecode">3</span> <span class="inlinecode">\></span> <span
class="inlinecode">3</span>, which is not provable. \*)</span>\
     <span class="id" type="var">skip</span>.\
\
   <span class="comment">(\* A correct proof: \*)</span>\
   <span class="id" type="var">false</span>. <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">le\_gt\_false</span>.\
     <span class="id" type="tactic">eauto</span>. <span
class="comment">(\* here, <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> uses <span class="inlinecode"><span
class="id" type="var">H</span></span>, as expected, to prove <span
class="inlinecode">?<span class="id" type="var">x</span></span> <span
class="inlinecode">≤</span> <span
class="inlinecode">3</span> \*)</span>\
     <span class="id" type="tactic">eauto</span>. <span
class="comment">(\* so the second subgoal becomes <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode">\></span> <span
class="inlinecode">3</span> \*)</span>\
\
   <span class="comment">(\* The same proof using <span
class="inlinecode"><span class="id"
type="var">false</span></span>: \*)</span>\
   <span class="id" type="var">false</span> <span class="id"
type="var">le\_gt\_false</span>. <span class="id"
type="tactic">eauto</span>. <span class="id"
type="tactic">eauto</span>.\
\
   <span class="comment">(\* The lemmas <span class="inlinecode"><span
class="id" type="var">le\_not\_gt</span></span> and <span
class="inlinecode"><span class="id"
type="var">gt\_not\_le</span></span> work as well \*)</span>\
   <span class="id" type="var">false</span> <span class="id"
type="var">le\_not\_gt</span>. <span class="id"
type="tactic">eauto</span>. <span class="id"
type="tactic">eauto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

In the above example, <span class="inlinecode"><span class="id"
type="var">false</span></span> <span class="inlinecode"><span class="id"
type="var">le\_gt\_false</span>;</span> <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> proves the goal, but <span
class="inlinecode"><span class="id" type="var">false</span></span> <span
class="inlinecode"><span class="id"
type="var">le\_gt\_false</span>;</span> <span class="inlinecode"><span
class="id" type="tactic">auto</span></span> does not, because <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
does not correctly instantiate the existential variable. Note that <span
class="inlinecode"><span class="id" type="var">false</span>×</span>
<span class="inlinecode"><span class="id"
type="var">le\_gt\_false</span></span> would not work either, because
the star symbol tries to call <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> first. So, there are two possibilities
for completing the proof: either call <span class="inlinecode"><span
class="id" type="var">false</span></span> <span class="inlinecode"><span
class="id" type="var">le\_gt\_false</span>;</span> <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span>,
or call <span class="inlinecode"><span class="id"
type="var">false</span>×</span> <span class="inlinecode">(<span
class="id" type="var">le\_gt\_false</span></span> <span
class="inlinecode">3)</span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Automation for Transitivity Lemmas {.section}
----------------------------------

<div class="paragraph">

</div>

Some lemmas should never be added as hints, because they would very
badly slow down proof search. The typical example is that of
transitivity results. This section describes the problem and presents a
general workaround.
<div class="paragraph">

</div>

Consider a subtyping relation, written <span class="inlinecode"><span
class="id" type="var">subtype</span></span> <span
class="inlinecode"><span class="id" type="var">S</span></span> <span
class="inlinecode"><span class="id" type="var">T</span></span>, that
relates two object <span class="inlinecode"><span class="id"
type="var">S</span></span> and <span class="inlinecode"><span class="id"
type="var">T</span></span> of type <span class="inlinecode"><span
class="id" type="var">typ</span></span>. Assume that this relation has
been proved reflexive and transitive. The corresponding lemmas are named
<span class="inlinecode"><span class="id"
type="var">subtype\_refl</span></span> and <span
class="inlinecode"><span class="id"
type="var">subtype\_trans</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Parameter</span> <span class="id"
type="var">typ</span> : <span class="id" type="keyword">Type</span>.\
\
 <span class="id" type="keyword">Parameter</span> <span class="id"
type="var">subtype</span> : <span class="id" type="var">typ</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">typ</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>.\
\
 <span class="id" type="keyword">Parameter</span> <span class="id"
type="var">subtype\_refl</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T</span>,\
   <span class="id" type="var">subtype</span> <span class="id"
type="var">T</span> <span class="id" type="var">T</span>.\
\
 <span class="id" type="keyword">Parameter</span> <span class="id"
type="var">subtype\_trans</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">S</span>
<span class="id" type="var">T</span> <span class="id"
type="var">U</span>,\
   <span class="id" type="var">subtype</span> <span class="id"
type="var">S</span> <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">subtype</span> <span class="id" type="var">T</span> <span
class="id" type="var">U</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">subtype</span> <span class="id" type="var">S</span> <span
class="id" type="var">U</span>.\
\

</div>

<div class="doc">

Adding reflexivity as hint is generally a good idea, so let's add
reflexivity of subtyping as hint.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Resolve</span> <span class="id"
type="var">subtype\_refl</span>.\
\

</div>

<div class="doc">

Adding transitivity as hint is generally a bad idea. To understand why,
let's add it as hint and see what happens. Because we cannot remove
hints once we've added them, we are going to open a "Section," so as to
restrict the scope of the transitivity hint to that section.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Section</span> <span class="id"
type="var">HintsTransitivity</span>.\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Resolve</span> <span class="id"
type="var">subtype\_trans</span>.\
\

</div>

<div class="doc">

Now, consider the goal <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">S</span></span> <span
class="inlinecode"><span class="id" type="var">T</span>,</span> <span
class="inlinecode"><span class="id" type="var">subtype</span></span>
<span class="inlinecode"><span class="id" type="var">S</span></span>
<span class="inlinecode"><span class="id" type="var">T</span></span>,
which clearly has no hope of being solved. Let's call <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span> on
this goal.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">transitivity\_bad\_hint\_1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">S</span>
<span class="id" type="var">T</span>,\
   <span class="id" type="var">subtype</span> <span class="id"
type="var">S</span> <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span
class="comment">(\* debug \*)</span> <span class="id"
type="tactic">eauto</span>. <span
class="comment">(\* Investigates 106 applications... \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

Note that after closing the section, the hint <span
class="inlinecode"><span class="id"
type="var">subtype\_trans</span></span> is no longer active.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">HintsTransitivity</span>.\
\

</div>

<div class="doc">

In the previous example, the proof search has spent a lot of time trying
to apply transitivity and reflexivity in every possible way. Its process
can be summarized as follows. The first goal is <span
class="inlinecode"><span class="id" type="var">subtype</span></span>
<span class="inlinecode"><span class="id" type="var">S</span></span>
<span class="inlinecode"><span class="id" type="var">T</span></span>.
Since reflexivity does not apply, <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> invokes transitivity, which
produces two subgoals, <span class="inlinecode"><span class="id"
type="var">subtype</span></span> <span class="inlinecode"><span
class="id" type="var">S</span></span> <span class="inlinecode">?<span
class="id" type="var">X</span></span> and <span class="inlinecode"><span
class="id" type="var">subtype</span></span> <span
class="inlinecode">?<span class="id" type="var">X</span></span> <span
class="inlinecode"><span class="id" type="var">T</span></span>. Solving
the first subgoal, <span class="inlinecode"><span class="id"
type="var">subtype</span></span> <span class="inlinecode"><span
class="id" type="var">S</span></span> <span class="inlinecode">?<span
class="id" type="var">X</span></span>, is straightforward, it suffices
to apply reflexivity. This unifies <span class="inlinecode">?<span
class="id" type="var">X</span></span> with <span
class="inlinecode"><span class="id" type="var">S</span></span>. So, the
second sugoal, <span class="inlinecode"><span class="id"
type="var">subtype</span></span> <span class="inlinecode">?<span
class="id" type="var">X</span></span> <span class="inlinecode"><span
class="id" type="var">T</span></span>, becomes <span
class="inlinecode"><span class="id" type="var">subtype</span></span>
<span class="inlinecode"><span class="id" type="var">S</span></span>
<span class="inlinecode"><span class="id" type="var">T</span></span>,
which is exactly what we started from...
<div class="paragraph">

</div>

The problem with the transitivity lemma is that it is applicable to any
goal concluding on a subtyping relation. Because of this, <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span>
keeps trying to apply it even though it most often doesn't help to solve
the goal. So, one should never add a transitivity lemma as a hint for
proof search.
<div class="paragraph">

</div>

There is a general workaround for having automation to exploit
transitivity lemmas without giving up on efficiency. This workaround
relies on a powerful mechanism called "external hint." This mechanism
allows to manually describe the condition under which a particular lemma
should be tried out during proof search.
<div class="paragraph">

</div>

For the case of transitivity of subtyping, we are going to tell Coq to
try and apply the transitivity lemma on a goal of the form <span
class="inlinecode"><span class="id" type="var">subtype</span></span>
<span class="inlinecode"><span class="id" type="var">S</span></span>
<span class="inlinecode"><span class="id" type="var">U</span></span>
only when the proof context already contains an assumption either of the
form <span class="inlinecode"><span class="id"
type="var">subtype</span></span> <span class="inlinecode"><span
class="id" type="var">S</span></span> <span class="inlinecode"><span
class="id" type="var">T</span></span> or of the form <span
class="inlinecode"><span class="id" type="var">subtype</span></span>
<span class="inlinecode"><span class="id" type="var">T</span></span>
<span class="inlinecode"><span class="id" type="var">U</span></span>. In
other words, we only apply the transitivity lemma when there is some
evidence that this application might help. To set up this "external
hint," one has to write the following.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Extern</span> 1 (<span class="id"
type="var">subtype</span> ?<span class="id" type="var">S</span> ?<span
class="id" type="var">U</span>) ⇒\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">goal</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">H</span>: <span class="id"
type="var">subtype</span> <span class="id" type="var">S</span> ?<span
class="id" type="var">T</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">\_</span> ⇒ <span class="id" type="tactic">apply</span>
(@<span class="id" type="var">subtype\_trans</span> <span class="id"
type="var">S</span> <span class="id" type="var">T</span> <span
class="id" type="var">U</span>)\
   | <span class="id" type="var">H</span>: <span class="id"
type="var">subtype</span> ?<span class="id" type="var">T</span> <span
class="id" type="var">U</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">\_</span> ⇒ <span class="id" type="tactic">apply</span>
(@<span class="id" type="var">subtype\_trans</span> <span class="id"
type="var">S</span> <span class="id" type="var">T</span> <span
class="id" type="var">U</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

This hint declaration can be understood as follows.
<div class="paragraph">

</div>

-   "Hint Extern" introduces the hint.
-   The number "1" corresponds to a priority for proof search. It
    doesn't matter so much what priority is used in practice.
-   The pattern <span class="inlinecode"><span class="id"
    type="var">subtype</span></span> <span class="inlinecode">?<span
    class="id" type="var">S</span></span> <span
    class="inlinecode">?<span class="id" type="var">U</span></span>
    describes the kind of goal on which the pattern should apply. The
    question marks are used to indicate that the variables <span
    class="inlinecode">?<span class="id" type="var">S</span></span> and
    <span class="inlinecode">?<span class="id"
    type="var">U</span></span> should be bound to some value in the rest
    of the hint description.
-   The construction <span class="inlinecode"><span class="id"
    type="keyword">match</span></span> <span class="inlinecode"><span
    class="id" type="var">goal</span></span> <span
    class="inlinecode"><span class="id"
    type="keyword">with</span></span> <span
    class="inlinecode">...</span> <span class="inlinecode"><span
    class="id" type="keyword">end</span></span> tries to recognize
    patterns in the goal, or in the proof context, or both.
-   The first pattern is <span class="inlinecode"><span class="id"
    type="var">H</span>:</span> <span class="inlinecode"><span
    class="id" type="var">subtype</span></span> <span
    class="inlinecode"><span class="id" type="var">S</span></span> <span
    class="inlinecode">?<span class="id" type="var">T</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">\_</span></span>. It
    indices that the context should contain an hypothesis <span
    class="inlinecode"><span class="id" type="var">H</span></span> of
    type <span class="inlinecode"><span class="id"
    type="var">subtype</span></span> <span class="inlinecode"><span
    class="id" type="var">S</span></span> <span
    class="inlinecode">?<span class="id" type="var">T</span></span>,
    where <span class="inlinecode"><span class="id"
    type="var">S</span></span> has to be the same as in the goal, and
    where <span class="inlinecode">?<span class="id"
    type="var">T</span></span> can have any value.
-   The symbol <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">\_</span></span> at
    the end of <span class="inlinecode"><span class="id"
    type="var">H</span>:</span> <span class="inlinecode"><span
    class="id" type="var">subtype</span></span> <span
    class="inlinecode"><span class="id" type="var">S</span></span> <span
    class="inlinecode">?<span class="id" type="var">T</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">\_</span></span>
    indicates that we do not impose further condition on how the proof
    obligation has to look like.
-   The branch <span class="inlinecode">⇒</span> <span
    class="inlinecode"><span class="id"
    type="tactic">apply</span></span> <span class="inlinecode">(@<span
    class="id" type="var">subtype\_trans</span></span> <span
    class="inlinecode"><span class="id" type="var">S</span></span> <span
    class="inlinecode"><span class="id" type="var">T</span></span> <span
    class="inlinecode"><span class="id" type="var">U</span>)</span> that
    follows indicates that if the goal has the form <span
    class="inlinecode"><span class="id" type="var">subtype</span></span>
    <span class="inlinecode"><span class="id" type="var">S</span></span>
    <span class="inlinecode"><span class="id" type="var">U</span></span>
    and if there exists an hypothesis of the form <span
    class="inlinecode"><span class="id" type="var">subtype</span></span>
    <span class="inlinecode"><span class="id" type="var">S</span></span>
    <span class="inlinecode"><span class="id"
    type="var">T</span></span>, then we should try and apply
    transitivity lemma instantiated on the arguments <span
    class="inlinecode"><span class="id" type="var">S</span></span>,
    <span class="inlinecode"><span class="id" type="var">T</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">U</span></span>. (Note: the symbol <span
    class="inlinecode">@</span> in front of <span
    class="inlinecode"><span class="id"
    type="var">subtype\_trans</span></span> is only actually needed when
    the "Implicit Arguments" feature is activated.)
-   The other branch, which corresponds to an hypothesis of the form
    <span class="inlinecode"><span class="id"
    type="var">H</span>:</span> <span class="inlinecode"><span
    class="id" type="var">subtype</span></span> <span
    class="inlinecode">?<span class="id" type="var">T</span></span>
    <span class="inlinecode"><span class="id" type="var">U</span></span>
    is symmetrical.

Note: the same external hint can be reused for any other transitive
relation, simply by renaming <span class="inlinecode"><span class="id"
type="var">subtype</span></span> into the name of that relation.
<div class="paragraph">

</div>

Let us see an example illustrating how the hint works.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">transitivity\_workaround\_1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> <span
class="id" type="var">T3</span> <span class="id" type="var">T4</span>,\
   <span class="id" type="var">subtype</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">subtype</span> <span class="id" type="var">T~2~</span> <span
class="id" type="var">T3</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">subtype</span> <span class="id" type="var">T3</span> <span
class="id" type="var">T4</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">subtype</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T4</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span
class="comment">(\* debug \*)</span> <span class="id"
type="tactic">eauto</span>. <span
class="comment">(\* The trace shows the external hint being used \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

We may also check that the new external hint does not suffer from the
complexity blow up.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">transitivity\_workaround\_2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">S</span>
<span class="id" type="var">T</span>,\
   <span class="id" type="var">subtype</span> <span class="id"
type="var">S</span> <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span
class="comment">(\* debug \*)</span> <span class="id"
type="tactic">eauto</span>. <span
class="comment">(\* Investigates 0 applications \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

Decision Procedures {.section}
===================

<div class="paragraph">

</div>

A decision procedure is able to solve proof obligations whose statement
admits a particular form. This section describes three useful decision
procedures. The tactic <span class="inlinecode"><span class="id"
type="tactic">omega</span></span> handles goals involving arithmetic and
inequalities, but not general multiplications. The tactic <span
class="inlinecode"><span class="id" type="tactic">ring</span></span>
handles goals involving arithmetic, including multiplications, but does
not support inequalities. The tactic <span class="inlinecode"><span
class="id" type="tactic">congruence</span></span> is able to prove
equalities and inequalities by exploiting equalities available in the
proof context.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Omega {.section}
-----

<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="tactic">omega</span></span> supports natural numbers (type <span
class="inlinecode"><span class="id" type="var">nat</span></span>) as
well as integers (type <span class="inlinecode"><span class="id"
type="var">Z</span></span>, available by including the module <span
class="inlinecode"><span class="id" type="var">ZArith</span></span>). It
supports addition, substraction, equalities and inequalities. Before
using <span class="inlinecode"><span class="id"
type="tactic">omega</span></span>, one needs to import the module <span
class="inlinecode"><span class="id" type="var">Omega</span></span>, as
follows.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Omega</span>.\
\

</div>

<div class="doc">

Here is an example. Let <span class="inlinecode"><span class="id"
type="var">x</span></span> and <span class="inlinecode"><span class="id"
type="var">y</span></span> be two natural numbers (they cannot be
negative). Assume <span class="inlinecode"><span class="id"
type="var">y</span></span> is less than 4, assume <span
class="inlinecode"><span class="id" type="var">x</span>+<span class="id"
type="var">x</span>+1</span> is less than <span class="inlinecode"><span
class="id" type="var">y</span></span>, and assume <span
class="inlinecode"><span class="id" type="var">x</span></span> is not
zero. Then, it must be the case that <span class="inlinecode"><span
class="id" type="var">x</span></span> is equal to one.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">omega\_demo\_1</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> <span class="id" type="var">y</span> : <span
class="id" type="var">nat</span>),\
   (<span class="id" type="var">y</span> ≤ 4) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">x</span> + <span class="id" type="var">x</span> + 1 ≤ <span
class="id" type="var">y</span>) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">x</span> ≠ 0) <span style="font-family: arial;">→</span>
(<span class="id" type="var">x</span> = 1).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span>. <span class="id"
type="tactic">omega</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Another example: if <span class="inlinecode"><span class="id"
type="var">z</span></span> is the mean of <span class="inlinecode"><span
class="id" type="var">x</span></span> and <span class="inlinecode"><span
class="id" type="var">y</span></span>, and if the difference between
<span class="inlinecode"><span class="id" type="var">x</span></span> and
<span class="inlinecode"><span class="id" type="var">y</span></span> is
at most <span class="inlinecode">4</span>, then the difference between
<span class="inlinecode"><span class="id" type="var">x</span></span> and
<span class="inlinecode"><span class="id" type="var">z</span></span> is
at most 2.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">omega\_demo\_2</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span> : <span class="id"
type="var">nat</span>),\
   (<span class="id" type="var">x</span> + <span class="id"
type="var">y</span> = <span class="id" type="var">z</span> + <span
class="id" type="var">z</span>) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">x</span> - <span class="id" type="var">y</span> ≤ 4) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">x</span> - <span class="id" type="var">z</span> ≤ 2).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span>. <span class="id"
type="tactic">omega</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

One can proof <span class="inlinecode"><span class="id"
type="var">False</span></span> using <span class="inlinecode"><span
class="id" type="tactic">omega</span></span> if the mathematical facts
from the context are contradictory. In the following example, the
constraints on the values <span class="inlinecode"><span class="id"
type="var">x</span></span> and <span class="inlinecode"><span class="id"
type="var">y</span></span> cannot be all satisfied in the same time.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">omega\_demo\_3</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> <span class="id" type="var">y</span> : <span
class="id" type="var">nat</span>),\
   (<span class="id" type="var">x</span> + 5 ≤ <span class="id"
type="var">y</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">y</span> - <span class="id" type="var">x</span> \<
3) <span style="font-family: arial;">→</span> <span class="id"
type="var">False</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span>. <span class="id"
type="tactic">omega</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Note: <span class="inlinecode"><span class="id"
type="tactic">omega</span></span> can prove a goal by contradiction only
if its conclusion is reduced <span class="inlinecode"><span class="id"
type="var">False</span></span>. The tactic <span
class="inlinecode"><span class="id" type="tactic">omega</span></span>
always fails when the conclusion is an arbitrary proposition <span
class="inlinecode"><span class="id" type="var">P</span></span>, even
though <span class="inlinecode"><span class="id"
type="var">False</span></span> implies any proposition <span
class="inlinecode"><span class="id" type="var">P</span></span> (by <span
class="inlinecode"><span class="id"
type="var">ex\_falso\_quodlibet</span></span>).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">omega\_demo\_4</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> <span class="id" type="var">y</span> : <span
class="id" type="var">nat</span>) (<span class="id" type="var">P</span>
: <span class="id" type="keyword">Prop</span>),\
   (<span class="id" type="var">x</span> + 5 ≤ <span class="id"
type="var">y</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">y</span> - <span class="id" type="var">x</span> \<
3) <span style="font-family: arial;">→</span> <span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="comment">(\* Calling <span class="inlinecode"><span
class="id"
type="tactic">omega</span></span> at this point fails with the message:\
     "Omega: Can't solve a goal with proposition variables" \*)</span>\
   <span class="comment">(\* So, one needs to replace the goal by <span
class="inlinecode"><span class="id"
type="var">False</span></span> first. \*)</span>\
   <span class="id" type="var">false</span>. <span class="id"
type="tactic">omega</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Ring {.section}
----

<div class="paragraph">

</div>

Compared with <span class="inlinecode"><span class="id"
type="tactic">omega</span></span>, the tactic <span
class="inlinecode"><span class="id" type="tactic">ring</span></span>
adds support for multiplications, however it gives up the ability to
reason on inequations. Moreover, it supports only integers (type <span
class="inlinecode"><span class="id" type="var">Z</span></span>) and not
natural numbers (type <span class="inlinecode"><span class="id"
type="var">nat</span></span>). Here is an example showing how to use
<span class="inlinecode"><span class="id"
type="tactic">ring</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">RingDemo</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">ZArith</span>.\
   <span class="id" type="keyword">Open</span> <span class="id"
type="keyword">Scope</span> <span class="id"
type="var">Z\_scope</span>.\
   <span
class="comment">(\* Arithmetic symbols are now interpreted in <span
class="inlinecode"><span class="id"
type="var">Z</span></span> \*)</span>\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">ring\_demo</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span> : <span class="id" type="var">Z</span>),\
     <span class="id" type="var">x</span> × (<span class="id"
type="var">y</span> + <span class="id" type="var">z</span>) - <span
class="id" type="var">z</span> × 3 × <span class="id"
type="var">x</span>\
   = <span class="id" type="var">x</span> × <span class="id"
type="var">y</span> - 2 × <span class="id" type="var">x</span> × <span
class="id" type="var">z</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span>. <span class="id" type="tactic">ring</span>.
<span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">RingDemo</span>.\
\

</div>

<div class="doc">

Congruence {.section}
----------

<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="tactic">congruence</span></span> is able to exploit equalities
from the proof context in order to automatically perform the rewriting
operations necessary to establish a goal. It is slightly more powerful
than the tactic <span class="inlinecode"><span class="id"
type="tactic">subst</span></span>, which can only handle equalities of
the form <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">e</span></span> where
<span class="inlinecode"><span class="id" type="var">x</span></span> is
a variable and <span class="inlinecode"><span class="id"
type="var">e</span></span> an expression.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">congruence\_demo\_1</span> :\
    <span style="font-family: arial;">∀</span>(<span class="id"
type="var">f</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span>) (<span class="id" type="var">g</span>
<span class="id" type="var">h</span> : <span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span>) (<span class="id" type="var">x</span>
<span class="id" type="var">y</span> <span class="id"
type="var">z</span> : <span class="id" type="var">nat</span>),\
    <span class="id" type="var">f</span> (<span class="id"
type="var">g</span> <span class="id" type="var">x</span>) (<span
class="id" type="var">g</span> <span class="id" type="var">y</span>) =
<span class="id" type="var">z</span> <span
style="font-family: arial;">→</span>\
    2 = <span class="id" type="var">g</span> <span class="id"
type="var">x</span> <span style="font-family: arial;">→</span>\
    <span class="id" type="var">g</span> <span class="id"
type="var">y</span> = <span class="id" type="var">h</span> <span
class="id" type="var">z</span> <span
style="font-family: arial;">→</span>\
    <span class="id" type="var">f</span> 2 (<span class="id"
type="var">h</span> <span class="id" type="var">z</span>) = <span
class="id" type="var">z</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span>. <span class="id"
type="tactic">congruence</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Moreover, <span class="inlinecode"><span class="id"
type="tactic">congruence</span></span> is able to exploit universally
quantified equalities, for example <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">a</span>,</span> <span
class="inlinecode"><span class="id" type="var">g</span></span> <span
class="inlinecode"><span class="id" type="var">a</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">h</span></span> <span class="inlinecode"><span class="id"
type="var">a</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">congruence\_demo\_2</span> :\
    <span style="font-family: arial;">∀</span>(<span class="id"
type="var">f</span> : <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span>) (<span class="id" type="var">g</span>
<span class="id" type="var">h</span> : <span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span>) (<span class="id" type="var">x</span>
<span class="id" type="var">y</span> <span class="id"
type="var">z</span> : <span class="id" type="var">nat</span>),\
    (<span style="font-family: arial;">∀</span><span class="id"
type="var">a</span>, <span class="id" type="var">g</span> <span
class="id" type="var">a</span> = <span class="id" type="var">h</span>
<span class="id" type="var">a</span>) <span
style="font-family: arial;">→</span>\
    <span class="id" type="var">f</span> (<span class="id"
type="var">g</span> <span class="id" type="var">x</span>) (<span
class="id" type="var">g</span> <span class="id" type="var">y</span>) =
<span class="id" type="var">z</span> <span
style="font-family: arial;">→</span>\
    <span class="id" type="var">g</span> <span class="id"
type="var">x</span> = 2 <span style="font-family: arial;">→</span>\
    <span class="id" type="var">f</span> 2 (<span class="id"
type="var">h</span> <span class="id" type="var">y</span>) = <span
class="id" type="var">z</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">congruence</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Next is an example where <span class="inlinecode"><span class="id"
type="tactic">congruence</span></span> is very useful.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">congruence\_demo\_4</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">f</span> <span class="id" type="var">g</span> : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">nat</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">a</span>, <span class="id" type="var">f</span> <span
class="id" type="var">a</span> = <span class="id" type="var">g</span>
<span class="id" type="var">a</span>) <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">f</span> (<span class="id"
type="var">g</span> (<span class="id" type="var">g</span> 2)) = <span
class="id" type="var">g</span> (<span class="id" type="var">f</span>
(<span class="id" type="var">f</span> 2)).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">congruence</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="tactic">congruence</span></span> is able to prove a contradiction
if the goal entails an equality that contradicts an inequality available
in the proof context.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">congruence\_demo\_3</span> :\
    <span style="font-family: arial;">∀</span>(<span class="id"
type="var">f</span> <span class="id" type="var">g</span> <span
class="id" type="var">h</span> : <span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span>) (<span class="id" type="var">x</span>
: <span class="id" type="var">nat</span>),\
    (<span style="font-family: arial;">∀</span><span class="id"
type="var">a</span>, <span class="id" type="var">f</span> <span
class="id" type="var">a</span> = <span class="id" type="var">h</span>
<span class="id" type="var">a</span>) <span
style="font-family: arial;">→</span>\
    <span class="id" type="var">g</span> <span class="id"
type="var">x</span> = <span class="id" type="var">f</span> <span
class="id" type="var">x</span> <span
style="font-family: arial;">→</span>\
    <span class="id" type="var">g</span> <span class="id"
type="var">x</span> ≠ <span class="id" type="var">h</span> <span
class="id" type="var">x</span> <span
style="font-family: arial;">→</span>\
    <span class="id" type="var">False</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">congruence</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

One of the strengths of <span class="inlinecode"><span class="id"
type="tactic">congruence</span></span> is that it is a very fast tactic.
So, one should not hesitate to invoke it wherever it might help.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Summary {.section}
=======

<div class="paragraph">

</div>

Let us summarize the main automation tactics available.
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="tactic">auto</span></span> automatically applies <span
    class="inlinecode"><span class="id"
    type="tactic">reflexivity</span></span>, <span
    class="inlinecode"><span class="id"
    type="tactic">assumption</span></span>, and <span
    class="inlinecode"><span class="id"
    type="tactic">apply</span></span>.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">eauto</span></span> moreover tries <span
    class="inlinecode"><span class="id"
    type="tactic">eapply</span></span>, and in particular can
    instantiate existentials in the conclusion.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">iauto</span></span> extends <span
    class="inlinecode"><span class="id"
    type="tactic">eauto</span></span> with support for negation,
    conjunctions, and disjunctions. However, its support for disjunction
    can make it exponentially slow.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">jauto</span></span> extends <span
    class="inlinecode"><span class="id"
    type="tactic">eauto</span></span> with support for negation,
    conjunctions, and existential at the head of hypothesis.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">congruence</span></span> helps reasoning about
    equalities and inequalities.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">omega</span></span> proves arithmetic goals with
    equalities and inequalities, but it does not support multiplication.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">ring</span></span> proves arithmetic goals with
    multiplications, but does not support inequalities.

In order to set up automation appropriately, keep in mind the following
rule of thumbs:
<div class="paragraph">

</div>

-   automation is all about balance: not enough automation makes proofs
    not very robust on change, whereas too much automation makes proofs
    very hard to fix when they break.
    <div class="paragraph">

    </div>

-   if a lemma is not goal directed (i.e., some of its variables do not
    occur in its conclusion), then the premises need to be ordered in
    such a way that proving the first premises maximizes the chances of
    correctly instantiating the variables that do not occur in the
    conclusion.
    <div class="paragraph">

    </div>

-   a lemma whose conclusion is <span class="inlinecode"><span
    class="id" type="var">False</span></span> should only be added as a
    local hint, i.e., as a hint within the current section.
    <div class="paragraph">

    </div>

-   a transitivity lemma should never be considered as hint; if
    automation of transitivity reasoning is really necessary, an <span
    class="inlinecode"><span class="id"
    type="keyword">Extern</span></span> <span class="inlinecode"><span
    class="id" type="keyword">Hint</span></span> needs to be set up.
    <div class="paragraph">

    </div>

-   a definition usually needs to be accompanied with a <span
    class="inlinecode"><span class="id"
    type="keyword">Hint</span></span> <span class="inlinecode"><span
    class="id" type="keyword">Unfold</span></span>.

Becoming a master in the black art of automation certainly requires some
investment, however this investment will pay off very quickly.
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
