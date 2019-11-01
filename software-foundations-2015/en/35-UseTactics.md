<div id="page">

<div id="header">

</div>

<div id="main">

UseTactics<span class="subtitle">Tactic Library for Coq: A Gentle Introduction</span> {.libtitle}
=====================================================================================

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

Coq comes with a set of builtin tactics, such as <span
class="inlinecode"><span class="id"
type="tactic">reflexivity</span></span>, <span class="inlinecode"><span
class="id" type="tactic">intros</span></span>, <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span> and so on. While it is possible to
conduct proofs using only those tactics, you can significantly increase
your productivity by working with a set of more powerful tactics. This
chapter describes a number of such very useful tactics, which, for
various reasons, are not yet available by default in Coq. These tactics
are defined in the <span class="inlinecode"><span class="id"
type="var">LibTactics.v</span></span> file.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id"
type="var">LibTactics</span>.\
\

</div>

<div class="doc">

Remark: SSReflect is another package providing powerful tactics. The
library "LibTactics" differs from "SSReflect" in two respects:
<div class="paragraph">

</div>

-   "SSReflect" was primarily developed for proving mathematical
    theorems, whereas "LibTactics" was primarily developed for proving
    theorems on programming languages. In particular, "LibTactics"
    provides a number of useful tactics that have no counterpart in the
    "SSReflect" package.
-   "SSReflect" entirely rethinks the presentation of tactics, whereas
    "LibTactics" mostly stick to the traditional presentation of Coq
    tactics, simply providing a number of additional tactics. For this
    reason, "LibTactics" is probably easier to get started with than
    "SSReflect".

<div class="paragraph">

</div>

This chapter is a tutorial focusing on the most useful features from the
"LibTactics" library. It does not aim at presenting all the features of
"LibTactics". The detailed specification of tactics can be found in the
source file <span class="inlinecode"><span class="id"
type="var">LibTactics.v</span></span>. Further documentation as well as
demos can be found at http://www.chargueraud.org/softs/tlc/ .
<div class="paragraph">

</div>

In this tutorial, tactics are presented using examples taken from the
core chapters of the "Software Foundations" course. To illustrate the
various ways in which a given tactic can be used, we use a tactic that
duplicates a given goal. More precisely, <span class="inlinecode"><span
class="id" type="var">dup</span></span> produces two copies of the
current goal, and <span class="inlinecode"><span class="id"
type="var">dup</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> produces <span class="inlinecode"><span
class="id" type="var">n</span></span> copies of it.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Tactics for introduction and case analysis {.section}
==========================================

<div class="paragraph">

</div>

This section presents the following tactics:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">introv</span></span>, for naming hypotheses more
    efficiently,
-   <span class="inlinecode"><span class="id"
    type="var">inverts</span></span>, for improving the <span
    class="inlinecode"><span class="id"
    type="tactic">inversion</span></span> tactic,
-   <span class="inlinecode"><span class="id"
    type="var">cases</span></span>, for performing a case analysis
    without losing information,
-   <span class="inlinecode"><span class="id"
    type="var">cases\_if</span></span>, for automating case analysis on
    the argument of <span class="inlinecode"><span class="id"
    type="keyword">if</span></span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id" type="var">introv</span></span> {.section}
------------------------------------------------------------------------------------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">IntrovExamples</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Stlc</span>.\
   <span class="id" type="keyword">Import</span> <span class="id"
type="var">Imp</span> <span class="id" type="var">STLC</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="var">introv</span></span> allows to automatically introduce the
variables of a theorem and explicitly name the hypotheses involved. In
the example shown next, the variables <span class="inlinecode"><span
class="id" type="var">c</span></span>, <span class="inlinecode"><span
class="id" type="var">st</span></span>, <span class="inlinecode"><span
class="id" type="var">st1</span></span> and <span
class="inlinecode"><span class="id" type="var">st2</span></span>
involved in the statement of determinism need not be named explicitly,
because their name where already given in the statement of the lemma. On
the contrary, it is useful to provide names for the two hypotheses,
which we name <span class="inlinecode"><span class="id"
type="var">E1</span></span> and <span class="inlinecode"><span
class="id" type="var">E2</span></span>, respectively.

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
   <span class="id" type="var">introv</span> <span class="id"
type="var">E1</span> <span class="id" type="var">E2</span>. <span
class="comment">(\* was <span class="inlinecode"><span class="id"
type="tactic">intros</span></span> <span class="inlinecode"><span
class="id" type="var">c</span></span> <span class="inlinecode"><span
class="id" type="var">st</span></span> <span class="inlinecode"><span
class="id" type="var">st1</span></span> <span class="inlinecode"><span
class="id" type="var">st2</span></span> <span class="inlinecode"><span
class="id" type="var">E1</span></span> <span class="inlinecode"><span
class="id" type="var">E2</span></span> \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

When there is no hypothesis to be named, one can call <span
class="inlinecode"><span class="id" type="var">introv</span></span>
without any argument.

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
   <span class="id" type="var">introv</span>. <span
class="comment">(\* was <span class="inlinecode"><span class="id"
type="tactic">intros</span></span> <span class="inlinecode"><span
class="id" type="var">X</span></span> <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode"><span
class="id" type="var">Q</span></span> \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="var">introv</span></span> also applies to statements in which
<span class="inlinecode"><span
style="font-family: arial;">∀</span></span> and <span
class="inlinecode"><span style="font-family: arial;">→</span></span> are
interleaved.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_deterministic'</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st1</span>,\
   (<span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st1</span>) <span
style="font-family: arial;">→</span> <span
style="font-family: arial;">∀</span><span class="id"
type="var">st2</span>, (<span class="id" type="var">c</span> / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st2</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">st1</span> = <span class="id"
type="var">st2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">introv</span> <span class="id"
type="var">E1</span> <span class="id" type="var">E2</span>. <span
class="comment">(\* was <span class="inlinecode"><span class="id"
type="tactic">intros</span></span> <span class="inlinecode"><span
class="id" type="var">c</span></span> <span class="inlinecode"><span
class="id" type="var">st</span></span> <span class="inlinecode"><span
class="id" type="var">st1</span></span> <span class="inlinecode"><span
class="id" type="var">E1</span></span> <span class="inlinecode"><span
class="id" type="var">st2</span></span> <span class="inlinecode"><span
class="id" type="var">E2</span></span> \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

Like the arguments of <span class="inlinecode"><span class="id"
type="tactic">intros</span></span>, the arguments of <span
class="inlinecode"><span class="id" type="var">introv</span></span> can
be structured patterns.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">exists\_impl</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">X</span>
(<span class="id" type="var">P</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>) (<span class="id"
type="var">Q</span> : <span class="id" type="keyword">Prop</span>)
(<span class="id" type="var">R</span> : <span class="id"
type="keyword">Prop</span>),\
       (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span class="id" type="var">P</span> <span
class="id" type="var">x</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span>) <span style="font-family: arial;">→</span>\
       ((<span style="font-family: arial;">∃</span><span class="id"
type="var">x</span>, <span class="id" type="var">P</span> <span
class="id" type="var">x</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">introv</span> [<span class="id"
type="var">x</span> <span class="id" type="var">H2</span>]. <span
class="id" type="tactic">eauto</span>.\
   <span class="comment">(\* same as <span class="inlinecode"><span
class="id" type="tactic">intros</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">Q</span></span> <span
class="inlinecode"><span class="id" type="var">R</span></span> <span
class="inlinecode"><span class="id" type="var">H1</span></span> <span
class="inlinecode">[<span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id"
type="var">H2</span>].</span>, which is itself short \
      for <span class="inlinecode"><span class="id"
type="tactic">intros</span></span> <span class="inlinecode"><span
class="id" type="var">X</span></span> <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode"><span
class="id" type="var">Q</span></span> <span class="inlinecode"><span
class="id" type="var">R</span></span> <span class="inlinecode"><span
class="id" type="var">H1</span></span> <span class="inlinecode"><span
class="id" type="var">H2</span>.</span> <span class="inlinecode"><span
class="id" type="tactic">destruct</span></span> <span
class="inlinecode"><span class="id" type="var">H2</span></span> <span
class="inlinecode"><span class="id" type="keyword">as</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span></span>
<span class="inlinecode"><span class="id"
type="var">H2</span>].</span> \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Remark: the tactic <span class="inlinecode"><span class="id"
type="var">introv</span></span> works even when definitions need to be
unfolded in order to reveal hypotheses.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">IntrovExamples</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id" type="var">inverts</span></span> {.section}
-------------------------------------------------------------------------------------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">InvertsExamples</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Stlc</span>
<span class="id" type="var">Equiv</span> <span class="id"
type="var">Imp</span>.\
   <span class="id" type="keyword">Import</span> <span class="id"
type="var">STLC</span>.\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> tactic of Coq is not very
satisfying for three reasons. First, it produces a bunch of equalities
which one typically wants to substitute away, using <span
class="inlinecode"><span class="id" type="tactic">subst</span></span>.
Second, it introduces meaningless names for hypotheses. Third, a call to
<span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> does not remove <span
class="inlinecode"><span class="id" type="var">H</span></span> from the
context, even though in most cases an hypothesis is no longer needed
after being inverted. The tactic <span class="inlinecode"><span
class="id" type="var">inverts</span></span> address all of these three
issues. It is intented to be used in place of the tactic <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span>.
<div class="paragraph">

</div>

The following example illustrates how the tactic <span
class="inlinecode"><span class="id" type="var">inverts</span></span>
<span class="inlinecode"><span class="id" type="var">H</span></span>
behaves mostly like <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> except that it performs some
substitutions in order to eliminate the trivial equalities that are
being produced by <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">skip\_left</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">c</span>,\
   <span class="id" type="var">cequiv</span> (<span class="id"
type="var">SKIP</span>;; <span class="id" type="var">c</span>) <span
class="id" type="var">c</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">introv</span>. <span class="id"
type="tactic">split</span>; <span class="id" type="tactic">intros</span>
<span class="id" type="var">H</span>.\
   <span class="id" type="var">dup</span>. <span
class="comment">(\* duplicate the goal for comparison \*)</span>\
   <span class="comment">(\* was: \*)</span>\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">H2</span>. <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">assumption</span>.\
   <span class="comment">(\* now: \*)</span>\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">H</span>. <span class="id" type="var">inverts</span> <span
class="id" type="var">H2</span>. <span class="id"
type="tactic">assumption</span>.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

A slightly more interesting example appears next.

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
   <span class="id" type="var">introv</span> <span class="id"
type="var">E1</span> <span class="id" type="var">E2</span>. <span
class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>.\
   (<span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>); <span class="id"
type="tactic">intros</span> <span class="id" type="var">st2</span> <span
class="id" type="var">E2</span>.\
   <span class="id" type="var">admit</span>. <span class="id"
type="var">admit</span>. <span
class="comment">(\* skip some basic cases \*)</span>\
   <span class="id" type="var">dup</span>. <span
class="comment">(\* duplicate the goal for comparison \*)</span>\
   <span class="comment">(\* was: \*)</span> <span class="id"
type="tactic">inversion</span> <span class="id" type="var">E2</span>.
<span class="id" type="tactic">subst</span>. <span class="id"
type="var">admit</span>.\
   <span class="comment">(\* now: \*)</span> <span class="id"
type="var">inverts</span> <span class="id" type="var">E2</span>. <span
class="id" type="var">admit</span>.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="var">inverts</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> <span class="inlinecode"><span
class="id" type="keyword">as</span>.</span> is like <span
class="inlinecode"><span class="id" type="var">inverts</span></span>
<span class="inlinecode"><span class="id" type="var">H</span></span>
except that the variables and hypotheses being produced are placed in
the goal rather than in the context. This strategy allows naming those
new variables and hypotheses explicitly, using either <span
class="inlinecode"><span class="id" type="tactic">intros</span></span>
or <span class="inlinecode"><span class="id"
type="var">introv</span></span>.

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
   <span class="id" type="var">introv</span> <span class="id"
type="var">E1</span> <span class="id" type="var">E2</span>. <span
class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>.\
   (<span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>); <span class="id"
type="tactic">intros</span> <span class="id" type="var">st2</span> <span
class="id" type="var">E2</span>;\
     <span class="id" type="var">inverts</span> <span class="id"
type="var">E2</span> <span class="id" type="keyword">as</span>.\
   <span class="id" type="var">Case</span> "E\_Skip". <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "E\_Ass".\
     <span class="comment">(\* Observe that the variable <span
class="inlinecode"><span class="id"
type="var">n</span></span> is not automatically \
        substituted because, contrary to <span class="inlinecode"><span
class="id" type="tactic">inversion</span></span> <span
class="inlinecode"><span class="id" type="var">E2</span>;</span> <span
class="inlinecode"><span class="id" type="tactic">subst</span></span>,\
        the tactic <span class="inlinecode"><span class="id"
type="var">inverts</span></span> <span class="inlinecode"><span
class="id"
type="var">E2</span></span> does not substitute the equalities\
        that exist before running the inversion. \*)</span>\
     <span class="comment">(\* new: \*)</span> <span class="id"
type="tactic">subst</span> <span class="id" type="var">n</span>.\
     <span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "E\_Seq".\
     <span
class="comment">(\* Here, the newly created variables can be introduced\
        using intros, so they can be assigned meaningful names,\
        for example <span class="inlinecode"><span class="id"
type="var">st3</span></span> instead of <span class="inlinecode"><span
class="id" type="var">st'0</span></span>. \*)</span>\
     <span class="comment">(\* new: \*)</span> <span class="id"
type="tactic">intros</span> <span class="id" type="var">st3</span> <span
class="id" type="var">Red1</span> <span class="id"
type="var">Red2</span>.\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st3</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">EQ1</span>.\
       <span class="id" type="var">SCase</span> "Proof of assertion".
<span class="id" type="tactic">apply</span> <span class="id"
type="var">IHE1\_1</span>; <span class="id"
type="tactic">assumption</span>.\
     <span class="id" type="tactic">subst</span> <span class="id"
type="var">st3</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHE1\_2</span>. <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "E\_IfTrue".\
     <span class="id" type="var">SCase</span> "b1 evaluates to true".\
       <span
class="comment">(\* In an easy case like this one, there is no need to\
          provide meaningful names, so we can just use <span
class="inlinecode"><span class="id"
type="tactic">intros</span></span> \*)</span>\
       <span class="comment">(\* new: \*)</span> <span class="id"
type="tactic">intros</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHE1</span>. <span class="id"
type="tactic">assumption</span>.\
     <span class="id" type="var">SCase</span> "b1 evaluates to false
(contradiction)".\
       <span class="comment">(\* new: \*)</span> <span class="id"
type="tactic">intros</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H5</span>.\
   <span class="comment">(\* The other cases are similiar \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

In the particular case where a call to <span class="inlinecode"><span
class="id" type="tactic">inversion</span></span> produces a single
subgoal, one can use the syntax <span class="inlinecode"><span
class="id" type="var">inverts</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span> <span
class="inlinecode"><span class="id" type="keyword">as</span></span>
<span class="inlinecode"><span class="id" type="var">H1</span></span>
<span class="inlinecode"><span class="id" type="var">H2</span></span>
<span class="inlinecode"><span class="id" type="var">H3</span></span>
for calling <span class="inlinecode"><span class="id"
type="var">inverts</span></span> and naming the new hypotheses <span
class="inlinecode"><span class="id" type="var">H1</span></span>, <span
class="inlinecode"><span class="id" type="var">H2</span></span> and
<span class="inlinecode"><span class="id" type="var">H3</span></span>.
In other words, the tactic <span class="inlinecode"><span class="id"
type="var">inverts</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> <span class="inlinecode"><span
class="id" type="keyword">as</span></span> <span
class="inlinecode"><span class="id" type="var">H1</span></span> <span
class="inlinecode"><span class="id" type="var">H2</span></span> <span
class="inlinecode"><span class="id" type="var">H3</span></span> is
equivalent to <span class="inlinecode"><span class="id"
type="var">inverts</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> <span class="inlinecode"><span
class="id" type="keyword">as</span>;</span> <span
class="inlinecode"><span class="id" type="var">introv</span></span>
<span class="inlinecode"><span class="id" type="var">H1</span></span>
<span class="inlinecode"><span class="id" type="var">H2</span></span>
<span class="inlinecode"><span class="id" type="var">H3</span></span>.
An example follows.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">skip\_left'</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">c</span>,\
   <span class="id" type="var">cequiv</span> (<span class="id"
type="var">SKIP</span>;; <span class="id" type="var">c</span>) <span
class="id" type="var">c</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">introv</span>. <span class="id"
type="tactic">split</span>; <span class="id" type="tactic">intros</span>
<span class="id" type="var">H</span>.\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">U</span> <span class="id" type="var">V</span>.
<span class="comment">(\* new hypotheses are named <span
class="inlinecode"><span class="id" type="var">U</span></span> and <span
class="inlinecode"><span class="id"
type="var">V</span></span> \*)</span>\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">U</span>. <span class="id" type="tactic">assumption</span>.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

A more involved example appears next. In particular, this example shows
that the name of the hypothesis being inverted can be reused.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_nonexample\_1</span> :\
   ¬ <span style="font-family: arial;">∃</span><span class="id"
type="var">T</span>,\
       <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span>\
         (<span class="id" type="var">tabs</span> <span class="id"
type="var">x</span> <span class="id" type="var">TBool</span>\
             (<span class="id" type="var">tabs</span> <span class="id"
type="var">y</span> <span class="id" type="var">TBool</span>\
                (<span class="id" type="var">tapp</span> (<span
class="id" type="var">tvar</span> <span class="id" type="var">x</span>)
(<span class="id" type="var">tvar</span> <span class="id"
type="var">y</span>))))\
         <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">dup</span> 3.\
\
   <span class="comment">(\* The old proof: \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">C</span>. <span class="id" type="tactic">destruct</span>
<span class="id" type="var">C</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H5</span>. <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H5</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H4</span>. <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H4</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H2</span>. <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H2</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H5</span>. <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H5</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H1</span>.\
\
   <span class="comment">(\* The new proof: \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">C</span>. <span class="id" type="tactic">destruct</span>
<span class="id" type="var">C</span>.\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">H1</span>.\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">H1</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">H2</span>.\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">H2</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">H3</span>.\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">H3</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">H4</span>.\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">H4</span>.\
\
   <span class="comment">(\* The new proof, alternative: \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">C</span>. <span class="id" type="tactic">destruct</span>
<span class="id" type="var">C</span>.\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="var">inverts</span> <span class="id"
type="var">H</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">InvertsExamples</span>.\
\

</div>

<div class="doc">

Note: in the rare cases where one needs to perform an inversion on an
hypothesis <span class="inlinecode"><span class="id"
type="var">H</span></span> without clearing <span
class="inlinecode"><span class="id" type="var">H</span></span> from the
context, one can use the tactic <span class="inlinecode"><span
class="id" type="var">inverts</span></span> <span
class="inlinecode"><span class="id" type="var">keep</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span>, where
the keyword <span class="inlinecode"><span class="id"
type="var">keep</span></span> indicates that the hypothesis should be
kept in the context.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Tactics for n-ary connectives {.section}
=============================

<div class="paragraph">

</div>

Because Coq encodes conjunctions and disjunctions using binary
constructors <span class="inlinecode"><span
style="font-family: arial;">∧</span></span> and <span
class="inlinecode"><span style="font-family: arial;">∨</span></span>,
working with a conjunction or a disjunction of <span
class="inlinecode"><span class="id" type="var">N</span></span> facts can
sometimes be quite cumbursome. For this reason, "LibTactics" provides
tactics offering direct support for n-ary conjunctions and disjunctions.
It also provides direct support for n-ary existententials.
<div class="paragraph">

</div>

This section presents the following tactics:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">splits</span></span> for decomposing n-ary conjunctions,
-   <span class="inlinecode"><span class="id"
    type="var">branch</span></span> for decomposing n-ary disjunctions,
-   <span class="inlinecode"><span
    style="font-family: arial;">∃</span></span> for proving n-ary
    existentials.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">NaryExamples</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id"
type="var">References</span> <span class="id" type="var">SfLib</span>.\
   <span class="id" type="keyword">Import</span> <span class="id"
type="var">STLCRef</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id" type="var">splits</span></span> {.section}
------------------------------------------------------------------------------------

<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="var">splits</span></span> applies to a goal made of a conjunction
of <span class="inlinecode"><span class="id" type="var">n</span></span>
propositions and it produces <span class="inlinecode"><span class="id"
type="var">n</span></span> subgoals. For example, it decomposes the goal
<span class="inlinecode"><span class="id" type="var">G1</span></span>
<span class="inlinecode"><span
style="font-family: arial;">∧</span></span> <span
class="inlinecode"><span class="id" type="var">G2</span></span> <span
class="inlinecode"><span style="font-family: arial;">∧</span></span>
<span class="inlinecode"><span class="id" type="var">G3</span></span>
into the three subgoals <span class="inlinecode"><span class="id"
type="var">G1</span></span>, <span class="inlinecode"><span class="id"
type="var">G2</span></span> and <span class="inlinecode"><span
class="id" type="var">G3</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_splits</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">n</span> \> 0 <span
style="font-family: arial;">∧</span> <span class="id"
type="var">n</span> \< <span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">m</span> \< <span class="id" type="var">n</span>+10 <span
style="font-family: arial;">∧</span> <span class="id"
type="var">m</span> ≠ 3.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="var">splits</span>.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id" type="var">branch</span></span> {.section}
------------------------------------------------------------------------------------

<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="var">branch</span></span> <span class="inlinecode"><span
class="id" type="var">k</span></span> can be used to prove a n-ary
disjunction. For example, if the goal takes the form <span
class="inlinecode"><span class="id" type="var">G1</span></span> <span
class="inlinecode"><span style="font-family: arial;">∨</span></span>
<span class="inlinecode"><span class="id" type="var">G2</span></span>
<span class="inlinecode"><span
style="font-family: arial;">∨</span></span> <span
class="inlinecode"><span class="id" type="var">G3</span></span>, the
tactic <span class="inlinecode"><span class="id"
type="var">branch</span></span> <span class="inlinecode">2</span> leaves
only <span class="inlinecode"><span class="id"
type="var">G2</span></span> as subgoal. The following example
illustrates the behavior of the <span class="inlinecode"><span
class="id" type="var">branch</span></span> tactic.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_branch</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">n</span> \< <span class="id"
type="var">m</span> <span style="font-family: arial;">∨</span> <span
class="id" type="var">n</span> = <span class="id" type="var">m</span>
<span style="font-family: arial;">∨</span> <span class="id"
type="var">m</span> \< <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">lt\_eq\_lt\_dec</span> <span class="id" type="var">n</span>
<span class="id" type="var">m</span>) <span class="id"
type="keyword">as</span> [[<span class="id" type="var">H1</span>|<span
class="id" type="var">H2</span>]|<span class="id"
type="var">H3</span>].\
   <span class="id" type="var">branch</span> 1. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H1</span>.\
   <span class="id" type="var">branch</span> 2. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H2</span>.\
   <span class="id" type="var">branch</span> 3. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H3</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span style="font-family: arial;">∃</span></span> {.section}
-------------------------------------------------------------------------------------

<div class="paragraph">

</div>

The library "LibTactics" introduces a notation for n-ary existentials.
For example, one can write <span class="inlinecode"><span
style="font-family: arial;">∃</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">y</span></span> <span
class="inlinecode"><span class="id" type="var">z</span>,</span> <span
class="inlinecode"><span class="id" type="var">H</span></span> instead
of <span class="inlinecode"><span
style="font-family: arial;">∃</span></span> <span
class="inlinecode"><span class="id" type="var">x</span>,</span> <span
class="inlinecode"><span style="font-family: arial;">∃</span></span>
<span class="inlinecode"><span class="id" type="var">y</span>,</span>
<span class="inlinecode"><span
style="font-family: arial;">∃</span></span> <span
class="inlinecode"><span class="id" type="var">z</span>,</span> <span
class="inlinecode"><span class="id" type="var">H</span></span>.
Similarly, the library provides a n-ary tactic <span
class="inlinecode"><span style="font-family: arial;">∃</span></span>
<span class="inlinecode"><span class="id" type="var">a</span></span>
<span class="inlinecode"><span class="id" type="var">b</span></span>
<span class="inlinecode"><span class="id" type="var">c</span></span>,
which is a shorthand for <span class="inlinecode"><span
style="font-family: arial;">∃</span></span> <span
class="inlinecode"><span class="id" type="var">a</span>;</span> <span
class="inlinecode"><span style="font-family: arial;">∃</span></span>
<span class="inlinecode"><span class="id" type="var">b</span>;</span>
<span class="inlinecode"><span
style="font-family: arial;">∃</span></span> <span
class="inlinecode"><span class="id" type="var">c</span></span>. The
following example illustrates both the notation and the tactic for
dealing with n-ary existentials.

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
   <span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">∨</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span> <span class="id" type="var">st'</span>, <span
class="id" type="var">t</span> / <span class="id" type="var">st</span>
<span style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span> / <span class="id" type="var">st'</span>.\
   <span class="comment">(\* was: <span class="inlinecode"><span
class="id" type="var">value</span></span> <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">∨</span></span> <span
class="inlinecode"><span style="font-family: arial;">∃</span></span>
<span class="inlinecode"><span class="id" type="var">t'</span>,</span>
<span class="inlinecode"><span
style="font-family: arial;">∃</span></span> <span
class="inlinecode"><span class="id" type="var">st'</span>,</span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">/</span> <span class="inlinecode"><span class="id"
type="var">st</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> <span
class="inlinecode">/</span> <span class="inlinecode"><span class="id"
type="var">st'</span></span> \*)</span>\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span class="id" type="var">st</span>
<span class="id" type="var">Ht</span> <span class="id"
type="var">HST</span>. <span class="id" type="var">remember</span>
(@<span class="id" type="var">empty</span> <span class="id"
type="var">ty</span>) <span class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   (<span class="id" type="var">has\_type\_cases</span> (<span
class="id" type="tactic">induction</span> <span class="id"
type="var">Ht</span>) <span class="id" type="var">Case</span>); <span
class="id" type="tactic">subst</span>; <span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">inversion</span>...\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">IHHt1</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">Ht1p</span> | <span class="id" type="var">Ht1p</span>]...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">Ht2p</span> | <span class="id"
type="var">Ht2p</span>]...\
       <span class="id" type="var">SSCase</span> "t~2~ steps".\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">Ht2p</span> <span class="id"
type="keyword">as</span> [<span class="id" type="var">t~2~'</span>
[<span class="id" type="var">st'</span> <span class="id"
type="var">Hstep</span>]].\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> (<span class="id" type="var">tabs</span> <span
class="id" type="var">x</span> <span class="id" type="var">T</span>
<span class="id" type="var">t</span>) <span class="id"
type="var">t~2~'</span>) <span class="id" type="var">st'</span>...\
         <span class="comment">(\* was: <span class="inlinecode"><span
style="font-family: arial;">∃</span></span> <span
class="inlinecode">(<span class="id" type="var">tapp</span></span> <span
class="inlinecode">(<span class="id" type="var">tabs</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">T</span></span> <span
class="inlinecode"><span class="id" type="var">t</span>)</span> <span
class="inlinecode"><span class="id" type="var">t~2~'</span>).</span>
<span class="inlinecode"><span
style="font-family: arial;">∃</span></span> <span
class="inlinecode"><span class="id"
type="var">st'</span>...</span> \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

Remark: a similar facility for n-ary existentials is provided by the
module <span class="inlinecode"><span class="id"
type="var">Coq.Program.Syntax</span></span> from the standard library.
(<span class="inlinecode"><span class="id"
type="var">Coq.Program.Syntax</span></span> supports existentials up to
arity 4; <span class="inlinecode"><span class="id"
type="var">LibTactics</span></span> supports them up to arity 10.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">NaryExamples</span>.\
\

</div>

<div class="doc">

Tactics for working with equality {.section}
=================================

<div class="paragraph">

</div>

One of the major weakness of Coq compared with other interactive proof
assistants is its relatively poor support for reasoning with equalities.
The tactics described next aims at simplifying pieces of proof scripts
manipulating equalities.
<div class="paragraph">

</div>

This section presents the following tactics:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">asserts\_rewrite</span></span> for introducing an
    equality to rewrite with,
-   <span class="inlinecode"><span class="id"
    type="var">cuts\_rewrite</span></span>, which is similar except that
    its subgoals are swapped,
-   <span class="inlinecode"><span class="id"
    type="var">substs</span></span> for improving the <span
    class="inlinecode"><span class="id"
    type="tactic">subst</span></span> tactic,
-   <span class="inlinecode"><span class="id"
    type="var">fequals</span></span> for improving the <span
    class="inlinecode"><span class="id"
    type="tactic">f\_equal</span></span> tactic,
-   <span class="inlinecode"><span class="id"
    type="var">applys\_eq</span></span> for proving <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode"><span class="id" type="var">x</span></span> <span
    class="inlinecode"><span class="id" type="var">y</span></span> using
    an hypothesis <span class="inlinecode"><span class="id"
    type="var">P</span></span> <span class="inlinecode"><span class="id"
    type="var">x</span></span> <span class="inlinecode"><span class="id"
    type="var">z</span></span>, automatically producing an equality
    <span class="inlinecode"><span class="id" type="var">y</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">z</span></span> as subgoal.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">EqualityExamples</span>.\
\

</div>

<div class="doc">

The tactics <span class="inlinecode"><span class="id" type="var">asserts\_rewrite</span></span> and <span class="inlinecode"><span class="id" type="var">cuts\_rewrite</span></span> {.section}
------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="var">asserts\_rewrite</span></span> <span
class="inlinecode">(<span class="id" type="var">E1</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">E2</span>)</span> replaces <span class="inlinecode"><span
class="id" type="var">E1</span></span> with <span
class="inlinecode"><span class="id" type="var">E2</span></span> in the
goal, and produces the goal <span class="inlinecode"><span class="id"
type="var">E1</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">E2</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">mult\_0\_plus</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> : <span class="id"
type="var">nat</span>,\
   (0 + <span class="id" type="var">n</span>) × <span class="id"
type="var">m</span> = <span class="id" type="var">n</span> × <span
class="id" type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">dup</span>.\
   <span class="comment">(\* The old proof: \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span>.\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">H</span>: 0 + <span class="id" type="var">n</span> = <span
class="id" type="var">n</span>). <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">H</span>.\
   <span class="id" type="tactic">reflexivity</span>.\
\
   <span class="comment">(\* The new proof: \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span>.\
   <span class="id" type="var">asserts\_rewrite</span> (0 + <span
class="id" type="var">n</span> = <span class="id" type="var">n</span>).\
     <span class="id" type="tactic">reflexivity</span>. <span
class="comment">(\* subgoal <span class="inlinecode">0+<span class="id"
type="var">n</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id"
type="var">n</span></span> \*)</span>\
     <span class="id" type="tactic">reflexivity</span>. <span
class="comment">(\* subgoal <span class="inlinecode"><span class="id"
type="var">n</span>×<span class="id" type="var">m</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">m</span>×<span class="id"
type="var">n</span></span> \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="comment">(\*\*\* Remark: the syntax <span
class="inlinecode"><span class="id"
type="var">asserts\_rewrite</span></span> <span
class="inlinecode">(<span class="id" type="var">E1</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">E2</span>)</span> <span class="inlinecode"><span class="id"
type="keyword">in</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> allows\
      rewriting in the hypothesis <span class="inlinecode"><span
class="id"
type="var">H</span></span> rather than in the goal. \*)</span>\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="var">cuts\_rewrite</span></span> <span class="inlinecode">(<span
class="id" type="var">E1</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">E2</span>)</span>
is like <span class="inlinecode"><span class="id"
type="var">asserts\_rewrite</span></span> <span
class="inlinecode">(<span class="id" type="var">E1</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">E2</span>)</span>, except that the equality <span
class="inlinecode"><span class="id" type="var">E1</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">E2</span></span> appears as first subgoal.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">mult\_0\_plus'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> : <span class="id"
type="var">nat</span>,\
   (0 + <span class="id" type="var">n</span>) × <span class="id"
type="var">m</span> = <span class="id" type="var">n</span> × <span
class="id" type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span>.\
   <span class="id" type="var">cuts\_rewrite</span> (0 + <span
class="id" type="var">n</span> = <span class="id" type="var">n</span>).\
     <span class="id" type="tactic">reflexivity</span>. <span
class="comment">(\* subgoal <span class="inlinecode"><span class="id"
type="var">n</span>×<span class="id" type="var">m</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">m</span>×<span class="id"
type="var">n</span></span> \*)</span>\
     <span class="id" type="tactic">reflexivity</span>. <span
class="comment">(\* subgoal <span class="inlinecode">0+<span class="id"
type="var">n</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id"
type="var">n</span></span> \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

More generally, the tactics <span class="inlinecode"><span class="id"
type="var">asserts\_rewrite</span></span> and <span
class="inlinecode"><span class="id"
type="var">cuts\_rewrite</span></span> can be provided a lemma as
argument. For example, one can write <span class="inlinecode"><span
class="id" type="var">asserts\_rewrite</span></span> <span
class="inlinecode">(<span style="font-family: arial;">∀</span></span>
<span class="inlinecode"><span class="id" type="var">a</span></span>
<span class="inlinecode"><span class="id" type="var">b</span>,</span>
<span class="inlinecode"><span class="id" type="var">a</span>\*(<span
class="id" type="var">S</span></span> <span class="inlinecode"><span
class="id" type="var">b</span>)</span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">a</span>×<span
class="id" type="var">b</span>+<span class="id"
type="var">a</span>)</span>. This formulation is useful when <span
class="inlinecode"><span class="id" type="var">a</span></span> and <span
class="inlinecode"><span class="id" type="var">b</span></span> are big
terms, since there is no need to repeat their statements.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">mult\_0\_plus''</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">u</span>
<span class="id" type="var">v</span> <span class="id"
type="var">w</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span> <span class="id" type="var">z</span>:
<span class="id" type="var">nat</span>,\
   (<span class="id" type="var">u</span> + <span class="id"
type="var">v</span>) × (<span class="id" type="var">S</span> (<span
class="id" type="var">w</span> × <span class="id" type="var">x</span> +
<span class="id" type="var">y</span>)) = <span class="id"
type="var">z</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="var">asserts\_rewrite</span> (<span
style="font-family: arial;">∀</span><span class="id" type="var">a</span>
<span class="id" type="var">b</span>, <span class="id"
type="var">a</span>\*(<span class="id" type="var">S</span> <span
class="id" type="var">b</span>) = <span class="id"
type="var">a</span>×<span class="id" type="var">b</span>+<span
class="id" type="var">a</span>).\
     <span class="comment">(\* first subgoal:  <span
class="inlinecode"><span style="font-family: arial;">∀</span></span>
<span class="inlinecode"><span class="id" type="var">a</span></span>
<span class="inlinecode"><span class="id" type="var">b</span>,</span>
<span class="inlinecode"><span class="id" type="var">a</span>\*(<span
class="id" type="var">S</span></span> <span class="inlinecode"><span
class="id" type="var">b</span>)</span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">a</span>×<span
class="id" type="var">b</span>+<span class="id"
type="var">a</span></span> \*)</span>\
     <span class="comment">(\* second subgoal: <span
class="inlinecode">(<span class="id" type="var">u</span></span> <span
class="inlinecode">+</span> <span class="inlinecode"><span class="id"
type="var">v</span>)</span> <span class="inlinecode">×</span> <span
class="inlinecode">(<span class="id" type="var">w</span></span> <span
class="inlinecode">×</span> <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode">+</span> <span
class="inlinecode"><span class="id" type="var">y</span>)</span> <span
class="inlinecode">+</span> <span class="inlinecode">(<span class="id"
type="var">u</span></span> <span class="inlinecode">+</span> <span
class="inlinecode"><span class="id" type="var">v</span>)</span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">z</span></span> \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id" type="var">substs</span></span> {.section}
------------------------------------------------------------------------------------

<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="var">substs</span></span> is similar to <span
class="inlinecode"><span class="id" type="tactic">subst</span></span>
except that it does not fail when the goal contains "circular
equalities", such as <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">f</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_substs</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">y</span> (<span class="id"
type="var">f</span>:<span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">nat</span>),\
   <span class="id" type="var">x</span> = <span class="id"
type="var">f</span> <span class="id" type="var">x</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">y</span> = <span class="id" type="var">x</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">y</span> = <span class="id" type="var">f</span> <span
class="id" type="var">x</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="var">substs</span>. <span class="comment">(\* the tactic <span
class="inlinecode"><span class="id"
type="tactic">subst</span></span> would fail here \*)</span>\
   <span class="id" type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id" type="var">fequals</span></span> {.section}
-------------------------------------------------------------------------------------

<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="var">fequals</span></span> is similar to <span
class="inlinecode"><span class="id" type="tactic">f\_equal</span></span>
except that it directly discharges all the trivial subgoals produced.
Moreover, the tactic <span class="inlinecode"><span class="id"
type="var">fequals</span></span> features an enhanced treatment of
equalities between tuples.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_fequals</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span> <span class="id" type="var">d</span>
<span class="id" type="var">e</span> : <span class="id"
type="var">nat</span>) (<span class="id" type="var">f</span> : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span>),\
   <span class="id" type="var">a</span> = 1 <span
style="font-family: arial;">→</span> <span class="id"
type="var">b</span> = <span class="id" type="var">e</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">e</span> = 2 <span style="font-family: arial;">→</span>\
   <span class="id" type="var">f</span> <span class="id"
type="var">a</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span> <span class="id" type="var">d</span> =
<span class="id" type="var">f</span> 1 2 <span class="id"
type="var">c</span> 4.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="var">fequals</span>.\
   <span class="comment">(\* subgoals <span class="inlinecode"><span
class="id" type="var">a</span></span> <span class="inlinecode">=</span>
<span class="inlinecode">1</span>, <span class="inlinecode"><span
class="id" type="var">b</span></span> <span class="inlinecode">=</span>
<span class="inlinecode">2</span> and <span class="inlinecode"><span
class="id" type="var">c</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">c</span></span> are proved, <span class="inlinecode"><span
class="id" type="var">d</span></span> <span class="inlinecode">=</span>
<span class="inlinecode">4</span> remains \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id" type="var">applys\_eq</span></span> {.section}
----------------------------------------------------------------------------------------

<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="var">applys\_eq</span></span> is a variant of <span
class="inlinecode"><span class="id" type="tactic">eapply</span></span>
that introduces equalities for subterms that do not unify. For example,
assume the goal is the proposition <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="var">y</span></span> and assume we have the assumption
<span class="inlinecode"><span class="id" type="var">H</span></span>
asserting that <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode"><span class="id"
type="var">z</span></span> holds. We know that we can prove <span
class="inlinecode"><span class="id" type="var">y</span></span> to be
equal to <span class="inlinecode"><span class="id"
type="var">z</span></span>. So, we could call the tactic <span
class="inlinecode"><span class="id"
type="var">assert\_rewrite</span></span> <span class="inlinecode">(<span
class="id" type="var">y</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">z</span>)</span>
and change the goal to <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode"><span class="id"
type="var">z</span></span>, but this would require copy-pasting the
values of <span class="inlinecode"><span class="id"
type="var">y</span></span> and <span class="inlinecode"><span class="id"
type="var">z</span></span>. With the tactic <span
class="inlinecode"><span class="id" type="var">applys\_eq</span></span>,
we can call <span class="inlinecode"><span class="id"
type="var">applys\_eq</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> <span class="inlinecode">1</span>,
which proves the goal and leaves only the subgoal <span
class="inlinecode"><span class="id" type="var">y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">z</span></span>. The value <span class="inlinecode">1</span>
given as argument to <span class="inlinecode"><span class="id"
type="var">applys\_eq</span></span> indicates that we want an equality
to be introduced for the first argument of <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">y</span></span> counting
from the right. The three following examples illustrate the behavior of
a call to <span class="inlinecode"><span class="id"
type="var">applys\_eq</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> <span class="inlinecode">1</span>,
a call to <span class="inlinecode"><span class="id"
type="var">applys\_eq</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> <span class="inlinecode">2</span>,
and a call to <span class="inlinecode"><span class="id"
type="var">applys\_eq</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> <span class="inlinecode">1</span>
<span class="inlinecode">2</span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Axiom</span> <span class="id"
type="var">big\_expression\_using</span> : <span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span>. <span
class="comment">(\* Used in the example \*)</span>\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_applys\_eq\_1</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span>:<span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="keyword">Prop</span>) <span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span>,\
   <span class="id" type="var">P</span> <span class="id"
type="var">x</span> (<span class="id"
type="var">big\_expression\_using</span> <span class="id"
type="var">z</span>) <span style="font-family: arial;">→</span>\
   <span class="id" type="var">P</span> <span class="id"
type="var">x</span> (<span class="id"
type="var">big\_expression\_using</span> <span class="id"
type="var">y</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">introv</span> <span class="id"
type="var">H</span>. <span class="id" type="var">dup</span>.\
\
   <span class="comment">(\* The old proof: \*)</span>\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">Eq</span>: <span class="id"
type="var">big\_expression\_using</span> <span class="id"
type="var">y</span> = <span class="id"
type="var">big\_expression\_using</span> <span class="id"
type="var">z</span>).\
     <span class="id" type="var">admit</span>. <span
class="comment">(\* Assume we can prove this equality somehow. \*)</span>\
   <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">Eq</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">H</span>.\
\
   <span class="comment">(\* The new proof: \*)</span>\
   <span class="id" type="var">applys\_eq</span> <span class="id"
type="var">H</span> 1.\
     <span class="id" type="var">admit</span>. <span
class="comment">(\* Assume we can prove this equality somehow. \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

If the mismatch was on the first argument of <span
class="inlinecode"><span class="id" type="var">P</span></span> instead
of the second, we would have written <span class="inlinecode"><span
class="id" type="var">applys\_eq</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span> <span
class="inlinecode">2</span>. Recall that the occurences are counted from
the right.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_applys\_eq\_2</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span>:<span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="keyword">Prop</span>) <span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span>,\
   <span class="id" type="var">P</span> (<span class="id"
type="var">big\_expression\_using</span> <span class="id"
type="var">z</span>) <span class="id" type="var">x</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">P</span> (<span class="id"
type="var">big\_expression\_using</span> <span class="id"
type="var">y</span>) <span class="id" type="var">x</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">introv</span> <span class="id"
type="var">H</span>. <span class="id" type="var">applys\_eq</span> <span
class="id" type="var">H</span> 2.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

When we have a mismatch on two arguments, we want to produce two
equalities. To achieve this, we may call <span class="inlinecode"><span
class="id" type="var">applys\_eq</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span> <span
class="inlinecode">1</span> <span class="inlinecode">2</span>. More
generally, the tactic <span class="inlinecode"><span class="id"
type="var">applys\_eq</span></span> expects a lemma and a sequence of
natural numbers as arguments.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_applys\_eq\_3</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span>:<span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="keyword">Prop</span>) <span class="id"
type="var">x1</span> <span class="id" type="var">x2</span> <span
class="id" type="var">y1</span> <span class="id" type="var">y2</span>,\
   <span class="id" type="var">P</span> (<span class="id"
type="var">big\_expression\_using</span> <span class="id"
type="var">x2</span>) (<span class="id"
type="var">big\_expression\_using</span> <span class="id"
type="var">y2</span>) <span style="font-family: arial;">→</span>\
   <span class="id" type="var">P</span> (<span class="id"
type="var">big\_expression\_using</span> <span class="id"
type="var">x1</span>) (<span class="id"
type="var">big\_expression\_using</span> <span class="id"
type="var">y1</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">introv</span> <span class="id"
type="var">H</span>. <span class="id" type="var">applys\_eq</span> <span
class="id" type="var">H</span> 1 2.\
   <span class="comment">(\* produces two subgoals:\
      <span class="inlinecode"><span class="id"
type="var">big\_expression\_using</span></span> <span
class="inlinecode"><span class="id" type="var">x1</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">big\_expression\_using</span></span> <span
class="inlinecode"><span class="id" type="var">x2</span></span>\
      <span class="inlinecode"><span class="id"
type="var">big\_expression\_using</span></span> <span
class="inlinecode"><span class="id" type="var">y1</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">big\_expression\_using</span></span> <span
class="inlinecode"><span class="id"
type="var">y2</span></span> \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">EqualityExamples</span>.\
\

</div>

<div class="doc">

Some convenient shorthands {.section}
==========================

<div class="paragraph">

</div>

This section of the tutorial introduces a few tactics that help make
proof scripts shorter and more readable:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">unfolds</span></span> (without argument) for unfolding
    the head definition,
-   <span class="inlinecode"><span class="id"
    type="var">false</span></span> for replacing the goal with <span
    class="inlinecode"><span class="id" type="var">False</span></span>,
-   <span class="inlinecode"><span class="id"
    type="var">gen</span></span> as a shorthand for <span
    class="inlinecode"><span class="id"
    type="tactic">dependent</span></span> <span class="inlinecode"><span
    class="id" type="tactic">generalize</span></span>,
-   <span class="inlinecode"><span class="id"
    type="var">skip</span></span> for skipping a subgoal even if it
    contains existential variables,
-   <span class="inlinecode"><span class="id"
    type="var">sort</span></span> for re-ordering the proof context by
    moving moving all propositions at the bottom.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id" type="var">unfolds</span></span> {.section}
-------------------------------------------------------------------------------------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">UnfoldsExample</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Hoare</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="var">unfolds</span></span> (without any argument) unfolds the head
constant of the goal. This tactic saves the need to name the constant
explicitly.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">bexp\_eval\_true</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">st</span>,\
   <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span> (<span class="id"
type="var">bassn</span> <span class="id" type="var">b</span>) <span
class="id" type="var">st</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">st</span> <span
class="id" type="var">Hbe</span>. <span class="id"
type="var">dup</span>.\
\
   <span class="comment">(\* The old proof: \*)</span>\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bassn</span>. <span class="id"
type="tactic">assumption</span>.\
\
   <span class="comment">(\* The new proof: \*)</span>\
   <span class="id" type="var">unfolds</span>. <span class="id"
type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Remark: contrary to the tactic <span class="inlinecode"><span class="id"
type="var">hnf</span></span>, which may unfold several constants, <span
class="inlinecode"><span class="id" type="var">unfolds</span></span>
performs only a single step of unfolding.
<div class="paragraph">

</div>

Remark: the tactic <span class="inlinecode"><span class="id"
type="var">unfolds</span></span> <span class="inlinecode"><span
class="id" type="keyword">in</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span> can be
used to unfold the head definition of the hypothesis <span
class="inlinecode"><span class="id" type="var">H</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">UnfoldsExample</span>.\
\

</div>

<div class="doc">

The tactics <span class="inlinecode"><span class="id" type="var">false</span></span> and <span class="inlinecode"><span class="id" type="var">tryfalse</span></span> {.section}
--------------------------------------------------------------------------------------------------------------------------------------------------------------------

<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="var">false</span></span> can be used to replace any goal with
<span class="inlinecode"><span class="id"
type="var">False</span></span>. In short, it is a shorthand for <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
<span class="inlinecode"><span class="id"
type="var">ex\_falso\_quodlibet</span></span>. Moreover, <span
class="inlinecode"><span class="id" type="var">false</span></span>
proves the goal if it contains an absurd assumption, such as <span
class="inlinecode"><span class="id" type="var">False</span></span> or
<span class="inlinecode">0</span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">S</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span>, or
if it contains contradictory assumptions, such as <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">true</span></span> and <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">false</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_false</span> :\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">S</span> <span
class="id" type="var">n</span> = 1 <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> = 0.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">n</span>.
<span class="id" type="tactic">reflexivity</span>. <span class="id"
type="var">false</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="var">false</span></span> can be given an argument: <span
class="inlinecode"><span class="id" type="var">false</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span> replace
the goals with <span class="inlinecode"><span class="id"
type="var">False</span></span> and then applies <span
class="inlinecode"><span class="id" type="var">H</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_false\_arg</span> :\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">n</span> \< 0 <span
style="font-family: arial;">→</span> <span class="id"
type="var">False</span>) <span style="font-family: arial;">→</span> (3
\< 0) <span style="font-family: arial;">→</span> 4 \< 0.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">H</span> <span class="id" type="var">L</span>. <span
class="id" type="var">false</span> <span class="id" type="var">H</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">L</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="var">tryfalse</span></span> is a shorthand for <span
class="inlinecode"><span class="id" type="tactic">try</span></span>
<span class="inlinecode"><span class="id" type="var">solve</span></span>
<span class="inlinecode">[<span class="id"
type="var">false</span>]</span>: it tries to find a contradiction in the
goal. The tactic <span class="inlinecode"><span class="id"
type="var">tryfalse</span></span> is generally called after a case
analysis.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_tryfalse</span> :\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">S</span> <span
class="id" type="var">n</span> = 1 <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> = 0.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">n</span>;
<span class="id" type="var">tryfalse</span>. <span class="id"
type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id" type="var">gen</span></span> {.section}
---------------------------------------------------------------------------------

<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="var">gen</span></span> is a shortand for <span
class="inlinecode"><span class="id"
type="tactic">generalize</span></span> <span class="inlinecode"><span
class="id" type="tactic">dependent</span></span> that accepts several
arguments at once. An invokation of this tactic takes the form <span
class="inlinecode"><span class="id" type="var">gen</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">y</span></span> <span
class="inlinecode"><span class="id" type="var">z</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">GenExample</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Stlc</span>.\
   <span class="id" type="keyword">Import</span> <span class="id"
type="var">STLC</span>.\
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
   <span class="id" type="var">dup</span>.\
\
   <span class="comment">(\* The old proof: \*)</span>\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span> <span
class="id" type="var">v</span> <span class="id" type="var">t</span>
<span class="id" type="var">S</span> <span class="id"
type="var">Htypt</span> <span class="id" type="var">Htypv</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">S</span>.
<span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">t</span>; <span class="id" type="tactic">intros</span>; <span
class="id" type="tactic">simpl</span>.\
   <span class="id" type="var">admit</span>. <span class="id"
type="var">admit</span>. <span class="id" type="var">admit</span>. <span
class="id" type="var">admit</span>. <span class="id"
type="var">admit</span>. <span class="id" type="var">admit</span>.\
\
   <span class="comment">(\* The new proof: \*)</span>\
   <span class="id" type="var">introv</span> <span class="id"
type="var">Htypt</span> <span class="id" type="var">Htypv</span>. <span
class="id" type="var">gen</span> <span class="id" type="var">S</span>
<span style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">t</span>; <span class="id" type="tactic">intros</span>; <span
class="id" type="tactic">simpl</span>.\
   <span class="id" type="var">admit</span>. <span class="id"
type="var">admit</span>. <span class="id" type="var">admit</span>. <span
class="id" type="var">admit</span>. <span class="id"
type="var">admit</span>. <span class="id" type="var">admit</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">GenExample</span>.\
\

</div>

<div class="doc">

The tactics <span class="inlinecode"><span class="id" type="var">skip</span></span>, <span class="inlinecode"><span class="id" type="var">skip\_rewrite</span></span> and <span class="inlinecode"><span class="id" type="var">skip\_goal</span></span> {.section}
-------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

<div class="paragraph">

</div>

Temporarily admitting a given subgoal is very useful when constructing
proofs. It gives the ability to focus first on the most interesting
cases of a proof. The tactic <span class="inlinecode"><span class="id"
type="var">skip</span></span> is like <span class="inlinecode"><span
class="id" type="var">admit</span></span> except that it also works when
the proof includes existential variables. Recall that existential
variables are those whose name starts with a question mark, e.g. <span
class="inlinecode">?24</span>, and which are typically introduced by
<span class="inlinecode"><span class="id"
type="tactic">eapply</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">SkipExample</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Stlc</span>.\
   <span class="id" type="keyword">Import</span> <span class="id"
type="var">STLC</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">astep\_example1</span> :\
   (<span class="id" type="var">APlus</span> (<span class="id"
type="var">ANum</span> 3) (<span class="id" type="var">AMult</span>
(<span class="id" type="var">ANum</span> 3) (<span class="id"
type="var">ANum</span> 4))) / <span class="id"
type="var">empty\_state</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span>× (<span class="id" type="var">ANum</span> 15).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id" type="var">skip</span>.
<span class="comment">(\* the tactic <span class="inlinecode"><span
class="id"
type="var">admit</span></span> would not work here \*)</span>\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id" type="var">skip</span>.
<span class="id" type="var">skip</span>.\
   <span
class="comment">(\* Note that because some unification variables have\
      not been instantiated, we still need to write\
      <span class="inlinecode"><span class="id"
type="keyword">Abort</span></span> instead of <span
class="inlinecode"><span class="id"
type="keyword">Qed</span></span> at the end of the proof. \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="var">skip</span></span> <span class="inlinecode"><span class="id"
type="var">H</span>:</span> <span class="inlinecode"><span class="id"
type="var">P</span></span> adds the hypothesis <span
class="inlinecode"><span class="id" type="var">H</span>:</span> <span
class="inlinecode"><span class="id" type="var">P</span></span> to the
context, without checking whether the proposition <span
class="inlinecode"><span class="id" type="var">P</span></span> is true.
It is useful for exploiting a fact and postponing its proof. Note: <span
class="inlinecode"><span class="id" type="var">skip</span></span> <span
class="inlinecode"><span class="id" type="var">H</span>:</span> <span
class="inlinecode"><span class="id" type="var">P</span></span> is simply
a shorthand for <span class="inlinecode"><span class="id"
type="tactic">assert</span></span> <span class="inlinecode">(<span
class="id" type="var">H</span>:<span class="id"
type="var">P</span>).</span> <span class="inlinecode"><span class="id"
type="var">skip</span>.</span>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">demo\_skipH</span> : <span class="id"
type="var">True</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">skip</span> <span class="id"
type="var">H</span>: (<span style="font-family: arial;">∀</span><span
class="id" type="var">n</span> <span class="id" type="var">m</span> :
<span class="id" type="var">nat</span>, (0 + <span class="id"
type="var">n</span>) × <span class="id" type="var">m</span> = <span
class="id" type="var">n</span> × <span class="id" type="var">m</span>).\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="var">skip\_rewrite</span></span> <span class="inlinecode">(<span
class="id" type="var">E1</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">E2</span>)</span>
replaces <span class="inlinecode"><span class="id"
type="var">E1</span></span> with <span class="inlinecode"><span
class="id" type="var">E2</span></span> in the goal, without checking
that <span class="inlinecode"><span class="id"
type="var">E1</span></span> is actually equal to <span
class="inlinecode"><span class="id" type="var">E2</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">mult\_0\_plus</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> : <span class="id"
type="var">nat</span>,\
   (0 + <span class="id" type="var">n</span>) × <span class="id"
type="var">m</span> = <span class="id" type="var">n</span> × <span
class="id" type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">dup</span>.\
\
   <span class="comment">(\* The old proof: \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span>.\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">H</span>: 0 + <span class="id" type="var">n</span> = <span
class="id" type="var">n</span>). <span class="id"
type="var">skip</span>. <span class="id" type="tactic">rewrite</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="tactic">reflexivity</span>.\
\
   <span class="comment">(\* The new proof: \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span>.\
   <span class="id" type="var">skip\_rewrite</span> (0 + <span
class="id" type="var">n</span> = <span class="id" type="var">n</span>).\
   <span class="id" type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Remark: the tactic <span class="inlinecode"><span class="id"
type="var">skip\_rewrite</span></span> can in fact be given a lemma
statement as argument, in the same way as <span class="inlinecode"><span
class="id" type="var">asserts\_rewrite</span></span>.
<div class="paragraph">

</div>

The tactic <span class="inlinecode"><span class="id"
type="var">skip\_goal</span></span> adds the current goal as hypothesis.
This cheat is useful to set up the structure of a proof by induction
without having to worry about the induction hypothesis being applied
only to smaller arguments. Using <span class="inlinecode"><span
class="id" type="var">skip\_goal</span></span>, one can construct a
proof in two steps: first, check that the main arguments go through
without waisting time on fixing the details of the induction hypotheses;
then, focus on fixing the invokations of the induction hypothesis.

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
   <span class="comment">(\* The tactic <span class="inlinecode"><span
class="id"
type="var">skip\_goal</span></span> creates an hypothesis called <span
class="inlinecode"><span class="id" type="var">IH</span></span> \
      asserting that the statment of <span class="inlinecode"><span
class="id"
type="var">ceval\_deterministic</span></span> is true. \*)</span>\
   <span class="id" type="var">skip\_goal</span>.\
   <span class="comment">(\* Of course, if we call <span
class="inlinecode"><span class="id"
type="tactic">assumption</span></span> here, then the goal is solved\
      right away, but the point is to do the proof and use <span
class="inlinecode"><span class="id" type="var">IH</span></span>\

     only at the places where we need an induction hypothesis. \*)</span>\
   <span class="id" type="var">introv</span> <span class="id"
type="var">E1</span> <span class="id" type="var">E2</span>. <span
class="id" type="var">gen</span> <span class="id"
type="var">st2</span>.\
   (<span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>); <span class="id"
type="var">introv</span> <span class="id" type="var">E2</span>; <span
class="id" type="var">inverts</span> <span class="id"
type="var">E2</span> <span class="id" type="keyword">as</span>.\
   <span class="id" type="var">Case</span> "E\_Skip". <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "E\_Ass".\
     <span class="id" type="tactic">subst</span> <span class="id"
type="var">n</span>.\
     <span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "E\_Seq".\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">st3</span> <span class="id" type="var">Red1</span> <span
class="id" type="var">Red2</span>.\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st3</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">EQ1</span>.\
       <span class="id" type="var">SCase</span> "Proof of assertion".\
         <span class="comment">(\* was: <span class="inlinecode"><span
class="id" type="tactic">apply</span></span> <span
class="inlinecode"><span class="id" type="var">IHE1\_1</span>;</span>
<span class="inlinecode"><span class="id"
type="tactic">assumption</span>.</span> \*)</span>\
         <span class="comment">(\* new: \*)</span> <span class="id"
type="tactic">eapply</span> <span class="id" type="var">IH</span>. <span
class="id" type="tactic">eapply</span> <span class="id"
type="var">E1\_1</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">Red1</span>.\
     <span class="id" type="tactic">subst</span> <span class="id"
type="var">st3</span>.\
     <span
class="comment">(\* was: apply IHE1\_2. assumption.] \*)</span>\
     <span class="comment">(\* new: \*)</span> <span class="id"
type="tactic">eapply</span> <span class="id" type="var">IH</span>. <span
class="id" type="tactic">eapply</span> <span class="id"
type="var">E1\_2</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">Red2</span>.\
   <span class="comment">(\* The other cases are similiar. \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">SkipExample</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id" type="var">sort</span></span> {.section}
----------------------------------------------------------------------------------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">SortExamples</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Imp</span>.\
\

</div>

<div class="doc">

The tactic <span class="inlinecode"><span class="id"
type="var">sort</span></span> reorganizes the proof context by placing
all the variables at the top and all the hypotheses at the bottom,
thereby making the proof context more readable.

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
type="var">inverts</span> <span class="id" type="var">E2</span>.\
   <span class="id" type="var">admit</span>. <span class="id"
type="var">admit</span>. <span
class="comment">(\* Skipping some trivial cases \*)</span>\
   <span class="id" type="var">sort</span>. <span
class="comment">(\* Observe how the context is reorganized \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">SortExamples</span>.\
\

</div>

<div class="doc">

Tactics for advanced lemma instantiation {.section}
========================================

<div class="paragraph">

</div>

This last section describes a mechanism for instantiating a lemma by
providing some of its arguments and leaving other implicit. Variables
whose instantiation is not provided are turned into existentential
variables, and facts whose instantiation is not provided are turned into
subgoals.
<div class="paragraph">

</div>

Remark: this instantion mechanism goes far beyond the abilities of the
"Implicit Arguments" mechanism. The point of the instantiation mechanism
described in this section is that you will no longer need to spend time
figuring out how many underscore symbols you need to write.
<div class="paragraph">

</div>

In this section, we'll use a useful feature of Coq for decomposing
conjunctions and existentials. In short, a tactic like <span
class="inlinecode"><span class="id" type="tactic">intros</span></span>
or <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> can be provided with a pattern
<span class="inlinecode">(<span class="id" type="var">H1</span></span>
<span class="inlinecode">&</span> <span class="inlinecode"><span
class="id" type="var">H2</span></span> <span class="inlinecode">&</span>
<span class="inlinecode"><span class="id" type="var">H3</span></span>
<span class="inlinecode">&</span> <span class="inlinecode"><span
class="id" type="var">H4</span></span> <span class="inlinecode">&</span>
<span class="inlinecode"><span class="id" type="var">H5</span>)</span>,
which is a shorthand for <span class="inlinecode">[<span class="id"
type="var">H1</span></span> <span class="inlinecode">[<span class="id"
type="var">H2</span></span> <span class="inlinecode">[<span class="id"
type="var">H3</span></span> <span class="inlinecode">[<span class="id"
type="var">H4</span></span> <span class="inlinecode"><span class="id"
type="var">H5</span>]]]]</span>]. For example, <span
class="inlinecode"><span class="id" type="tactic">destruct</span></span>
<span class="inlinecode">(<span class="id" type="var">H</span></span>
<span class="inlinecode"><span class="id" type="var">\_</span></span>
<span class="inlinecode"><span class="id" type="var">\_</span></span>
<span class="inlinecode"><span class="id" type="var">\_</span></span>
<span class="inlinecode"><span class="id"
type="var">Htypt</span>)</span> <span class="inlinecode"><span
class="id" type="keyword">as</span></span> <span
class="inlinecode">[<span class="id" type="var">T</span></span> <span
class="inlinecode">[<span class="id" type="var">Hctx</span></span> <span
class="inlinecode"><span class="id" type="var">Hsub</span>]].</span> can
be rewritten in the form <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> <span class="inlinecode">(<span
class="id" type="var">H</span></span> <span class="inlinecode"><span
class="id" type="var">\_</span></span> <span class="inlinecode"><span
class="id" type="var">\_</span></span> <span class="inlinecode"><span
class="id" type="var">\_</span></span> <span class="inlinecode"><span
class="id" type="var">Htypt</span>)</span> <span
class="inlinecode"><span class="id" type="keyword">as</span></span>
<span class="inlinecode">(<span class="id" type="var">T</span></span>
<span class="inlinecode">&</span> <span class="inlinecode"><span
class="id" type="var">Hctx</span></span> <span
class="inlinecode">&</span> <span class="inlinecode"><span class="id"
type="var">Hsub</span>).</span>

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Working of <span class="inlinecode"><span class="id" type="var">lets</span></span> {.section}
----------------------------------------------------------------------------------

<div class="paragraph">

</div>

When we have a lemma (or an assumption) that we want to exploit, we
often need to explicitly provide arguments to this lemma, writing
something like: <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> <span class="inlinecode">(<span
class="id" type="var">typing\_inversion\_var</span></span> <span
class="inlinecode"><span class="id" type="var">\_</span></span> <span
class="inlinecode"><span class="id" type="var">\_</span></span> <span
class="inlinecode"><span class="id" type="var">\_</span></span> <span
class="inlinecode"><span class="id" type="var">Htypt</span>)</span>
<span class="inlinecode"><span class="id"
type="keyword">as</span></span> <span class="inlinecode">(<span
class="id" type="var">T</span></span> <span class="inlinecode">&</span>
<span class="inlinecode"><span class="id" type="var">Hctx</span></span>
<span class="inlinecode">&</span> <span class="inlinecode"><span
class="id" type="var">Hsub</span>).</span> The need to write several
times the "underscore" symbol is tedious. Not only we need to figure out
how many of them to write down, but it also makes the proof scripts look
prettly ugly. With the tactic <span class="inlinecode"><span class="id"
type="var">lets</span></span>, one can simply write: <span
class="inlinecode"><span class="id" type="var">lets</span></span> <span
class="inlinecode">(<span class="id" type="var">T</span></span> <span
class="inlinecode">&</span> <span class="inlinecode"><span class="id"
type="var">Hctx</span></span> <span class="inlinecode">&</span> <span
class="inlinecode"><span class="id" type="var">Hsub</span>):</span>
<span class="inlinecode"><span class="id"
type="var">typing\_inversion\_var</span></span> <span
class="inlinecode"><span class="id" type="var">Htypt</span>.</span>
<div class="paragraph">

</div>

In short, this tactic <span class="inlinecode"><span class="id"
type="var">lets</span></span> allows to specialize a lemma on a bunch of
variables and hypotheses. The syntax is <span class="inlinecode"><span
class="id" type="var">lets</span></span> <span class="inlinecode"><span
class="id" type="var">I</span>:</span> <span class="inlinecode"><span
class="id" type="var">E0</span></span> <span class="inlinecode"><span
class="id" type="var">E1</span></span> <span
class="inlinecode">..</span> <span class="inlinecode"><span class="id"
type="var">EN</span></span>, for building an hypothesis named <span
class="inlinecode"><span class="id" type="var">I</span></span> by
applying the fact <span class="inlinecode"><span class="id"
type="var">E0</span></span> to the arguments <span
class="inlinecode"><span class="id" type="var">E1</span></span> to <span
class="inlinecode"><span class="id" type="var">EN</span></span>. Not all
the arguments need to be provided, however the arguments that are
provided need to be provided in the correct order. The tactic relies on
a first-match algorithm based on types in order to figure out how the to
instantiate the lemma with the arguments provided.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">ExamplesLets</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Sub</span>.\
\
 <span class="comment">(\* To illustrate the working of <span
class="inlinecode"><span class="id"
type="var">lets</span></span>, assume that we want to\
    exploit the following lemma. \*)</span>\
\
 <span class="id" type="keyword">Axiom</span> <span class="id"
type="var">typing\_inversion\_var</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">G</span>:<span class="id" type="var">context</span>) (<span
class="id" type="var">x</span>:<span class="id" type="var">id</span>)
(<span class="id" type="var">T</span>:<span class="id"
type="var">ty</span>),\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">G</span> (<span class="id" type="var">tvar</span> <span
class="id" type="var">x</span>) <span class="id" type="var">T</span>
<span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">S</span>, <span class="id" type="var">G</span> <span
class="id" type="var">x</span> = <span class="id" type="var">Some</span>
<span class="id" type="var">S</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">subtype</span> <span class="id" type="var">S</span> <span
class="id" type="var">T</span>.\
\

</div>

<div class="doc">

First, assume we have an assumption <span class="inlinecode"><span
class="id" type="var">H</span></span> with the type of the form <span
class="inlinecode"><span class="id" type="var">has\_type</span></span>
<span class="inlinecode"><span class="id" type="var">G</span></span>
<span class="inlinecode">(<span class="id" type="var">tvar</span></span>
<span class="inlinecode"><span class="id" type="var">x</span>)</span>
<span class="inlinecode"><span class="id" type="var">T</span></span>. We
can obtain the conclusion of the lemma <span class="inlinecode"><span
class="id" type="var">typing\_inversion\_var</span></span> by invoking
the tactics <span class="inlinecode"><span class="id"
type="var">lets</span></span> <span class="inlinecode"><span class="id"
type="var">K</span>:</span> <span class="inlinecode"><span class="id"
type="var">typing\_inversion\_var</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span>, as shown
next.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_lets\_1</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">G</span>:<span class="id" type="var">context</span>) (<span
class="id" type="var">x</span>:<span class="id" type="var">id</span>)
(<span class="id" type="var">T</span>:<span class="id"
type="var">ty</span>),\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">G</span> (<span class="id" type="var">tvar</span> <span
class="id" type="var">x</span>) <span class="id" type="var">T</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">True</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">G</span> <span class="id" type="var">x</span> <span
class="id" type="var">T</span> <span class="id" type="var">H</span>.
<span class="id" type="var">dup</span>.\
\
   <span class="comment">(\* step-by-step: \*)</span>\
   <span class="id" type="var">lets</span> <span class="id"
type="var">K</span>: <span class="id"
type="var">typing\_inversion\_var</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">K</span> <span class="id" type="keyword">as</span> (<span
class="id" type="var">S</span> & <span class="id" type="var">Eq</span> &
<span class="id" type="var">Sub</span>).\
   <span class="id" type="var">admit</span>.\
\
   <span class="comment">(\* all-at-once: \*)</span>\
   <span class="id" type="var">lets</span> (<span class="id"
type="var">S</span> & <span class="id" type="var">Eq</span> & <span
class="id" type="var">Sub</span>): <span class="id"
type="var">typing\_inversion\_var</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="var">admit</span>.\
\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Assume now that we know the values of <span class="inlinecode"><span
class="id" type="var">G</span></span>, <span class="inlinecode"><span
class="id" type="var">x</span></span> and <span class="inlinecode"><span
class="id" type="var">T</span></span> and we want to obtain <span
class="inlinecode"><span class="id" type="var">S</span></span>, and have
<span class="inlinecode"><span class="id"
type="var">has\_type</span></span> <span class="inlinecode"><span
class="id" type="var">G</span></span> <span class="inlinecode">(<span
class="id" type="var">tvar</span></span> <span class="inlinecode"><span
class="id" type="var">x</span>)</span> <span class="inlinecode"><span
class="id" type="var">T</span></span> be produced as a subgoal. To
indicate that we want all the remaining arguments of <span
class="inlinecode"><span class="id"
type="var">typing\_inversion\_var</span></span> to be produced as
subgoals, we use a triple-underscore symbol <span
class="inlinecode"><span class="id" type="var">\_\_\_</span></span>.
(We'll later introduce a shorthand tactic called <span
class="inlinecode"><span class="id" type="var">forwards</span></span> to
avoid writing triple underscores.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_lets\_2</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">G</span>:<span class="id" type="var">context</span>) (<span
class="id" type="var">x</span>:<span class="id" type="var">id</span>)
(<span class="id" type="var">T</span>:<span class="id"
type="var">ty</span>), <span class="id" type="var">True</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">G</span> <span class="id" type="var">x</span> <span
class="id" type="var">T</span>.\
   <span class="id" type="var">lets</span> (<span class="id"
type="var">S</span> & <span class="id" type="var">Eq</span> & <span
class="id" type="var">Sub</span>): <span class="id"
type="var">typing\_inversion\_var</span> <span class="id"
type="var">G</span> <span class="id" type="var">x</span> <span
class="id" type="var">T</span> <span class="id"
type="var">\_\_\_</span>.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

Usually, there is only one context <span class="inlinecode"><span
class="id" type="var">G</span></span> and one type <span
class="inlinecode"><span class="id" type="var">T</span></span> that are
going to be suitable for proving <span class="inlinecode"><span
class="id" type="var">has\_type</span></span> <span
class="inlinecode"><span class="id" type="var">G</span></span> <span
class="inlinecode">(<span class="id" type="var">tvar</span></span> <span
class="inlinecode"><span class="id" type="var">x</span>)</span> <span
class="inlinecode"><span class="id" type="var">T</span></span>, so we
don't really need to bother giving <span class="inlinecode"><span
class="id" type="var">G</span></span> and <span class="inlinecode"><span
class="id" type="var">T</span></span> explicitly. It suffices to call
<span class="inlinecode"><span class="id" type="var">lets</span></span>
<span class="inlinecode">(<span class="id" type="var">S</span></span>
<span class="inlinecode">&</span> <span class="inlinecode"><span
class="id" type="var">Eq</span></span> <span class="inlinecode">&</span>
<span class="inlinecode"><span class="id" type="var">Sub</span>):</span>
<span class="inlinecode"><span class="id"
type="var">typing\_inversion\_var</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span>. The
variables <span class="inlinecode"><span class="id"
type="var">G</span></span> and <span class="inlinecode"><span class="id"
type="var">T</span></span> are then instantiated using existential
variables.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_lets\_3</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span>:<span class="id" type="var">id</span>), <span
class="id" type="var">True</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span>.\
   <span class="id" type="var">lets</span> (<span class="id"
type="var">S</span> & <span class="id" type="var">Eq</span> & <span
class="id" type="var">Sub</span>): <span class="id"
type="var">typing\_inversion\_var</span> <span class="id"
type="var">x</span> <span class="id" type="var">\_\_\_</span>.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

We may go even further by not giving any argument to instantiate <span
class="inlinecode"><span class="id"
type="var">typing\_inversion\_var</span></span>. In this case, three
unification variables are introduced.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_lets\_4</span> : <span class="id"
type="var">True</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">lets</span> (<span class="id"
type="var">S</span> & <span class="id" type="var">Eq</span> & <span
class="id" type="var">Sub</span>): <span class="id"
type="var">typing\_inversion\_var</span> <span class="id"
type="var">\_\_\_</span>.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

Note: if we provide <span class="inlinecode"><span class="id"
type="var">lets</span></span> with only the name of the lemma as
argument, it simply adds this lemma in the proof context, without trying
to instantiate any of its arguments.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_lets\_5</span> : <span class="id"
type="var">True</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">lets</span> <span class="id"
type="var">H</span>: <span class="id"
type="var">typing\_inversion\_var</span>.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

A last useful feature of <span class="inlinecode"><span class="id"
type="var">lets</span></span> is the double-underscore symbol, which
allows skipping an argument when several arguments have the same type.
In the following example, our assumption quantifies over two variables
<span class="inlinecode"><span class="id" type="var">n</span></span> and
<span class="inlinecode"><span class="id" type="var">m</span></span>,
both of type <span class="inlinecode"><span class="id"
type="var">nat</span></span>. We would like <span
class="inlinecode"><span class="id" type="var">m</span></span> to be
instantiated as the value <span class="inlinecode">3</span>, but without
specifying a value for <span class="inlinecode"><span class="id"
type="var">n</span></span>. This can be achieved by writting <span
class="inlinecode"><span class="id" type="var">lets</span></span> <span
class="inlinecode"><span class="id" type="var">K</span>:</span> <span
class="inlinecode"><span class="id" type="var">H</span></span> <span
class="inlinecode"><span class="id" type="var">\_\_</span></span> <span
class="inlinecode">3</span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">demo\_lets\_underscore</span> :\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> <span class="id" type="var">m</span>, <span
class="id" type="var">n</span> ≤ <span class="id" type="var">m</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">n</span> \< <span class="id" type="var">m</span>+1) <span
style="font-family: arial;">→</span> <span class="id"
type="var">True</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">H</span>.\
\
   <span
class="comment">(\* If we do not use a double underscore, the first argument,\
      which is <span class="inlinecode"><span class="id"
type="var">n</span></span>, gets instantiated as 3. \*)</span>\
   <span class="id" type="var">lets</span> <span class="id"
type="var">K</span>: <span class="id" type="var">H</span> 3. <span
class="comment">(\* gives <span class="inlinecode"><span class="id"
type="var">K</span></span> of type <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">m</span>,</span> <span
class="inlinecode">3</span> <span class="inlinecode">≤</span> <span
class="inlinecode"><span class="id" type="var">m</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode">3</span> <span class="inlinecode">\<</span>
<span class="inlinecode"><span class="id"
type="var">m</span>+1</span> \*)</span>\
     <span class="id" type="tactic">clear</span> <span class="id"
type="var">K</span>.\
\
   <span class="comment">(\* The double underscore preceeding <span
class="inlinecode">3</span> indicates that we want \
      to skip a value that has the type <span class="inlinecode"><span
class="id" type="var">nat</span></span> (because <span
class="inlinecode">3</span> has \
      the type <span class="inlinecode"><span class="id"
type="var">nat</span></span>). So, the variable <span
class="inlinecode"><span class="id"
type="var">m</span></span> gets instiated as <span
class="inlinecode">3</span>. \*)</span>\
   <span class="id" type="var">lets</span> <span class="id"
type="var">K</span>: <span class="id" type="var">H</span> <span
class="id" type="var">\_\_</span> 3. <span
class="comment">(\* gives <span class="inlinecode"><span class="id"
type="var">K</span></span> of type <span class="inlinecode">?<span
class="id" type="var">X</span></span> <span class="inlinecode">≤</span>
<span class="inlinecode">3</span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode">?<span class="id" type="var">X</span></span> <span
class="inlinecode">\<</span> <span
class="inlinecode">3+1</span> \*)</span>\
     <span class="id" type="tactic">clear</span> <span class="id"
type="var">K</span>.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

Note: one can write <span class="inlinecode"><span class="id"
type="var">lets</span>:</span> <span class="inlinecode"><span class="id"
type="var">E0</span></span> <span class="inlinecode"><span class="id"
type="var">E1</span></span> <span class="inlinecode"><span class="id"
type="var">E2</span></span> in place of <span class="inlinecode"><span
class="id" type="var">lets</span></span> <span class="inlinecode"><span
class="id" type="var">H</span>:</span> <span class="inlinecode"><span
class="id" type="var">E0</span></span> <span class="inlinecode"><span
class="id" type="var">E1</span></span> <span class="inlinecode"><span
class="id" type="var">E2</span></span>. In this case, the name <span
class="inlinecode"><span class="id" type="var">H</span></span> is chosen
arbitrarily.
<div class="paragraph">

</div>

Note: the tactics <span class="inlinecode"><span class="id"
type="var">lets</span></span> accepts up to five arguments. Another
syntax is available for providing more than five arguments. It consists
in using a list introduced with the special symbol <span
class="inlinecode">\>\></span>, for example <span
class="inlinecode"><span class="id" type="var">lets</span></span> <span
class="inlinecode"><span class="id" type="var">H</span>:</span> <span
class="inlinecode">(\>\></span> <span class="inlinecode"><span
class="id" type="var">E0</span></span> <span class="inlinecode"><span
class="id" type="var">E1</span></span> <span class="inlinecode"><span
class="id" type="var">E2</span></span> <span class="inlinecode"><span
class="id" type="var">E3</span></span> <span class="inlinecode"><span
class="id" type="var">E4</span></span> <span class="inlinecode"><span
class="id" type="var">E5</span></span> <span class="inlinecode"><span
class="id" type="var">E6</span></span> <span class="inlinecode"><span
class="id" type="var">E7</span></span> <span class="inlinecode"><span
class="id" type="var">E8</span></span> <span class="inlinecode"><span
class="id" type="var">E9</span></span> <span
class="inlinecode">10)</span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">ExamplesLets</span>.\
\

</div>

<div class="doc">

Working of <span class="inlinecode"><span class="id" type="var">applys</span></span>, <span class="inlinecode"><span class="id" type="var">forwards</span></span> and <span class="inlinecode"><span class="id" type="var">specializes</span></span> {.section}
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

<div class="paragraph">

</div>

The tactics <span class="inlinecode"><span class="id"
type="var">applys</span></span>, <span class="inlinecode"><span
class="id" type="var">forwards</span></span> and <span
class="inlinecode"><span class="id" type="var">specializes</span></span>
are shorthand that may be used in place of <span
class="inlinecode"><span class="id" type="var">lets</span></span> to
perform specific tasks.
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">forwards</span></span> is a shorthand for instantiating
    all the arguments

of a lemma. More precisely, <span class="inlinecode"><span class="id"
type="var">forwards</span></span> <span class="inlinecode"><span
class="id" type="var">H</span>:</span> <span class="inlinecode"><span
class="id" type="var">E0</span></span> <span class="inlinecode"><span
class="id" type="var">E1</span></span> <span class="inlinecode"><span
class="id" type="var">E2</span></span> <span class="inlinecode"><span
class="id" type="var">E3</span></span> is the same as <span
class="inlinecode"><span class="id" type="var">lets</span></span> <span
class="inlinecode"><span class="id" type="var">H</span>:</span> <span
class="inlinecode"><span class="id" type="var">E0</span></span> <span
class="inlinecode"><span class="id" type="var">E1</span></span> <span
class="inlinecode"><span class="id" type="var">E2</span></span> <span
class="inlinecode"><span class="id" type="var">E3</span></span> <span
class="inlinecode"><span class="id" type="var">\_\_\_</span></span>,
where the triple-underscore has the same meaning as explained earlier
on.
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">applys</span></span> allows building a lemma using the
    advanced instantion

mode of <span class="inlinecode"><span class="id"
type="var">lets</span></span>, and then apply that lemma right away. So,
<span class="inlinecode"><span class="id"
type="var">applys</span></span> <span class="inlinecode"><span
class="id" type="var">E0</span></span> <span class="inlinecode"><span
class="id" type="var">E1</span></span> <span class="inlinecode"><span
class="id" type="var">E2</span></span> <span class="inlinecode"><span
class="id" type="var">E3</span></span> is the same as <span
class="inlinecode"><span class="id" type="var">lets</span></span> <span
class="inlinecode"><span class="id" type="var">H</span>:</span> <span
class="inlinecode"><span class="id" type="var">E0</span></span> <span
class="inlinecode"><span class="id" type="var">E1</span></span> <span
class="inlinecode"><span class="id" type="var">E2</span></span> <span
class="inlinecode"><span class="id" type="var">E3</span></span> followed
with <span class="inlinecode"><span class="id"
type="tactic">eapply</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> and then <span
class="inlinecode"><span class="id" type="tactic">clear</span></span>
<span class="inlinecode"><span class="id" type="var">H</span></span>.
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">specializes</span></span> is a shorthand for
    instantiating in-place

an assumption from the context with particular arguments. More
precisely, <span class="inlinecode"><span class="id"
type="var">specializes</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> <span class="inlinecode"><span
class="id" type="var">E0</span></span> <span class="inlinecode"><span
class="id" type="var">E1</span></span> is the same as <span
class="inlinecode"><span class="id" type="var">lets</span></span> <span
class="inlinecode"><span class="id" type="var">H'</span>:</span> <span
class="inlinecode"><span class="id" type="var">H</span></span> <span
class="inlinecode"><span class="id" type="var">E0</span></span> <span
class="inlinecode"><span class="id" type="var">E1</span></span> followed
with <span class="inlinecode"><span class="id"
type="tactic">clear</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> and <span class="inlinecode"><span
class="id" type="tactic">rename</span></span> <span
class="inlinecode"><span class="id" type="var">H'</span></span> <span
class="inlinecode"><span class="id" type="var">into</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span>.
<div class="paragraph">

</div>

Examples of use of <span class="inlinecode"><span class="id"
type="var">applys</span></span> appear further on. Several examples of
use of <span class="inlinecode"><span class="id"
type="var">forwards</span></span> can be found in the tutorial chapter
<span class="inlinecode"><span class="id"
type="var">UseAuto</span></span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Example of instantiations {.section}
-------------------------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">ExamplesInstantiations</span>.\
   <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Sub</span>.\
\

</div>

<div class="doc">

The following proof shows several examples where <span
class="inlinecode"><span class="id" type="var">lets</span></span> is
used instead of <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span>, as well as examples where <span
class="inlinecode"><span class="id" type="var">applys</span></span> is
used instead of <span class="inlinecode"><span class="id"
type="tactic">apply</span></span>. The proof also contains some holes
that you need to fill in as an exercise.

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
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span> <span
class="id" type="var">v</span> <span class="id" type="var">t</span>
<span class="id" type="var">S</span> <span class="id"
type="var">Htypt</span> <span class="id" type="var">Htypv</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">S</span>.
<span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   (<span class="id" type="var">t\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">t</span>)
<span class="id" type="var">Case</span>); <span class="id"
type="tactic">intros</span>; <span class="id"
type="tactic">simpl</span>.\
   <span class="id" type="var">Case</span> "tvar".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y</span>.\
\
     <span class="comment">(\* An example where <span
class="inlinecode"><span class="id"
type="tactic">destruct</span></span> is replaced with <span
class="inlinecode"><span class="id"
type="var">lets</span></span>. \*)</span>\
     <span
class="comment">(\* old: destruct (typing\_inversion\_var \_ \_ \_ Htypt) as <span
class="inlinecode"><span class="id" type="var">T</span></span> <span
class="inlinecode">[<span class="id" type="var">Hctx</span></span> <span
class="inlinecode"><span class="id"
type="var">Hsub</span>]</span>.\*)</span>\
     <span class="comment">(\* new: \*)</span> <span class="id"
type="var">lets</span> (<span class="id" type="var">T</span>&<span
class="id" type="var">Hctx</span>&<span class="id"
type="var">Hsub</span>): <span class="id"
type="var">typing\_inversion\_var</span> <span class="id"
type="var">Htypt</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hctx</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>)...\
     <span class="id" type="var">SCase</span> "x=y".\
       <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hctx</span>; <span class="id" type="tactic">subst</span>.
<span class="id" type="tactic">clear</span> <span class="id"
type="var">Hctx</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">context\_invariance</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">empty</span>...\
       <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">Hcontra</span>.\
\
        <span class="comment">(\* A more involved example. \*)</span>\
        <span
class="comment">(\* old: destruct (free\_in\_context \_ \_ S empty Hcontra) \
                  as <span class="inlinecode"><span class="id"
type="var">T'</span></span> <span class="inlinecode"><span class="id"
type="var">HT'</span></span>... \*)</span>\
        <span class="comment">(\* new: \*)</span>\
         <span class="id" type="var">lets</span> [<span class="id"
type="var">T'</span> <span class="id" type="var">HT'</span>]: <span
class="id" type="var">free\_in\_context</span> <span class="id"
type="var">S</span> <span class="id" type="var">empty</span> <span
class="id" type="var">Hcontra</span>...\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">HT'</span>.\
   <span class="id" type="var">Case</span> "tapp".\
\
     <span class="comment">(\* Exercise: replace the following <span
class="inlinecode"><span class="id"
type="tactic">destruct</span></span> with a <span
class="inlinecode"><span class="id"
type="var">lets</span></span>. \*)</span>\
     <span
class="comment">(\* old: destruct (typing\_inversion\_app \_ \_ \_ \_ Htypt) \
               as <span class="inlinecode"><span class="id"
type="var">T~1~</span></span> <span class="inlinecode">[<span class="id"
type="var">Htypt1</span></span> <span class="inlinecode"><span
class="id"
type="var">Htypt2</span>]</span>. eapply T\_App... \*)</span>\
     <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
   <span class="id" type="var">Case</span> "tabs".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y</span>. <span class="id"
type="tactic">rename</span> <span class="id" type="var">t</span> <span
class="id" type="var">into</span> <span class="id"
type="var">T~1~</span>.\
\
     <span class="comment">(\* Here is another example of using <span
class="inlinecode"><span class="id"
type="var">lets</span></span>. \*)</span>\
     <span
class="comment">(\* old: destruct (typing\_inversion\_abs \_ \_ \_ \_ \_ Htypt). \*)</span>\
     <span class="comment">(\* new: \*)</span> <span class="id"
type="var">lets</span> (<span class="id" type="var">T~2~</span>&<span
class="id" type="var">Hsub</span>&<span class="id"
type="var">Htypt2</span>): <span class="id"
type="var">typing\_inversion\_abs</span> <span class="id"
type="var">Htypt</span>.\
\
     <span class="comment">(\* An example of where <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
<span class="inlinecode"><span class="id"
type="keyword">with</span></span> can be replaced with <span
class="inlinecode"><span class="id"
type="var">applys</span></span>. \*)</span>\
     <span
class="comment">(\* old: apply T\_Sub with (TArrow T~1~ T~2~)... \*)</span>\
     <span class="comment">(\* new: \*)</span> <span class="id"
type="var">applys</span> <span class="id" type="var">T\_Sub</span>
(<span class="id" type="var">TArrow</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span>)...\
      <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>...\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>).\
     <span class="id" type="var">SCase</span> "x=y".\
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
   <span class="id" type="var">Case</span> "ttrue".\
     <span class="id" type="var">lets</span>: <span class="id"
type="var">typing\_inversion\_true</span> <span class="id"
type="var">Htypt</span>...\
   <span class="id" type="var">Case</span> "tfalse".\
     <span class="id" type="var">lets</span>: <span class="id"
type="var">typing\_inversion\_false</span> <span class="id"
type="var">Htypt</span>...\
   <span class="id" type="var">Case</span> "tif".\
     <span class="id" type="var">lets</span> (<span class="id"
type="var">Htyp1</span>&<span class="id" type="var">Htyp2</span>&<span
class="id" type="var">Htyp3</span>): <span class="id"
type="var">typing\_inversion\_if</span> <span class="id"
type="var">Htypt</span>...\
   <span class="id" type="var">Case</span> "tunit".\
     <span class="comment">(\* An example where <span
class="inlinecode"><span class="id"
type="tactic">assert</span></span> can be replaced with <span
class="inlinecode"><span class="id"
type="var">lets</span></span>. \*)</span>\
     <span class="comment">(\* old: assert (subtype TUnit S) \

             by apply (typing\_inversion\_unit \_ \_ Htypt)... \*)</span>\
     <span class="comment">(\* new: \*)</span> <span class="id"
type="var">lets</span>: <span class="id"
type="var">typing\_inversion\_unit</span> <span class="id"
type="var">Htypt</span>...\
\
\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">ExamplesInstantiations</span>.\
\

</div>

<div class="doc">

Summary {.section}
=======

<div class="paragraph">

</div>

In this chapter we have presented a number of tactics that help make
proof script more concise and more robust on change.
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">introv</span></span> and <span class="inlinecode"><span
    class="id" type="var">inverts</span></span> improve naming and
    inversions.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">false</span></span> and <span class="inlinecode"><span
    class="id" type="var">tryfalse</span></span> help discarding absurd
    goals.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">unfolds</span></span> automatically calls <span
    class="inlinecode"><span class="id"
    type="tactic">unfold</span></span> on the head definition.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">gen</span></span> helps setting up goals for induction.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">cases</span></span> and <span class="inlinecode"><span
    class="id" type="var">cases\_if</span></span> help with case
    analysis.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">splits</span></span>, <span class="inlinecode"><span
    class="id" type="var">branch</span></span> and <span
    class="inlinecode"><span style="font-family: arial;">∃</span></span>
    to deal with n-ary constructs.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">asserts\_rewrite</span></span>, <span
    class="inlinecode"><span class="id"
    type="var">cuts\_rewrite</span></span>, <span
    class="inlinecode"><span class="id" type="var">substs</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">fequals</span></span> help working with equalities.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">lets</span></span>, <span class="inlinecode"><span
    class="id" type="var">forwards</span></span>, <span
    class="inlinecode"><span class="id"
    type="var">specializes</span></span> and <span
    class="inlinecode"><span class="id" type="var">applys</span></span>
    provide means of very conveniently instantiating lemmas.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">applys\_eq</span></span> can save the need to perform
    manual rewriting steps before being able to apply lemma.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">skip</span></span>, <span class="inlinecode"><span
    class="id" type="var">skip\_rewrite</span></span> and <span
    class="inlinecode"><span class="id"
    type="var">skip\_goal</span></span> give the flexibility to choose
    which subgoals to try and discharge first.

Making use of these tactics can boost one's productivity in Coq proofs.
<div class="paragraph">

</div>

If you are interested in using <span class="inlinecode"><span class="id"
type="var">LibTactics.v</span></span> in your own developments, make
sure you get the lastest version from:
http://www.chargueraud.org/softs/tlc/ .
<div class="paragraph">

</div>

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
