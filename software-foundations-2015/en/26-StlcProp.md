<div id="page">

<div id="header">

</div>

<div id="main">

StlcProp<span class="subtitle">Properties of STLC</span> {.libtitle}
========================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">Stlc</span>.\
\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">STLCProp</span>.\
 <span class="id" type="keyword">Import</span> <span class="id"
type="var">STLC</span>.\
\

</div>

<div class="doc">

In this chapter, we develop the fundamental theory of the Simply Typed
Lambda Calculus — in particular, the type safety theorem.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Canonical Forms {.section}
===============

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">canonical\_forms\_bool</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>,\
   <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">TBool</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">t</span> = <span class="id"
type="var">ttrue</span>) <span style="font-family: arial;">∨</span>
(<span class="id" type="var">t</span> = <span class="id"
type="var">tfalse</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">HT</span> <span
class="id" type="var">HVal</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HVal</span>; <span class="id" type="tactic">intros</span>;
<span class="id" type="tactic">subst</span>; <span class="id"
type="tactic">try</span> <span class="id" type="tactic">inversion</span>
<span class="id" type="var">HT</span>; <span class="id"
type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">canonical\_forms\_fun</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>,\
   <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ (<span class="id" type="var">TArrow</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
   <span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">x</span> <span class="id" type="var">u</span>, <span
class="id" type="var">t</span> = <span class="id" type="var">tabs</span>
<span class="id" type="var">x</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">u</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span> <span class="id" type="var">HT</span>
<span class="id" type="var">HVal</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HVal</span>; <span class="id" type="tactic">intros</span>;
<span class="id" type="tactic">subst</span>; <span class="id"
type="tactic">try</span> <span class="id" type="tactic">inversion</span>
<span class="id" type="var">HT</span>; <span class="id"
type="tactic">subst</span>; <span class="id" type="tactic">auto</span>.\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">x0</span>. <span style="font-family: arial;">∃</span><span
class="id" type="var">t0</span>. <span class="id"
type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Progress {.section}
========

<div class="paragraph">

</div>

As before, the *progress* theorem tells us that closed, well-typed terms
are not stuck: either a well-typed term is a value, or it can take an
evaluation step. The proof is a relatively straightforward extension of
the progress proof we saw in the <span class="inlinecode"><span
class="id" type="keyword">Types</span></span> chapter.

</div>

<div class="code code-tight">

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
\

</div>

<div class="doc">

*Proof*: by induction on the derivation of <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">∈</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>.
<div class="paragraph">

</div>

-   The last rule of the derivation cannot be <span
    class="inlinecode"><span class="id" type="var">T\_Var</span></span>,
    since a variable is never well typed in an empty context.
    <div class="paragraph">

    </div>

-   The <span class="inlinecode"><span class="id"
    type="var">T\_True</span></span>, <span class="inlinecode"><span
    class="id" type="var">T\_False</span></span>, and <span
    class="inlinecode"><span class="id" type="var">T\_Abs</span></span>
    cases are trivial, since in each of these cases we know immediately
    that <span class="inlinecode"><span class="id"
    type="var">t</span></span> is a value.
    <div class="paragraph">

    </div>

-   If the last rule of the derivation was <span
    class="inlinecode"><span class="id" type="var">T\_App</span></span>,
    then <span class="inlinecode"><span class="id"
    type="var">t</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span>, and we know that <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> are also well typed in the empty
    context; in particular, there exists a type <span
    class="inlinecode"><span class="id" type="var">T~2~</span></span>
    such that <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T~2~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">→</span></span>
    <span class="inlinecode"><span class="id" type="var">T</span></span>
    and <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span>
    <span class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T~2~</span></span>. By the induction
    hypothesis, either <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> is a value or it can take an
    evaluation step.
    <div class="paragraph">

    </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> is a value, we now consider <span
        class="inlinecode"><span class="id"
        type="var">t~2~</span></span>, which by the other induction
        hypothesis must also either be a value or take an evaluation
        step.
        <div class="paragraph">

        </div>

        -   Suppose <span class="inlinecode"><span class="id"
            type="var">t~2~</span></span> is a value. Since <span
            class="inlinecode"><span class="id"
            type="var">t~1~</span></span> is a value with an arrow type,
            it must be a lambda abstraction; hence <span
            class="inlinecode"><span class="id"
            type="var">t~1~</span></span> <span class="inlinecode"><span
            class="id" type="var">t~2~</span></span> can take a step by
            <span class="inlinecode"><span class="id"
            type="var">ST\_AppAbs</span></span>.
            <div class="paragraph">

            </div>

        -   Otherwise, <span class="inlinecode"><span class="id"
            type="var">t~2~</span></span> can take a step, and hence so
            can <span class="inlinecode"><span class="id"
            type="var">t~1~</span></span> <span class="inlinecode"><span
            class="id" type="var">t~2~</span></span> by <span
            class="inlinecode"><span class="id"
            type="var">ST\_App2</span></span>.
            <div class="paragraph">

            </div>
    -   If <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> can take a step, then so can <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span> by <span
        class="inlinecode"><span class="id"
        type="var">ST\_App1</span></span>.
        <div class="paragraph">

        </div>
-   If the last rule of the derivation was <span
    class="inlinecode"><span class="id" type="var">T\_If</span></span>,
    then <span class="inlinecode"><span class="id"
    type="var">t</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="keyword">if</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="keyword">then</span></span> <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span>
    <span class="inlinecode"><span class="id"
    type="keyword">else</span></span> <span class="inlinecode"><span
    class="id" type="var">t~3~</span></span>, where <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    has type <span class="inlinecode"><span class="id"
    type="var">Bool</span></span>. By the IH, <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    either is a value or takes a step.
    <div class="paragraph">

    </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> is a value, then since it has type
        <span class="inlinecode"><span class="id"
        type="var">Bool</span></span> it must be either <span
        class="inlinecode"><span class="id"
        type="var">true</span></span> or <span class="inlinecode"><span
        class="id" type="var">false</span></span>. If it is <span
        class="inlinecode"><span class="id"
        type="var">true</span></span>, then <span
        class="inlinecode"><span class="id" type="var">t</span></span>
        steps to <span class="inlinecode"><span class="id"
        type="var">t~2~</span></span>; otherwise it steps to <span
        class="inlinecode"><span class="id"
        type="var">t~3~</span></span>.
        <div class="paragraph">

        </div>

    -   Otherwise, <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> takes a step, and therefore so
        does <span class="inlinecode"><span class="id"
        type="var">t</span></span> (by <span class="inlinecode"><span
        class="id" type="var">ST\_If</span></span>).

</div>

<div class="code code-tight">

\
<div id="proofcontrol1" class="togglescript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')">

<span class="show"></span>

</div>

<div id="proof1" class="proofscript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
class="id" type="var">Ht</span>.\
   <span class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Ht</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">subst</span> <span
style="font-family: serif; font-size:85%;">Γ</span>...\
   <span class="id" type="var">Case</span> "T\_Var".\
     <span
class="comment">(\* contradictory: variables cannot be typed in an \
        empty context \*)</span>\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>.\
\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="comment">(\* <span class="inlinecode"><span class="id"
type="var">t</span></span> = <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> <span class="inlinecode"><span class="id"
type="var">t~2~</span></span>.  Proceed by cases on whether <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> is a \
        value or steps... \*)</span>\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span>...\
       <span class="id" type="var">SSCase</span> "t~2~ is also a
value".\
         <span class="id" type="tactic">assert</span> (<span
style="font-family: arial;">∃</span><span class="id"
type="var">x0</span> <span class="id" type="var">t0</span>, <span
class="id" type="var">t~1~</span> = <span class="id"
type="var">tabs</span> <span class="id" type="var">x0</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">t0</span>).\
         <span class="id" type="tactic">eapply</span> <span class="id"
type="var">canonical\_forms\_fun</span>; <span class="id"
type="tactic">eauto</span>.\
         <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H1</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">x0</span> [<span class="id" type="var">t0</span>
<span class="id" type="var">Heq</span>]]. <span class="id"
type="tactic">subst</span>.\
         <span style="font-family: arial;">∃</span>([<span class="id"
type="var">x0</span>:=<span class="id" type="var">t~2~</span>]<span
class="id" type="var">t0</span>)...\
\
       <span class="id" type="var">SSCase</span> "t~2~ steps".\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">H0</span> <span class="id"
type="keyword">as</span> [<span class="id" type="var">t~2~'</span> <span
class="id" type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~'</span>)...\
\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)...\
\
   <span class="id" type="var">Case</span> "T\_If".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>...\
\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">canonical\_forms\_bool</span> <span class="id"
type="var">t~1~</span>); <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">eauto</span>.\
\
     <span class="id" type="var">SCase</span> "t~1~ also steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tif</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>)...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 3 stars, optional (progress\_from\_term\_ind) {.section}

Show that progress can also be proved by induction on terms instead of
induction on typing derivations.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">progress'</span> : <span
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
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span>.\
   <span class="id" type="var">t\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">t</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">T</span> <span
class="id" type="var">Ht</span>; <span class="id"
type="tactic">auto</span>.\
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

Preservation {.section}
============

<div class="paragraph">

</div>

The other half of the type soundness property is the preservation of
types during reduction. For this, we need to develop some technical
machinery for reasoning about variables and substitution. Working from
top to bottom (the high-level property we are actually interested in to
the lowest-level technical lemmas that are needed by various cases of
the more interesting proofs), the story goes like this:
<div class="paragraph">

</div>

-   The *preservation theorem* is proved by induction on a typing
    derivation, pretty much as we did in the <span
    class="inlinecode"><span class="id"
    type="keyword">Types</span></span> chapter. The one case that is
    significantly different is the one for the <span
    class="inlinecode"><span class="id"
    type="var">ST\_AppAbs</span></span> rule, which is defined using the
    substitution operation. To see that this step preserves typing, we
    need to know that the substitution itself does. So we prove a...
    <div class="paragraph">

    </div>

-   *substitution lemma*, stating that substituting a (closed) term
    <span class="inlinecode"><span class="id" type="var">s</span></span>
    for a variable <span class="inlinecode"><span class="id"
    type="var">x</span></span> in a term <span class="inlinecode"><span
    class="id" type="var">t</span></span> preserves the type of <span
    class="inlinecode"><span class="id" type="var">t</span></span>. The
    proof goes by induction on the form of <span
    class="inlinecode"><span class="id" type="var">t</span></span> and
    requires looking at all the different cases in the definition of
    substitition. This time, the tricky cases are the ones for variables
    and for function abstractions. In both cases, we discover that we
    need to take a term <span class="inlinecode"><span class="id"
    type="var">s</span></span> that has been shown to be well-typed in
    some context <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> and
    consider the same term <span class="inlinecode"><span class="id"
    type="var">s</span></span> in a slightly different context <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span>. For
    this we prove a...
    <div class="paragraph">

    </div>

-   *context invariance* lemma, showing that typing is preserved under
    "inessential changes" to the context <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> — in
    particular, changes that do not affect any of the free variables of
    the term. For this, we need a careful definition of
    <div class="paragraph">

    </div>

-   the *free variables* of a term — i.e., the variables occuring in the
    term that are not in the scope of a function abstraction that binds
    them.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Free Occurrences {.section}
----------------

<div class="paragraph">

</div>

A variable <span class="inlinecode"><span class="id"
type="var">x</span></span> *appears free in* a term *t* if <span
class="inlinecode"><span class="id" type="var">t</span></span> contains
some occurrence of <span class="inlinecode"><span class="id"
type="var">x</span></span> that is not under an abstraction labeled
<span class="inlinecode"><span class="id" type="var">x</span></span>.
For example:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">y</span></span>
    appears free, but <span class="inlinecode"><span class="id"
    type="var">x</span></span> does not, in <span
    class="inlinecode">\\<span class="id" type="var">x</span>:<span
    class="id" type="var">T</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">U</span>.</span> <span class="inlinecode"><span
    class="id" type="var">x</span></span> <span class="inlinecode"><span
    class="id" type="var">y</span></span>
-   both <span class="inlinecode"><span class="id"
    type="var">x</span></span> and <span class="inlinecode"><span
    class="id" type="var">y</span></span> appear free in <span
    class="inlinecode">(\\<span class="id" type="var">x</span>:<span
    class="id" type="var">T</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">U</span>.</span> <span class="inlinecode"><span
    class="id" type="var">x</span></span> <span class="inlinecode"><span
    class="id" type="var">y</span>)</span> <span
    class="inlinecode"><span class="id" type="var">x</span></span>
-   no variables appear free in <span class="inlinecode">\\<span
    class="id" type="var">x</span>:<span class="id"
    type="var">T</span><span style="font-family: arial;">→</span><span
    class="id" type="var">U</span>.</span> <span
    class="inlinecode">\\<span class="id" type="var">y</span>:<span
    class="id" type="var">T</span>.</span> <span
    class="inlinecode"><span class="id" type="var">x</span></span> <span
    class="inlinecode"><span class="id" type="var">y</span></span>

</div>

<div class="code code-tight">

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
   | <span class="id" type="var">afi\_if1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>)\
   | <span class="id" type="var">afi\_if2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>)\
   | <span class="id" type="var">afi\_if3</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~3~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>).\
<div id="proofcontrol2" class="togglescript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')">

<span class="show"></span>

</div>

<div id="proof2" class="proofscript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')"
style="display: none;">

\
 <span class="id" type="keyword">Tactic Notation</span> "afi\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "afi\_var"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "afi\_app1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"afi\_app2"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "afi\_abs"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "afi\_if1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"afi\_if2"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "afi\_if3" ].\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">appears\_free\_in</span>.\

</div>

\

</div>

<div class="doc">

A term in which no variables appear free is said to be *closed*.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">closed</span> (<span class="id" type="var">t</span>:<span
class="id" type="var">tm</span>) :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, ¬ <span class="id"
type="var">appears\_free\_in</span> <span class="id" type="var">x</span>
<span class="id" type="var">t</span>.\
\

</div>

<div class="doc">

Substitution {.section}
------------

<div class="paragraph">

</div>

We first need a technical lemma connecting free variables and typing
contexts. If a variable <span class="inlinecode"><span class="id"
type="var">x</span></span> appears free in a term <span
class="inlinecode"><span class="id" type="var">t</span></span>, and if
we know <span class="inlinecode"><span class="id"
type="var">t</span></span> is well typed in context <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span>, then it must
be the case that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> assigns a
type to <span class="inlinecode"><span class="id"
type="var">x</span></span>.

</div>

<div class="code code-tight">

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
\

</div>

<div class="doc">

*Proof*: We show, by induction on the proof that <span
class="inlinecode"><span class="id" type="var">x</span></span> appears
free in <span class="inlinecode"><span class="id"
type="var">t</span></span>, that, for all contexts <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span>, if <span
class="inlinecode"><span class="id" type="var">t</span></span> is well
typed under <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span>, then <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> assigns some
type to <span class="inlinecode"><span class="id"
type="var">x</span></span>.
<div class="paragraph">

</div>

-   If the last rule used was <span class="inlinecode"><span class="id"
    type="var">afi\_var</span></span>, then <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">x</span></span>, and from the assumption that
    <span class="inlinecode"><span class="id" type="var">t</span></span>
    is well typed under <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> we have
    immediately that <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> assigns a
    type to <span class="inlinecode"><span class="id"
    type="var">x</span></span>.
    <div class="paragraph">

    </div>

-   If the last rule used was <span class="inlinecode"><span class="id"
    type="var">afi\_app1</span></span>, then <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">t~1~</span></span> <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">x</span></span> appears free in <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>.
    Since <span class="inlinecode"><span class="id"
    type="var">t</span></span> is well typed under <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span>, we can
    see from the typing rules that <span class="inlinecode"><span
    class="id" type="var">t~1~</span></span> must also be, and the IH
    then tells us that <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> assigns
    <span class="inlinecode"><span class="id" type="var">x</span></span>
    a type.
    <div class="paragraph">

    </div>

-   Almost all the other cases are similar: <span
    class="inlinecode"><span class="id" type="var">x</span></span>
    appears free in a subterm of <span class="inlinecode"><span
    class="id" type="var">t</span></span>, and since <span
    class="inlinecode"><span class="id" type="var">t</span></span> is
    well typed under <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span>, we know
    the subterm of <span class="inlinecode"><span class="id"
    type="var">t</span></span> in which <span class="inlinecode"><span
    class="id" type="var">x</span></span> appears is well typed under
    <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> as well,
    and the IH gives us exactly the conclusion we want.
    <div class="paragraph">

    </div>

-   The only remaining case is <span class="inlinecode"><span class="id"
    type="var">afi\_abs</span></span>. In this case <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode">\\<span
    class="id" type="var">y</span>:<span class="id"
    type="var">T~11~.t~12~</span></span>, and <span
    class="inlinecode"><span class="id" type="var">x</span></span>
    appears free in <span class="inlinecode"><span class="id"
    type="var">t~12~</span></span>; we also know that <span
    class="inlinecode"><span class="id" type="var">x</span></span> is
    different from <span class="inlinecode"><span class="id"
    type="var">y</span></span>. The difference from the previous cases
    is that whereas <span class="inlinecode"><span class="id"
    type="var">t</span></span> is well typed under <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span>, its body
    <span class="inlinecode"><span class="id"
    type="var">t~12~</span></span> is well typed under <span
    class="inlinecode">(<span
    style="font-family: serif; font-size:85%;">Γ</span>,</span> <span
    class="inlinecode"><span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span>)</span>, so the IH allows us to
    conclude that <span class="inlinecode"><span class="id"
    type="var">x</span></span> is assigned some type by the extended
    context <span class="inlinecode">(<span
    style="font-family: serif; font-size:85%;">Γ</span>,</span> <span
    class="inlinecode"><span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span>)</span>. To conclude that <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> assigns a
    type to <span class="inlinecode"><span class="id"
    type="var">x</span></span>, we appeal to lemma <span
    class="inlinecode"><span class="id"
    type="var">extend\_neq</span></span>, noting that <span
    class="inlinecode"><span class="id" type="var">x</span></span> and
    <span class="inlinecode"><span class="id" type="var">y</span></span>
    are different variables.

</div>

<div class="code code-tight">

\
<div id="proofcontrol3" class="togglescript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')">

<span class="show"></span>

</div>

<div id="proof3" class="proofscript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">H</span> <span class="id" type="var">H0</span>. <span
class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">T</span>.\
   <span class="id" type="var">afi\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>)
<span class="id" type="var">Case</span>;\
          <span class="id" type="tactic">intros</span>; <span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> [<span
class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span>; <span class="id" type="tactic">eauto</span>].\
   <span class="id" type="var">Case</span> "afi\_abs".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H1</span>; <span class="id" type="tactic">subst</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHappears\_free\_in</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H7</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">extend\_neq</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H7</span>; <span class="id"
type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Next, we'll need the fact that any term <span class="inlinecode"><span
class="id" type="var">t</span></span> which is well typed in the empty
context is closed — that is, it has no free variables.
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (typable\_empty\_\_closed) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Corollary</span> <span class="id"
type="var">typable\_empty\_\_closed</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">T</span>,\
     <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">closed</span> <span class="id"
type="var">t</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Sometimes, when we have a proof <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>, we will need to replace <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> by a
different context <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ'</span></span>. When is it
safe to do this? Intuitively, it must at least be the case that <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ'</span></span> assigns the
same types as <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> to all the
variables that appear free in <span class="inlinecode"><span class="id"
type="var">t</span></span>. In fact, this is the only condition that is
needed.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">context\_invariance</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: serif; font-size:85%;">Γ'</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span>,\
      <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
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
type="var">t</span> ∈ <span class="id" type="var">T</span>.\
\

</div>

<div class="doc">

*Proof*: By induction on the derivation of <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">∈</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>.
<div class="paragraph">

</div>

-   If the last rule in the derivation was <span
    class="inlinecode"><span class="id" type="var">T\_Var</span></span>,
    then <span class="inlinecode"><span class="id"
    type="var">t</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">x</span></span> and
    <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> <span
    class="inlinecode"><span class="id" type="var">x</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span>. By assumption, <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span> <span
    class="inlinecode"><span class="id" type="var">x</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span> as well, and hence <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id" type="var">t</span></span>
    <span class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span> by <span
    class="inlinecode"><span class="id" type="var">T\_Var</span></span>.
    <div class="paragraph">

    </div>

-   If the last rule was <span class="inlinecode"><span class="id"
    type="var">T\_Abs</span></span>, then <span class="inlinecode"><span
    class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode">\\<span
    class="id" type="var">y</span>:<span class="id"
    type="var">T~11~</span>.</span> <span class="inlinecode"><span
    class="id" type="var">t~12~</span></span>, with <span
    class="inlinecode"><span class="id" type="var">T</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">T~11~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">→</span></span>
    <span class="inlinecode"><span class="id"
    type="var">T~12~</span></span> and <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span>,</span> <span
    class="inlinecode"><span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~12~</span></span> <span class="inlinecode">∈</span>
    <span class="inlinecode"><span class="id"
    type="var">T~12~</span></span>. The induction hypothesis is that for
    any context <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ''</span></span>, if
    <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span>,</span> <span
    class="inlinecode"><span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span></span> and <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ''</span></span> assign
    the same types to all the free variables in <span
    class="inlinecode"><span class="id" type="var">t~12~</span></span>,
    then <span class="inlinecode"><span class="id"
    type="var">t~12~</span></span> has type <span
    class="inlinecode"><span class="id" type="var">T~12~</span></span>
    under <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ''</span></span>. Let
    <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span> be a
    context which agrees with <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> on the
    free variables in <span class="inlinecode"><span class="id"
    type="var">t</span></span>; we must show <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode">\\<span class="id"
    type="var">y</span>:<span class="id" type="var">T~11~</span>.</span>
    <span class="inlinecode"><span class="id"
    type="var">t~12~</span></span> <span class="inlinecode">∈</span>
    <span class="inlinecode"><span class="id"
    type="var">T~11~</span></span> <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">T~12~</span></span>.
    <div class="paragraph">

    </div>

    By <span class="inlinecode"><span class="id"
    type="var">T\_Abs</span></span>, it suffices to show that <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span>,</span> <span
    class="inlinecode"><span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~12~</span></span> <span class="inlinecode">∈</span>
    <span class="inlinecode"><span class="id"
    type="var">T~12~</span></span>. By the IH (setting <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ''</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span>,</span> <span
    class="inlinecode"><span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span></span>), it suffices to show that
    <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span>,</span> <span
    class="inlinecode"><span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span></span> and <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span>,</span> <span
    class="inlinecode"><span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span></span> agree on all the variables
    that appear free in <span class="inlinecode"><span class="id"
    type="var">t~12~</span></span>.
    <div class="paragraph">

    </div>

    Any variable occurring free in <span class="inlinecode"><span
    class="id" type="var">t~12~</span></span> must either be <span
    class="inlinecode"><span class="id" type="var">y</span></span>, or
    some other variable. <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span>,</span> <span
    class="inlinecode"><span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span></span> and <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span>,</span> <span
    class="inlinecode"><span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span></span> clearly agree on <span
    class="inlinecode"><span class="id" type="var">y</span></span>.
    Otherwise, we note that any variable other than <span
    class="inlinecode"><span class="id" type="var">y</span></span> which
    occurs free in <span class="inlinecode"><span class="id"
    type="var">t~12~</span></span> also occurs free in <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode">\\<span
    class="id" type="var">y</span>:<span class="id"
    type="var">T~11~</span>.</span> <span class="inlinecode"><span
    class="id" type="var">t~12~</span></span>, and by assumption <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> and <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span> agree on
    all such variables, and hence so do <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span>,</span> <span
    class="inlinecode"><span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span></span> and <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span>,</span> <span
    class="inlinecode"><span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span></span>.
    <div class="paragraph">

    </div>

-   If the last rule was <span class="inlinecode"><span class="id"
    type="var">T\_App</span></span>, then <span class="inlinecode"><span
    class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">t~1~</span></span> <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span>,
    with <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode">∈</span>
    <span class="inlinecode"><span class="id"
    type="var">T~2~</span></span> <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">T</span></span> and
    <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> <span class="inlinecode">∈</span>
    <span class="inlinecode"><span class="id"
    type="var">T~2~</span></span>. One induction hypothesis states that
    for all contexts <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span>, if
    <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span> agrees
    with <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> on the
    free variables in <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span>, then <span class="inlinecode"><span
    class="id" type="var">t~1~</span></span> has type <span
    class="inlinecode"><span class="id" type="var">T~2~</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">T</span></span> under
    <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span>; there
    is a similar IH for <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span>. We must show that <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> also has type <span
    class="inlinecode"><span class="id" type="var">T</span></span> under
    <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span>, given
    the assumption that <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span> agrees
    with <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> on all
    the free variables in <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span>. By <span
    class="inlinecode"><span class="id" type="var">T\_App</span></span>,
    it suffices to show that <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> and <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> each have the same type
    under <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span> as under
    <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span>. However,
    we note that all free variables in <span class="inlinecode"><span
    class="id" type="var">t~1~</span></span> are also free in <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span>, and similarly for free variables in
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span>; hence the desired result follows by
    the two IHs.

</div>

<div class="code code-tight">

\
<div id="proofcontrol4" class="togglescript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')">

<span class="show"></span>

</div>

<div id="proof4" class="proofscript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ'</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span>; <span class="id"
type="tactic">auto</span>.\
   <span class="id" type="var">Case</span> "T\_Var".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Var</span>. <span class="id" type="tactic">rewrite</span>
<span style="font-family: arial;">←</span> <span class="id"
type="var">H0</span>...\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHhas\_type</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">x1</span> <span
class="id" type="var">Hafi</span>.\
     <span class="comment">(\* the only tricky step... the <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ'</span></span> we use to \
        instantiate is <span class="inlinecode"><span class="id"
type="var">extend</span></span> <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id"
type="var">T~11~</span></span> \*)</span>\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>. <span class="id" type="tactic">destruct</span>
(<span class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x0</span> <span class="id" type="var">x1</span>)...\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_App</span> <span class="id" type="keyword">with</span>
<span class="id" type="var">T~11~</span>...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Now we come to the conceptual heart of the proof that reduction
preserves types — namely, the observation that *substitution* preserves
types.
<div class="paragraph">

</div>

Formally, the so-called *Substitution Lemma* says this: suppose we have
a term <span class="inlinecode"><span class="id"
type="var">t</span></span> with a free variable <span
class="inlinecode"><span class="id" type="var">x</span></span>, and
suppose we've been able to assign a type <span class="inlinecode"><span
class="id" type="var">T</span></span> to <span class="inlinecode"><span
class="id" type="var">t</span></span> under the assumption that <span
class="inlinecode"><span class="id" type="var">x</span></span> has some
type <span class="inlinecode"><span class="id"
type="var">U</span></span>. Also, suppose that we have some other term
<span class="inlinecode"><span class="id" type="var">v</span></span> and
that we've shown that <span class="inlinecode"><span class="id"
type="var">v</span></span> has type <span class="inlinecode"><span
class="id" type="var">U</span></span>. Then, since <span
class="inlinecode"><span class="id" type="var">v</span></span> satisfies
the assumption we made about <span class="inlinecode"><span class="id"
type="var">x</span></span> when typing <span class="inlinecode"><span
class="id" type="var">t</span></span>, we should be able to substitute
<span class="inlinecode"><span class="id" type="var">v</span></span> for
each of the occurrences of <span class="inlinecode"><span class="id"
type="var">x</span></span> in <span class="inlinecode"><span class="id"
type="var">t</span></span> and obtain a new term that still has type
<span class="inlinecode"><span class="id" type="var">T</span></span>.
<div class="paragraph">

</div>

*Lemma*: If <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">∈</span> <span class="inlinecode"><span
class="id" type="var">T</span></span> and <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">v</span></span> <span
class="inlinecode">∈</span> <span class="inlinecode"><span class="id"
type="var">U</span></span>, then <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t</span></span> <span class="inlinecode">∈</span> <span
class="inlinecode"><span class="id" type="var">T</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">substitution\_preserves\_typing</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span> <span
class="id" type="var">t</span> <span class="id" type="var">v</span>
<span class="id" type="var">T</span>,\
      <span class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">v</span> ∈ <span class="id" type="var">U</span> <span
style="font-family: arial;">→</span>\
      <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> [<span class="id"
type="var">x</span>:=<span class="id" type="var">v</span>]<span
class="id" type="var">t</span> ∈ <span class="id" type="var">T</span>.\
\

</div>

<div class="doc">

One technical subtlety in the statement of the lemma is that we assign
<span class="inlinecode"><span class="id" type="var">v</span></span> the
type <span class="inlinecode"><span class="id"
type="var">U</span></span> in the *empty* context — in other words, we
assume <span class="inlinecode"><span class="id"
type="var">v</span></span> is closed. This assumption considerably
simplifies the <span class="inlinecode"><span class="id"
type="var">T\_Abs</span></span> case of the proof (compared to assuming
<span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">v</span></span>
<span class="inlinecode">∈</span> <span class="inlinecode"><span
class="id" type="var">U</span></span>, which would be the other
reasonable assumption at this point) because the context invariance
lemma then tells us that <span class="inlinecode"><span class="id"
type="var">v</span></span> has type <span class="inlinecode"><span
class="id" type="var">U</span></span> in any context at all — we don't
have to worry about free variables in <span class="inlinecode"><span
class="id" type="var">v</span></span> clashing with the variable being
introduced into the context by <span class="inlinecode"><span class="id"
type="var">T\_Abs</span></span>.
<div class="paragraph">

</div>

*Proof*: We prove, by induction on <span class="inlinecode"><span
class="id" type="var">t</span></span>, that, for all <span
class="inlinecode"><span class="id" type="var">T</span></span> and <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span>, if <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">∈</span> <span class="inlinecode"><span
class="id" type="var">T</span></span> and <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">v</span></span> <span
class="inlinecode">∈</span> <span class="inlinecode"><span class="id"
type="var">U</span></span>, then <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t</span></span> <span class="inlinecode">∈</span> <span
class="inlinecode"><span class="id" type="var">T</span></span>.
<div class="paragraph">

</div>

-   If <span class="inlinecode"><span class="id"
    type="var">t</span></span> is a variable, there are two cases to
    consider, depending on whether <span class="inlinecode"><span
    class="id" type="var">t</span></span> is <span
    class="inlinecode"><span class="id" type="var">x</span></span> or
    some other variable.
    <div class="paragraph">

    </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t</span></span> <span class="inlinecode">=</span>
        <span class="inlinecode"><span class="id"
        type="var">x</span></span>, then from the fact that <span
        class="inlinecode"><span
        style="font-family: serif; font-size:85%;">Γ</span>,</span>
        <span class="inlinecode"><span class="id"
        type="var">x</span>:<span class="id" type="var">U</span></span>
        <span class="inlinecode"><span
        style="font-family: arial;">⊢</span></span> <span
        class="inlinecode"><span class="id" type="var">x</span></span>
        <span class="inlinecode">∈</span> <span class="inlinecode"><span
        class="id" type="var">T</span></span> we conclude that <span
        class="inlinecode"><span class="id" type="var">U</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">T</span></span>. We must show that <span
        class="inlinecode">[<span class="id" type="var">x</span>:=<span
        class="id" type="var">v</span>]<span class="id"
        type="var">x</span></span> <span class="inlinecode">=</span>
        <span class="inlinecode"><span class="id"
        type="var">v</span></span> has type <span
        class="inlinecode"><span class="id" type="var">T</span></span>
        under <span class="inlinecode"><span
        style="font-family: serif; font-size:85%;">Γ</span></span>,
        given the assumption that <span class="inlinecode"><span
        class="id" type="var">v</span></span> has type <span
        class="inlinecode"><span class="id" type="var">U</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">T</span></span> under the empty context.
        This follows from context invariance: if a closed term has type
        <span class="inlinecode"><span class="id"
        type="var">T</span></span> in the empty context, it has that
        type in any context.
        <div class="paragraph">

        </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t</span></span> is some variable <span
        class="inlinecode"><span class="id" type="var">y</span></span>
        that is not equal to <span class="inlinecode"><span class="id"
        type="var">x</span></span>, then we need only note that <span
        class="inlinecode"><span class="id" type="var">y</span></span>
        has the same type under <span class="inlinecode"><span
        style="font-family: serif; font-size:85%;">Γ</span>,</span>
        <span class="inlinecode"><span class="id"
        type="var">x</span>:<span class="id" type="var">U</span></span>
        as under <span class="inlinecode"><span
        style="font-family: serif; font-size:85%;">Γ</span></span>.
        <div class="paragraph">

        </div>
-   If <span class="inlinecode"><span class="id"
    type="var">t</span></span> is an abstraction <span
    class="inlinecode">\\<span class="id" type="var">y</span>:<span
    class="id" type="var">T~11~</span>.</span> <span
    class="inlinecode"><span class="id" type="var">t~12~</span></span>,
    then the IH tells us, for all <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span> and
    <span class="inlinecode"><span class="id"
    type="var">T'</span></span>, that if <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span>,<span
    class="id" type="var">x</span>:<span class="id"
    type="var">U</span></span> <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~12~</span></span>
    <span class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T'</span></span> and <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id" type="var">v</span></span>
    <span class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">U</span></span>, then <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ'</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode">[<span class="id"
    type="var">x</span>:=<span class="id" type="var">v</span>]<span
    class="id" type="var">t~12~</span></span> <span
    class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T'</span></span>.
    <div class="paragraph">

    </div>

    The substitution in the conclusion behaves differently, depending on
    whether <span class="inlinecode"><span class="id"
    type="var">x</span></span> and <span class="inlinecode"><span
    class="id" type="var">y</span></span> are the same variable name.
    <div class="paragraph">

    </div>

    First, suppose <span class="inlinecode"><span class="id"
    type="var">x</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">y</span></span>.
    Then, by the definition of substitution, <span
    class="inlinecode">[<span class="id" type="var">x</span>:=<span
    class="id" type="var">v</span>]<span class="id"
    type="var">t</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">t</span></span>, so
    we just need to show <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id" type="var">t</span></span>
    <span class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span>. But we know <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
    type="var">x</span>:<span class="id" type="var">U</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span>, and since the variable <span
    class="inlinecode"><span class="id" type="var">y</span></span> does
    not appear free in <span class="inlinecode">\\<span class="id"
    type="var">y</span>:<span class="id" type="var">T~11~</span>.</span>
    <span class="inlinecode"><span class="id"
    type="var">t~12~</span></span>, the context invariance lemma yields
    <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id" type="var">t</span></span>
    <span class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span>.
    <div class="paragraph">

    </div>

    Second, suppose <span class="inlinecode"><span class="id"
    type="var">x</span></span> <span class="inlinecode">≠</span> <span
    class="inlinecode"><span class="id" type="var">y</span></span>. We
    know <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
    type="var">x</span>:<span class="id" type="var">U</span>,<span
    class="id" type="var">y</span>:<span class="id"
    type="var">T~11~</span></span> <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~12~</span></span>
    <span class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T~12~</span></span> by inversion of the typing
    relation, and <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
    type="var">y</span>:<span class="id" type="var">T~11~</span>,<span
    class="id" type="var">x</span>:<span class="id"
    type="var">U</span></span> <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~12~</span></span>
    <span class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T~12~</span></span> follows from this by the
    context invariance lemma, so the IH applies, giving us <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
    type="var">y</span>:<span class="id" type="var">T~11~</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode">[<span class="id" type="var">x</span>:=<span
    class="id" type="var">v</span>]<span class="id"
    type="var">t~12~</span></span> <span class="inlinecode">∈</span>
    <span class="inlinecode"><span class="id"
    type="var">T~12~</span></span>. By <span class="inlinecode"><span
    class="id" type="var">T\_Abs</span></span>, <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode">\\<span class="id"
    type="var">y</span>:<span class="id" type="var">T~11~</span>.</span>
    <span class="inlinecode">[<span class="id"
    type="var">x</span>:=<span class="id" type="var">v</span>]<span
    class="id" type="var">t~12~</span></span> <span
    class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T~11~</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">T~12~</span></span>, and by the definition of
    substitution (noting that <span class="inlinecode"><span class="id"
    type="var">x</span></span> <span class="inlinecode">≠</span> <span
    class="inlinecode"><span class="id" type="var">y</span></span>),
    <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode">\\<span class="id"
    type="var">y</span>:<span class="id" type="var">T~11~</span>.</span>
    <span class="inlinecode">[<span class="id"
    type="var">x</span>:=<span class="id" type="var">v</span>]<span
    class="id" type="var">t~12~</span></span> <span
    class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T~11~</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">T~12~</span></span> as required.
    <div class="paragraph">

    </div>

-   If <span class="inlinecode"><span class="id"
    type="var">t</span></span> is an application <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span>, the result follows straightforwardly
    from the definition of substitution and the induction hypotheses.
    <div class="paragraph">

    </div>

-   The remaining cases are similar to the application case.

<div class="paragraph">

</div>

Another technical note: This proof is a rare case where an induction on
terms, rather than typing derivations, yields a simpler argument. The
reason for this is that the assumption <span class="inlinecode"><span
class="id" type="var">extend</span></span> <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">U</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">∈</span> <span class="inlinecode"><span
class="id" type="var">T</span></span> is not completely generic, in the
sense that one of the "slots" in the typing relation — namely the
context — is not just a variable, and this means that Coq's native
induction tactic does not give us the induction hypothesis that we want.
It is possible to work around this, but the needed generalization is a
little tricky. The term <span class="inlinecode"><span class="id"
type="var">t</span></span>, on the other hand, *is* completely generic.

</div>

<div class="code code-tight">

\
<div id="proofcontrol5" class="togglescript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')">

<span class="show"></span>

</div>

<div id="proof5" class="proofscript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span> <span
class="id" type="var">t</span> <span class="id" type="var">v</span>
<span class="id" type="var">T</span> <span class="id"
type="var">Ht</span> <span class="id" type="var">Ht'</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">T</span>.\
   <span class="id" type="var">t\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">t</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">T</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">H</span>;\
     <span
class="comment">(\* in each case, we'll want to get at the derivation of H \*)</span>\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">simpl</span>...\
   <span class="id" type="var">Case</span> "tvar".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y</span>. <span class="id"
type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>).\
     <span class="id" type="var">SCase</span> "x=y".\
       <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">extend\_eq</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H2</span>.\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H2</span>; <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H2</span>.\
                   <span class="id" type="tactic">eapply</span> <span
class="id" type="var">context\_invariance</span>... <span class="id"
type="tactic">intros</span> <span class="id" type="var">x</span> <span
class="id" type="var">Hcontra</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">free\_in\_context</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">T</span> <span class="id" type="var">empty</span>
<span class="id" type="var">Hcontra</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">T'</span> <span
class="id" type="var">HT'</span>]...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT'</span>.\
     <span class="id" type="var">SCase</span> "x≠y".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Var</span>. <span class="id" type="tactic">rewrite</span>
<span class="id" type="var">extend\_neq</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H2</span>...\
   <span class="id" type="var">Case</span> "tabs".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">T\_Abs</span>.\
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
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

The substitution lemma can be viewed as a kind of "commutation"
property. Intuitively, it says that substitution and typing can be done
in either order: we can either assign types to the terms <span
class="inlinecode"><span class="id" type="var">t</span></span> and <span
class="inlinecode"><span class="id" type="var">v</span></span>
separately (under suitable contexts) and then combine them using
substitution, or we can substitute first and then assign a type to <span
class="inlinecode"></span> <span class="inlinecode">[<span class="id"
type="var">x</span>:=<span class="id" type="var">v</span>]</span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode"></span> — the result is the same either way.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Main Theorem {.section}
------------

<div class="paragraph">

</div>

We now have the tools we need to prove preservation: if a closed term
<span class="inlinecode"><span class="id" type="var">t</span></span> has
type <span class="inlinecode"><span class="id"
type="var">T</span></span>, and takes an evaluation step to <span
class="inlinecode"><span class="id" type="var">t'</span></span>, then
<span class="inlinecode"><span class="id" type="var">t'</span></span> is
also a closed term with type <span class="inlinecode"><span class="id"
type="var">T</span></span>. In other words, the small-step evaluation
relation preserves types.

</div>

<div class="code code-tight">

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
\

</div>

<div class="doc">

*Proof*: by induction on the derivation of <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">∈</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>.
<div class="paragraph">

</div>

-   We can immediately rule out <span class="inlinecode"><span
    class="id" type="var">T\_Var</span></span>, <span
    class="inlinecode"><span class="id" type="var">T\_Abs</span></span>,
    <span class="inlinecode"><span class="id"
    type="var">T\_True</span></span>, and <span class="inlinecode"><span
    class="id" type="var">T\_False</span></span> as the final rules in
    the derivation, since in each of these cases <span
    class="inlinecode"><span class="id" type="var">t</span></span>
    cannot take a step.
    <div class="paragraph">

    </div>

-   If the last rule in the derivation was <span
    class="inlinecode"><span class="id" type="var">T\_App</span></span>,
    then <span class="inlinecode"><span class="id"
    type="var">t</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span>. There are three cases to consider,
    one for each rule that could have been used to show that <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> takes a step to <span
    class="inlinecode"><span class="id" type="var">t'</span></span>.
    <div class="paragraph">

    </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span> takes a step by <span
        class="inlinecode"><span class="id"
        type="var">ST\_App1</span></span>, with <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> stepping to <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span>, then by the IH <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span> has the same type as <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span>, and hence <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span> <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span> has the same type as
        <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span>.
        <div class="paragraph">

        </div>

    -   The <span class="inlinecode"><span class="id"
        type="var">ST\_App2</span></span> case is similar.
        <div class="paragraph">

        </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span> takes a step by <span
        class="inlinecode"><span class="id"
        type="var">ST\_AppAbs</span></span>, then <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode">=</span>
        <span class="inlinecode">\\<span class="id"
        type="var">x</span>:<span class="id"
        type="var">T~11~.t~12~</span></span> and <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span> steps to <span
        class="inlinecode">[<span class="id" type="var">x</span>:=<span
        class="id" type="var">t~2~</span>]<span class="id"
        type="var">t~12~</span></span>; the desired result now follows
        from the fact that substitution preserves types.
        <div class="paragraph">

        </div>
-   If the last rule in the derivation was <span
    class="inlinecode"><span class="id" type="var">T\_If</span></span>,
    then <span class="inlinecode"><span class="id"
    type="var">t</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="keyword">if</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="keyword">then</span></span> <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span>
    <span class="inlinecode"><span class="id"
    type="keyword">else</span></span> <span class="inlinecode"><span
    class="id" type="var">t~3~</span></span>, and there are again three
    cases depending on how <span class="inlinecode"><span class="id"
    type="var">t</span></span> steps.
    <div class="paragraph">

    </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t</span></span> steps to <span
        class="inlinecode"><span class="id"
        type="var">t~2~</span></span> or <span class="inlinecode"><span
        class="id" type="var">t~3~</span></span>, the result is
        immediate, since <span class="inlinecode"><span class="id"
        type="var">t~2~</span></span> and <span class="inlinecode"><span
        class="id" type="var">t~3~</span></span> have the same type as
        <span class="inlinecode"><span class="id"
        type="var">t</span></span>.
        <div class="paragraph">

        </div>

    -   Otherwise, <span class="inlinecode"><span class="id"
        type="var">t</span></span> steps by <span
        class="inlinecode"><span class="id"
        type="var">ST\_If</span></span>, and the desired conclusion
        follows directly from the induction hypothesis.

</div>

<div class="code code-tight">

\
<div id="proofcontrol6" class="togglescript"
onclick="toggleDisplay('proof6');toggleDisplay('proofcontrol6')">

<span class="show"></span>

</div>

<div id="proof6" class="proofscript"
onclick="toggleDisplay('proof6');toggleDisplay('proofcontrol6')"
style="display: none;">

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
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">HT</span>)
<span class="id" type="var">Case</span>;\
        <span class="id" type="tactic">intros</span> <span class="id"
type="var">t'</span> <span class="id" type="var">HE</span>; <span
class="id" type="tactic">subst</span> <span
style="font-family: serif; font-size:85%;">Γ</span>; <span class="id"
type="tactic">subst</span>;\
        <span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> [<span class="id" type="tactic">inversion</span>
<span class="id" type="var">HE</span>; <span class="id"
type="tactic">subst</span>; <span class="id"
type="tactic">auto</span>].\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>; <span class="id" type="tactic">subst</span>...\
     <span
class="comment">(\* Most of the cases are immediate by induction, \
        and <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> takes care of them \*)</span>\
     <span class="id" type="var">SCase</span> "ST\_AppAbs".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">substitution\_preserves\_typing</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">T~11~</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT1</span>...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 2 stars (subject\_expansion\_stlc) {.section}

An exercise in the <span class="inlinecode"><span class="id"
type="keyword">Types</span></span> chapter asked about the subject
expansion property for the simple language of arithmetic and boolean
expressions. Does this property hold for STLC? That is, is it always the
case that, if <span class="inlinecode"><span class="id"
type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> and
<span class="inlinecode"><span class="id"
type="var">has\_type</span></span> <span class="inlinecode"><span
class="id" type="var">t'</span></span> <span class="inlinecode"><span
class="id" type="var">T</span></span>, then <span
class="inlinecode"><span class="id" type="var">empty</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">∈</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>? If so, prove it. If not, give a
counter-example not involving conditionals.
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Type Soundness {.section}
==============

<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (type\_soundness) {.section}

<div class="paragraph">

</div>

Put progress and preservation together and show that a well-typed term
can *never* reach a stuck state.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">stuck</span> (<span class="id" type="var">t</span>:<span
class="id" type="var">tm</span>) : <span class="id"
type="keyword">Prop</span> :=\
   (<span class="id" type="var">normal\_form</span> <span class="id"
type="var">step</span>) <span class="id" type="var">t</span> <span
style="font-family: arial;">∧</span> ¬ <span class="id"
type="var">value</span> <span class="id" type="var">t</span>.\
\
 <span class="id" type="keyword">Corollary</span> <span class="id"
type="var">soundness</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">t'</span> <span class="id"
type="var">T</span>,\
   <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">t'</span> <span style="font-family: arial;">→</span>\
   \~(<span class="id" type="var">stuck</span> <span class="id"
type="var">t'</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">t'</span> <span
class="id" type="var">T</span> <span class="id"
type="var">Hhas\_type</span> <span class="id" type="var">Hmulti</span>.
<span class="id" type="tactic">unfold</span> <span class="id"
type="var">stuck</span>.\
   <span class="id" type="tactic">intros</span> [<span class="id"
type="var">Hnf</span> <span class="id" type="var">Hnot\_val</span>].
<span class="id" type="tactic">unfold</span> <span class="id"
type="var">normal\_form</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">Hnf</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">Hmulti</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Uniqueness of Types {.section}
===================

<div class="paragraph">

</div>

#### Exercise: 3 stars (types\_unique) {.section}

Another pleasant property of the STLC is that types are unique: a given
term (in a given context) has at most one type. Formalize this statement
and prove it.

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

Additional Exercises {.section}
====================

<div class="paragraph">

</div>

#### Exercise: 1 star (progress\_preservation\_statement) {.section}

Without peeking, write down the progress and preservation theorems for
the simply typed lambda-calculus. ☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (stlc\_variation1) {.section}

Suppose we add a new term <span class="inlinecode"><span class="id"
type="var">zap</span></span> with the following reduction rule:
  
(ST\_Zap)  

------------------------------------------------------------------------

t <span style="font-family: arial;">⇒</span> zap
and the following typing rule:
  
(T\_Zap)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> zap : T
Which of the following properties of the STLC remain true in the
presence of this rule? For each one, write either "remains true" or else
"becomes false." If a property becomes false, give a counterexample.
<div class="paragraph">

</div>

-   Determinism of <span class="inlinecode"><span class="id"
    type="var">step</span></span>
    <div class="paragraph">

    </div>

-   Progress
    <div class="paragraph">

    </div>

-   Preservation

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (stlc\_variation2) {.section}

Suppose instead that we add a new term <span class="inlinecode"><span
class="id" type="var">foo</span></span> with the following reduction
rules:
  
(ST\_Foo1)  

------------------------------------------------------------------------

(\\x:A. x) <span style="font-family: arial;">⇒</span> foo
  
(ST\_Foo2)  

------------------------------------------------------------------------

foo <span style="font-family: arial;">⇒</span> true
Which of the following properties of the STLC remain true in the
presence of this rule? For each one, write either "remains true" or else
"becomes false." If a property becomes false, give a counterexample.
<div class="paragraph">

</div>

-   Determinism of <span class="inlinecode"><span class="id"
    type="var">step</span></span>
    <div class="paragraph">

    </div>

-   Progress
    <div class="paragraph">

    </div>

-   Preservation

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (stlc\_variation3) {.section}

Suppose instead that we remove the rule <span class="inlinecode"><span
class="id" type="var">ST\_App1</span></span> from the <span
class="inlinecode"><span class="id" type="var">step</span></span>
relation. Which of the following properties of the STLC remain true in
the presence of this rule? For each one, write either "remains true" or
else "becomes false." If a property becomes false, give a
counterexample.
<div class="paragraph">

</div>

-   Determinism of <span class="inlinecode"><span class="id"
    type="var">step</span></span>
    <div class="paragraph">

    </div>

-   Progress
    <div class="paragraph">

    </div>

-   Preservation

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (stlc\_variation4) {.section}

Suppose instead that we add the following new rule to the reduction
relation:
  
(ST\_FunnyIfTrue)  

------------------------------------------------------------------------

(if true then t~1~ else t~2~) <span
style="font-family: arial;">⇒</span> true
Which of the following properties of the STLC remain true in the
presence of this rule? For each one, write either "remains true" or else
"becomes false." If a property becomes false, give a counterexample.
<div class="paragraph">

</div>

-   Determinism of <span class="inlinecode"><span class="id"
    type="var">step</span></span>
    <div class="paragraph">

    </div>

-   Progress
    <div class="paragraph">

    </div>

-   Preservation

<div class="paragraph">

</div>

<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (stlc\_variation5) {.section}

Suppose instead that we add the following new rule to the typing
relation:
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ ∈ Bool-\>Bool-\>Bool
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~2~ ∈ Bool
(T\_FunnyApp)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ t~2~ ∈ Bool
Which of the following properties of the STLC remain true in the
presence of this rule? For each one, write either "remains true" or else
"becomes false." If a property becomes false, give a counterexample.
<div class="paragraph">

</div>

-   Determinism of <span class="inlinecode"><span class="id"
    type="var">step</span></span>
    <div class="paragraph">

    </div>

-   Progress
    <div class="paragraph">

    </div>

-   Preservation

<div class="paragraph">

</div>

<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (stlc\_variation6) {.section}

Suppose instead that we add the following new rule to the typing
relation:
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ ∈ Bool
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~2~ ∈ Bool
(T\_FunnyApp')  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ t~2~ ∈ Bool
Which of the following properties of the STLC remain true in the
presence of this rule? For each one, write either "remains true" or else
"becomes false." If a property becomes false, give a counterexample.
<div class="paragraph">

</div>

-   Determinism of <span class="inlinecode"><span class="id"
    type="var">step</span></span>
    <div class="paragraph">

    </div>

-   Progress
    <div class="paragraph">

    </div>

-   Preservation

<div class="paragraph">

</div>

<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (stlc\_variation7) {.section}

Suppose we add the following new rule to the typing relation of the
STLC:
  
(T\_FunnyAbs)  

------------------------------------------------------------------------

<span style="font-family: arial;">⊢</span> \\x:Bool.t ∈ Bool
Which of the following properties of the STLC remain true in the
presence of this rule? For each one, write either "remains true" or else
"becomes false." If a property becomes false, give a counterexample.
<div class="paragraph">

</div>

-   Determinism of <span class="inlinecode"><span class="id"
    type="var">step</span></span>
    <div class="paragraph">

    </div>

-   Progress
    <div class="paragraph">

    </div>

-   Preservation

<div class="paragraph">

</div>

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">STLCProp</span>.\
\

</div>

<div class="doc">

Exercise: STLC with Arithmetic {.section}
------------------------------

<div class="paragraph">

</div>

To see how the STLC might function as the core of a real programming
language, let's extend it with a concrete base type of numbers and some
constants and primitive operators.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">STLCArith</span>.\
\

</div>

<div class="doc">

To types, we add a base type of natural numbers (and remove booleans,
for brevity)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ty</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">TArrow</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TNat</span> : <span class="id"
type="var">ty</span>.\
\

</div>

<div class="doc">

To terms, we add natural number constants, along with successor,
predecessor, multiplication, and zero-testing...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">tm</span> : <span class="id" type="keyword">Type</span> :=\
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
class="id" type="var">tm</span>.\
\
<div id="proofcontrol7" class="togglescript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')">

<span class="show"></span>

</div>

<div id="proof7" class="proofscript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')"
style="display: none;">

<span class="id" type="keyword">Tactic Notation</span> "t\_cases" <span
class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tvar" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tapp"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tabs" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tnat"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tsucc" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"tpred"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tmult" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tif0"
].\

</div>

\

</div>

<div class="doc">

#### Exercise: 4 stars (stlc\_arith) {.section}

Finish formalizing the definition and properties of the STLC extended
with arithmetic. Specifically:
<div class="paragraph">

</div>

-   Copy the whole development of STLC that we went through above (from
    the definition of values through the Progress theorem), and paste it
    into the file at this point.
    <div class="paragraph">

    </div>

-   Extend the definitions of the <span class="inlinecode"><span
    class="id" type="tactic">subst</span></span> operation and the <span
    class="inlinecode"><span class="id" type="var">step</span></span>
    relation to include appropriate clauses for the arithmetic
    operators.
    <div class="paragraph">

    </div>

-   Extend the proofs of all the properties (up to <span
    class="inlinecode"><span class="id"
    type="var">soundness</span></span>) of the original STLC to deal
    with the new syntactic forms. Make sure Coq accepts the whole file.

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
type="var">STLCArith</span>.\
\

</div>

<div class="doc">

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
