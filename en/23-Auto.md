<div id="page">

<div id="header">

</div>

<div id="main">

Auto<span class="subtitle">More Automation</span> {.libtitle}
=================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">Imp</span>.\
\

</div>

<div class="doc">

Up to now, we've continued to use a quite restricted set of Coq's tactic
facilities. In this chapter, we'll learn more about two very powerful
features of Coq's tactic language: proof search via the <span
class="inlinecode"><span class="id" type="tactic">auto</span></span> and
<span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> tactics, and automated forward
reasoning via the <span class="inlinecode"><span class="id"
type="keyword">Ltac</span></span> hypothesis matching machinery. Using
these features together with Ltac's scripting facilities will enable us
to make our proofs startlingly short! Used properly, they can also make
proofs more maintainable and robust in the face of incremental changes
to underlying definitions.
<div class="paragraph">

</div>

There's a third major source of automation we haven't fully studied yet,
namely built-in decision procedures for specific kinds of problems:
<span class="inlinecode"><span class="id"
type="tactic">omega</span></span> is one example, but there are others.
This topic will be defered for a while longer.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

Our motivating example will be this proof, repeated with just a few
small changes from <span class="inlinecode"><span class="id"
type="var">Imp</span></span>. We will try to simplify this proof in
several stages.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Ltac</span> <span class="id"
type="var">inv</span> <span class="id" type="var">H</span> := <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>.\
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
type="var">E2</span>;\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>;\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>;\
            <span class="id" type="tactic">intros</span> <span
class="id" type="var">st2</span> <span class="id" type="var">E2</span>;
<span class="id" type="var">inv</span> <span class="id"
type="var">E2</span>.\
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
     <span class="id" type="var">SCase</span> "b evaluates to true".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHE1</span>. <span class="id"
type="tactic">assumption</span>.\
     <span class="id" type="var">SCase</span> "b evaluates to false
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H5</span>.\
   <span class="id" type="var">Case</span> "E\_IfFalse".\
     <span class="id" type="var">SCase</span> "b evaluates to true
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H5</span>.\
     <span class="id" type="var">SCase</span> "b evaluates to false".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHE1</span>. <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "E\_WhileEnd".\
     <span class="id" type="var">SCase</span> "b evaluates to false".\
       <span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> "b evaluates to true
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H2</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H2</span>.\
   <span class="id" type="var">Case</span> "E\_WhileLoop".\
     <span class="id" type="var">SCase</span> "b evaluates to false
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H4</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H4</span>.\
     <span class="id" type="var">SCase</span> "b evaluates to true".\
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
type="tactic">assumption</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id" type="tactic">auto</span></span> and <span class="inlinecode"><span class="id" type="tactic">eauto</span></span> tactics {.section}
======================================================================================================================================================================

<div class="paragraph">

</div>

Thus far, we have (nearly) always written proof scripts that apply
relevant hypothoses or lemmas by name. In particular, when a chain of
hypothesis applications is needed, we have specified them explicitly.
(The only exceptions introduced so far are using <span
class="inlinecode"><span class="id"
type="tactic">assumption</span></span> to find a matching unqualified
hypothesis or <span class="inlinecode">(<span class="id"
type="var">e</span>)<span class="id"
type="var">constructor</span></span> to find a matching constructor.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">auto\_example\_1</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">R</span>: <span class="id"
type="keyword">Prop</span>), (<span class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">Q</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">R</span> <span class="id" type="var">H1</span>
<span class="id" type="var">H2</span> <span class="id"
type="var">H3</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">H2</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">H1</span>. <span class="id"
type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> tactic frees us from this drudgery by
*searching* for a sequence of applications that will prove the goal

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">auto\_example\_1'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">R</span>: <span class="id"
type="keyword">Prop</span>), (<span class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">Q</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">R</span> <span class="id" type="var">H1</span>
<span class="id" type="var">H2</span> <span class="id"
type="var">H3</span>.\
   <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> tactic solves goals that are solvable
by any combination of
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="tactic">intros</span></span>,
-   <span class="inlinecode"><span class="id"
    type="tactic">apply</span></span> (with a local hypothesis, by
    default).

<div class="paragraph">

</div>

The <span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> tactic works just like <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>,
except that it uses <span class="inlinecode"><span class="id"
type="tactic">eapply</span></span> instead of <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>.
<div class="paragraph">

</div>

Using <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> is always "safe" in the sense that it
will never fail and will never change the proof state: either it
completely solves the current goal, or it does nothing.
<div class="paragraph">

</div>

A more complicated example:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">auto\_example\_2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> <span class="id"
type="var">R</span> <span class="id" type="var">S</span> <span
class="id" type="var">T</span> <span class="id" type="var">U</span> :
<span class="id" type="keyword">Prop</span>,\
   (<span class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span>) <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">T</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">S</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">T</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">U</span>) <span
style="font-family: arial;">→</span>\
   ((<span class="id" type="var">P</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Q</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">P</span><span
style="font-family: arial;">→</span><span class="id"
type="var">S</span>)) <span style="font-family: arial;">→</span>\
   <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">U</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Search can take an arbitrarily long time, so there are limits to how far
<span class="inlinecode"><span class="id"
type="tactic">auto</span></span> will search by default

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">auto\_example\_3</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">R</span> <span class="id" type="var">S</span>
<span class="id" type="var">T</span> <span class="id"
type="var">U</span>: <span class="id" type="keyword">Prop</span>),\
                            (<span class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">Q</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">R</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">S</span>) <span style="font-family: arial;">→</span>\
                            (<span class="id" type="var">S</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">T</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">U</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">U</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">auto</span>. <span
class="comment">(\* When it cannot solve the goal, does nothing! \*)</span>\
   <span class="id" type="tactic">auto</span> 6. <span
class="comment">(\* Optional argument says how deep to search (default depth is 5) \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

When searching for potential proofs of the current goal, <span
class="inlinecode"><span class="id" type="tactic">auto</span></span> and
<span class="inlinecode"><span class="id"
type="tactic">eauto</span></span> consider the hypotheses in the current
context together with a *hint database* of other lemmas and
constructors. Some of the lemmas and constructors we've already seen —
e.g., <span class="inlinecode"><span class="id"
type="var">eq\_refl</span></span>, <span class="inlinecode"><span
class="id" type="var">conj</span></span>, <span class="inlinecode"><span
class="id" type="var">or\_introl</span></span>, and <span
class="inlinecode"><span class="id" type="var">or\_intror</span></span>
— are installed in this hint database by default.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">auto\_example\_4</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> <span class="id"
type="var">R</span> : <span class="id" type="keyword">Prop</span>,\
   <span class="id" type="var">Q</span> <span
style="font-family: arial;">→</span>\
   (<span class="id" type="var">Q</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span>) <span style="font-family: arial;">→</span>\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">∨</span> (<span class="id"
type="var">Q</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">R</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">auto</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

If we want to see which facts <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> is using, we can use <span
class="inlinecode"><span class="id" type="var">info\_auto</span></span>
instead.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">auto\_example\_5</span>: 2 = 2.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">info\_auto</span>. <span
class="comment">(\* subsumes reflexivity because eq\_refl is in hint database \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

We can extend the hint database just for the purposes of one application
of <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> or <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> by writing <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
<span class="inlinecode"><span class="id"
type="keyword">using</span></span> <span class="inlinecode">...</span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">le\_antisym</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>: <span class="id"
type="var">nat</span>, (<span class="id" type="var">n</span> ≤ <span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">m</span> ≤ <span class="id" type="var">n</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> = <span class="id" type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span>. <span class="id"
type="tactic">omega</span>. <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">auto\_example\_6</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> <span class="id"
type="var">p</span> : <span class="id" type="var">nat</span>,\
   (<span class="id" type="var">n</span>≤ <span class="id"
type="var">p</span> <span style="font-family: arial;">→</span> (<span
class="id" type="var">n</span> ≤ <span class="id" type="var">m</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">m</span> ≤ <span class="id" type="var">n</span>)) <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">n</span> ≤ <span class="id"
type="var">p</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">n</span> = <span class="id"
type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">auto</span>. <span
class="comment">(\* does nothing: auto doesn't destruct hypotheses! \*)</span>\
   <span class="id" type="tactic">auto</span> <span class="id"
type="keyword">using</span> <span class="id"
type="var">le\_antisym</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Of course, in any given development there will also be some of our own
specific constructors and lemmas that are used very often in proofs. We
can add these to the global hint database by writing
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Resolve</span> <span class="id" type="var">T</span>.
<div class="paragraph">

</div>

</div>

at the top level, where <span class="inlinecode"><span class="id"
type="var">T</span></span> is a top-level theorem or a constructor of an
inductively defined proposition (i.e., anything whose type is an
implication). As a shorthand, we can write
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id" type="var">c</span>.
<div class="paragraph">

</div>

</div>

to tell Coq to do a <span class="inlinecode"><span class="id"
type="keyword">Hint</span></span> <span class="inlinecode"><span
class="id" type="keyword">Resolve</span></span> for *all* of the
constructors from the inductive definition of <span
class="inlinecode"><span class="id" type="var">c</span></span>.
<div class="paragraph">

</div>

It is also sometimes necessary to add
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Unfold</span> <span class="id" type="var">d</span>.
<div class="paragraph">

</div>

</div>

where <span class="inlinecode"><span class="id"
type="var">d</span></span> is a defined symbol, so that <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>
knows to expand uses of <span class="inlinecode"><span class="id"
type="var">d</span></span> and enable further possibilities for applying
lemmas that it knows about.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Resolve</span> <span class="id"
type="var">le\_antisym</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">auto\_example\_6'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> <span class="id"
type="var">p</span> : <span class="id" type="var">nat</span>,\
   (<span class="id" type="var">n</span>≤ <span class="id"
type="var">p</span> <span style="font-family: arial;">→</span> (<span
class="id" type="var">n</span> ≤ <span class="id" type="var">m</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">m</span> ≤ <span class="id" type="var">n</span>)) <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">n</span> ≤ <span class="id"
type="var">p</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">n</span> = <span class="id"
type="var">m</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">auto</span>. <span
class="comment">(\* picks up hint from database \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">is\_fortytwo</span> <span class="id" type="var">x</span> :=
<span class="id" type="var">x</span> = 42.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">auto\_example\_7</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, (<span class="id" type="var">x</span> ≤ 42 <span
style="font-family: arial;">∧</span> 42 ≤ <span class="id"
type="var">x</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">is\_fortytwo</span> <span class="id"
type="var">x</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">auto</span>. <span
class="comment">(\* does nothing \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Unfold</span> <span class="id"
type="var">is\_fortytwo</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">auto\_example\_7'</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, (<span class="id" type="var">x</span> ≤ 42 <span
style="font-family: arial;">∧</span> 42 ≤ <span class="id"
type="var">x</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">is\_fortytwo</span> <span class="id"
type="var">x</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">info\_auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">ceval</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">st12</span> := <span class="id" type="var">update</span>
(<span class="id" type="var">update</span> <span class="id"
type="var">empty\_state</span> <span class="id" type="var">X</span> 1)
<span class="id" type="var">Y</span> 2.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">st21</span> := <span class="id" type="var">update</span>
(<span class="id" type="var">update</span> <span class="id"
type="var">empty\_state</span> <span class="id" type="var">X</span> 2)
<span class="id" type="var">Y</span> 1.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">auto\_example\_8</span> : <span
style="font-family: arial;">∃</span><span class="id"
type="var">s'</span>,\
   (<span class="id" type="var">IFB</span> (<span class="id"
type="var">BLe</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">AId</span>
<span class="id" type="var">Y</span>))\
     <span class="id" type="var">THEN</span> (<span class="id"
type="var">Z</span> ::= <span class="id" type="var">AMinus</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">Y</span>)
(<span class="id" type="var">AId</span> <span class="id"
type="var">X</span>))\
     <span class="id" type="var">ELSE</span> (<span class="id"
type="var">Y</span> ::= <span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">AId</span> <span class="id"
type="var">Z</span>))\
   <span class="id" type="var">FI</span>) / <span class="id"
type="var">st21</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">s'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">eexists</span>. <span class="id"
type="var">info\_auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">auto\_example\_8'</span> : <span
style="font-family: arial;">∃</span><span class="id"
type="var">s'</span>,\
   (<span class="id" type="var">IFB</span> (<span class="id"
type="var">BLe</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">AId</span>
<span class="id" type="var">Y</span>))\
     <span class="id" type="var">THEN</span> (<span class="id"
type="var">Z</span> ::= <span class="id" type="var">AMinus</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">Y</span>)
(<span class="id" type="var">AId</span> <span class="id"
type="var">X</span>))\
     <span class="id" type="var">ELSE</span> (<span class="id"
type="var">Y</span> ::= <span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">AId</span> <span class="id"
type="var">Z</span>))\
   <span class="id" type="var">FI</span>) / <span class="id"
type="var">st12</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">s'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">eexists</span>. <span class="id"
type="var">info\_auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Now let's take a pass over <span class="inlinecode"><span class="id"
type="var">ceval\_deterministic</span></span> using <span
class="inlinecode"><span class="id" type="tactic">auto</span></span> to
simplify the proof script. We see that all simple sequences of
hypothesis applications and all uses of <span class="inlinecode"><span
class="id" type="tactic">reflexivity</span></span> can be replaced by
<span class="inlinecode"><span class="id"
type="tactic">auto</span></span>, which we add to the default tactic to
be applied to each case.

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
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st1</span> <span class="id" type="var">st2</span>
<span class="id" type="var">E1</span> <span class="id"
type="var">E2</span>;\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>;\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>;\
            <span class="id" type="tactic">intros</span> <span
class="id" type="var">st2</span> <span class="id" type="var">E2</span>;
<span class="id" type="var">inv</span> <span class="id"
type="var">E2</span>; <span class="id" type="tactic">auto</span>.\
   <span class="id" type="var">Case</span> "E\_Seq".\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">EQ1</span>.\
       <span class="id" type="var">SCase</span> "Proof of assertion".
<span class="id" type="tactic">auto</span>.\
     <span class="id" type="tactic">subst</span> <span class="id"
type="var">st'0</span>.\
     <span class="id" type="tactic">auto</span>.\
   <span class="id" type="var">Case</span> "E\_IfTrue".\
     <span class="id" type="var">SCase</span> "b evaluates to false
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H5</span>.\
   <span class="id" type="var">Case</span> "E\_IfFalse".\
     <span class="id" type="var">SCase</span> "b evaluates to true
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H5</span>.\
   <span class="id" type="var">Case</span> "E\_WhileEnd".\
     <span class="id" type="var">SCase</span> "b evaluates to true
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H2</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H2</span>.\
   <span class="id" type="var">Case</span> "E\_WhileLoop".\
     <span class="id" type="var">SCase</span> "b evaluates to false
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H4</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H4</span>.\
     <span class="id" type="var">SCase</span> "b evaluates to true".\
       <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">EQ1</span>.\
         <span class="id" type="var">SSCase</span> "Proof of assertion".
<span class="id" type="tactic">auto</span>.\
       <span class="id" type="tactic">subst</span> <span class="id"
type="var">st'0</span>.\
       <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

When we are using a particular tactic many times in a proof, we can use
a variant of the <span class="inlinecode"><span class="id"
type="keyword">Proof</span></span> command to make that tactic into a
default within the proof. Saying <span class="inlinecode"><span
class="id" type="keyword">Proof</span></span> <span
class="inlinecode"><span class="id" type="keyword">with</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
(where <span class="inlinecode"><span class="id"
type="var">t</span></span> is an arbitrary tactic) allows us to use
<span class="inlinecode"><span class="id"
type="var">t~1~</span>...</span> as a shorthand for <span
class="inlinecode"><span class="id" type="var">t~1~</span>;<span
class="id" type="var">t</span></span> within the proof. As an
illustration, here is an alternate version of the previous proof, using
<span class="inlinecode"><span class="id"
type="keyword">Proof</span></span> <span class="inlinecode"><span
class="id" type="keyword">with</span></span> <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_deterministic'\_alt</span>: <span
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
<div id="proofcontrol1" class="togglescript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')">

<span class="show"></span>

</div>

<div id="proof1" class="proofscript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st1</span> <span class="id" type="var">st2</span>
<span class="id" type="var">E1</span> <span class="id"
type="var">E2</span>;\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>;\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>;\
            <span class="id" type="tactic">intros</span> <span
class="id" type="var">st2</span> <span class="id" type="var">E2</span>;
<span class="id" type="var">inv</span> <span class="id"
type="var">E2</span>...\
   <span class="id" type="var">Case</span> "E\_Seq".\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">EQ1</span>.\
       <span class="id" type="var">SCase</span> "Proof of assertion"...\
     <span class="id" type="tactic">subst</span> <span class="id"
type="var">st'0</span>...\
   <span class="id" type="var">Case</span> "E\_IfTrue".\
     <span class="id" type="var">SCase</span> "b evaluates to false
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H5</span>.\
   <span class="id" type="var">Case</span> "E\_IfFalse".\
     <span class="id" type="var">SCase</span> "b evaluates to true
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H5</span>.\
   <span class="id" type="var">Case</span> "E\_WhileEnd".\
     <span class="id" type="var">SCase</span> "b evaluates to true
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H2</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H2</span>.\
   <span class="id" type="var">Case</span> "E\_WhileLoop".\
     <span class="id" type="var">SCase</span> "b evaluates to false
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H4</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H4</span>.\
     <span class="id" type="var">SCase</span> "b evaluates to true".\
       <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">EQ1</span>.\
         <span class="id" type="var">SSCase</span> "Proof of
assertion"...\
       <span class="id" type="tactic">subst</span> <span class="id"
type="var">st'0</span>...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Searching Hypotheses {.section}
====================

<div class="paragraph">

</div>

The proof has become simpler, but there is still an annoying amount of
repetition. Let's start by tackling the contradiction cases. Each of
them occurs in a situation where we have both
<div class="paragraph">

</div>

<span class="inlinecode"><span class="id" type="var">H1</span>:</span>
<span class="inlinecode"><span class="id" type="var">beval</span></span>
<span class="inlinecode"><span class="id" type="var">st</span></span>
<span class="inlinecode"><span class="id" type="var">b</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">false</span></span>
<div class="paragraph">

</div>

and
<div class="paragraph">

</div>

<span class="inlinecode"><span class="id" type="var">H2</span>:</span>
<span class="inlinecode"><span class="id" type="var">beval</span></span>
<span class="inlinecode"><span class="id" type="var">st</span></span>
<span class="inlinecode"><span class="id" type="var">b</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">true</span></span>
<div class="paragraph">

</div>

as hypotheses. The contradiction is evident, but demonstrating it is a
little complicated: we have to locate the two hypotheses <span
class="inlinecode"><span class="id" type="var">H1</span></span> and
<span class="inlinecode"><span class="id" type="var">H2</span></span>
and do a <span class="inlinecode"><span class="id"
type="tactic">rewrite</span></span> following by an <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span>. We'd like to automate this
process.
<div class="paragraph">

</div>

Note: In fact, Coq has a built-in tactic <span class="inlinecode"><span
class="id" type="tactic">congruence</span></span> that will do the job.
But we'll ignore the existence of this tactic for now, in order to
demonstrate how to build forward search tactics by hand.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

As a first step, we can abstract out the piece of script in question by
writing a small amount of paramerized Ltac.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Ltac</span> <span class="id"
type="var">rwinv</span> <span class="id" type="var">H1</span> <span
class="id" type="var">H2</span> := <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">H1</span> <span
class="id" type="keyword">in</span> <span class="id"
type="var">H2</span>; <span class="id" type="var">inv</span> <span
class="id" type="var">H2</span>.\
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
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st1</span> <span class="id" type="var">st2</span>
<span class="id" type="var">E1</span> <span class="id"
type="var">E2</span>;\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>;\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>;\
            <span class="id" type="tactic">intros</span> <span
class="id" type="var">st2</span> <span class="id" type="var">E2</span>;
<span class="id" type="var">inv</span> <span class="id"
type="var">E2</span>; <span class="id" type="tactic">auto</span>.\
   <span class="id" type="var">Case</span> "E\_Seq".\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">EQ1</span>.\
       <span class="id" type="var">SCase</span> "Proof of assertion".
<span class="id" type="tactic">auto</span>.\
     <span class="id" type="tactic">subst</span> <span class="id"
type="var">st'0</span>.\
     <span class="id" type="tactic">auto</span>.\
   <span class="id" type="var">Case</span> "E\_IfTrue".\
     <span class="id" type="var">SCase</span> "b evaluates to false
(contradiction)".\
       <span class="id" type="var">rwinv</span> <span class="id"
type="var">H</span> <span class="id" type="var">H5</span>.\
   <span class="id" type="var">Case</span> "E\_IfFalse".\
     <span class="id" type="var">SCase</span> "b evaluates to true
(contradiction)".\
       <span class="id" type="var">rwinv</span> <span class="id"
type="var">H</span> <span class="id" type="var">H5</span>.\
   <span class="id" type="var">Case</span> "E\_WhileEnd".\
     <span class="id" type="var">SCase</span> "b evaluates to true
(contradiction)".\
       <span class="id" type="var">rwinv</span> <span class="id"
type="var">H</span> <span class="id" type="var">H2</span>.\
   <span class="id" type="var">Case</span> "E\_WhileLoop".\
     <span class="id" type="var">SCase</span> "b evaluates to false
(contradiction)".\
       <span class="id" type="var">rwinv</span> <span class="id"
type="var">H</span> <span class="id" type="var">H4</span>.\
     <span class="id" type="var">SCase</span> "b evaluates to true".\
       <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">EQ1</span>.\
         <span class="id" type="var">SSCase</span> "Proof of assertion".
<span class="id" type="tactic">auto</span>.\
       <span class="id" type="tactic">subst</span> <span class="id"
type="var">st'0</span>.\
       <span class="id" type="tactic">auto</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

But this is not much better. We really want Coq to discover the relevant
hypotheses for us. We can do this by using the <span
class="inlinecode"><span class="id" type="keyword">match</span></span>
<span class="inlinecode"><span class="id" type="var">goal</span></span>
<span class="inlinecode"><span class="id"
type="keyword">with</span></span> <span class="inlinecode">...</span>
<span class="inlinecode"><span class="id"
type="keyword">end</span></span> facility of Ltac.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Ltac</span> <span class="id"
type="var">find\_rwinv</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">goal</span> <span class="id" type="keyword">with</span>\
     <span class="id" type="var">H1</span>: ?<span class="id"
type="var">E</span> = <span class="id" type="var">true</span>, <span
class="id" type="var">H2</span>: ?<span class="id" type="var">E</span> =
<span class="id" type="var">false</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">\_</span> ⇒ <span class="id" type="var">rwinv</span> <span
class="id" type="var">H1</span> <span class="id" type="var">H2</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

In words, this <span class="inlinecode"><span class="id"
type="keyword">match</span></span> <span class="inlinecode"><span
class="id" type="var">goal</span></span> looks for two (distinct)
hypotheses that have the form of equalities with the same arbitrary
expression <span class="inlinecode"><span class="id"
type="var">E</span></span> on the left and conflicting boolean values on
the right; if such hypotheses are found, it binds <span
class="inlinecode"><span class="id" type="var">H1</span></span> and
<span class="inlinecode"><span class="id" type="var">H2</span></span> to
their names, and applies the tactic after the <span
class="inlinecode">⇒</span>.
<div class="paragraph">

</div>

Adding this tactic to our default string handles all the contradiction
cases.

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
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st1</span> <span class="id" type="var">st2</span>
<span class="id" type="var">E1</span> <span class="id"
type="var">E2</span>;\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>;\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>;\
            <span class="id" type="tactic">intros</span> <span
class="id" type="var">st2</span> <span class="id" type="var">E2</span>;
<span class="id" type="var">inv</span> <span class="id"
type="var">E2</span>; <span class="id" type="tactic">try</span> <span
class="id" type="var">find\_rwinv</span>; <span class="id"
type="tactic">auto</span>.\
   <span class="id" type="var">Case</span> "E\_Seq".\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">EQ1</span>.\
       <span class="id" type="var">SCase</span> "Proof of assertion".
<span class="id" type="tactic">auto</span>.\
     <span class="id" type="tactic">subst</span> <span class="id"
type="var">st'0</span>.\
     <span class="id" type="tactic">auto</span>.\
   <span class="id" type="var">Case</span> "E\_WhileLoop".\
     <span class="id" type="var">SCase</span> "b evaluates to true".\
       <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = <span class="id" type="var">st'0</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">EQ1</span>.\
         <span class="id" type="var">SSCase</span> "Proof of assertion".
<span class="id" type="tactic">auto</span>.\
       <span class="id" type="tactic">subst</span> <span class="id"
type="var">st'0</span>.\
       <span class="id" type="tactic">auto</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Finally, let's see about the remaining cases. Each of them involves
applying a conditional hypothesis to extract an equality. Currently we
have phrased these as assertions, so that we have to predict what the
resulting equality will be (although we can then use <span
class="inlinecode"><span class="id" type="tactic">auto</span></span> to
prove it.) An alternative is to pick the relevant hypotheses to use, and
then rewrite with them, as follows:

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
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st1</span> <span class="id" type="var">st2</span>
<span class="id" type="var">E1</span> <span class="id"
type="var">E2</span>;\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>;\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>;\
            <span class="id" type="tactic">intros</span> <span
class="id" type="var">st2</span> <span class="id" type="var">E2</span>;
<span class="id" type="var">inv</span> <span class="id"
type="var">E2</span>; <span class="id" type="tactic">try</span> <span
class="id" type="var">find\_rwinv</span>; <span class="id"
type="tactic">auto</span>.\
   <span class="id" type="var">Case</span> "E\_Seq".\
     <span class="id" type="tactic">rewrite</span> (<span class="id"
type="var">IHE1\_1</span> <span class="id" type="var">st'0</span> <span
class="id" type="var">H1</span>) <span class="id"
type="keyword">in</span> ×. <span class="id" type="tactic">auto</span>.\
   <span class="id" type="var">Case</span> "E\_WhileLoop".\
     <span class="id" type="var">SCase</span> "b evaluates to true".\
       <span class="id" type="tactic">rewrite</span> (<span class="id"
type="var">IHE1\_1</span> <span class="id" type="var">st'0</span> <span
class="id" type="var">H3</span>) <span class="id"
type="keyword">in</span> ×. <span class="id" type="tactic">auto</span>.
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Now we can automate the task of finding the relevant hypotheses to
rewrite with.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Ltac</span> <span class="id"
type="var">find\_eqn</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">goal</span> <span class="id" type="keyword">with</span>\
     <span class="id" type="var">H1</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, ?<span class="id" type="var">P</span> <span
class="id" type="var">x</span> <span
style="font-family: arial;">→</span> ?<span class="id"
type="var">L</span> = ?<span class="id" type="var">R</span>, <span
class="id" type="var">H2</span>: ?<span class="id" type="var">P</span>
?<span class="id" type="var">X</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">\_</span> ⇒\
          <span class="id" type="tactic">rewrite</span> (<span
class="id" type="var">H1</span> <span class="id" type="var">X</span>
<span class="id" type="var">H2</span>) <span class="id"
type="keyword">in</span> ×\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

But there are several pairs of hypotheses that have the right general
form, and it seems tricky to pick out the ones we actually need. A key
trick is to realize that we can *try them all*! Here's how this works:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="tactic">rewrite</span></span> will fail given a trivial
    equation of the form <span class="inlinecode"><span class="id"
    type="var">X</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">X</span></span>.
-   each execution of <span class="inlinecode"><span class="id"
    type="keyword">match</span></span> <span class="inlinecode"><span
    class="id" type="var">goal</span></span> will keep trying to find a
    valid pair of hypotheses until the tactic on the RHS of the match
    succeeds; if there are no such pairs, it fails.
-   we can wrap the whole thing in a <span class="inlinecode"><span
    class="id" type="tactic">repeat</span></span> which will keep doing
    useful rewrites until only trivial ones are left.

</div>

<div class="code code-tight">

\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_deterministic'''''</span>: <span
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
type="var">E2</span>;\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>;\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>;\
            <span class="id" type="tactic">intros</span> <span
class="id" type="var">st2</span> <span class="id" type="var">E2</span>;
<span class="id" type="var">inv</span> <span class="id"
type="var">E2</span>; <span class="id" type="tactic">try</span> <span
class="id" type="var">find\_rwinv</span>; <span class="id"
type="tactic">repeat</span> <span class="id"
type="var">find\_eqn</span>; <span class="id"
type="tactic">auto</span>.\
   <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The big pay-off in this approach is that our proof script should be
robust in the face of modest changes to our language. For example, we
can add a <span class="inlinecode"><span class="id"
type="var">REPEAT</span></span> command to the language. (This was an
exercise in <span class="inlinecode"><span class="id"
type="var">Hoare.v</span></span>.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Repeat</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">com</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">CSkip</span> : <span class="id"
type="var">com</span>\
   | <span class="id" type="var">CAsgn</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">com</span>\
   | <span class="id" type="var">CSeq</span> : <span class="id"
type="var">com</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">com</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">com</span>\
   | <span class="id" type="var">CIf</span> : <span class="id"
type="var">bexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">com</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">com</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">com</span>\
   | <span class="id" type="var">CWhile</span> : <span class="id"
type="var">bexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">com</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">com</span>\
   | <span class="id" type="var">CRepeat</span> : <span class="id"
type="var">com</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">bexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">com</span>.\
\

</div>

<div class="doc">

<span class="inlinecode"><span class="id"
type="var">REPEAT</span></span> behaves like <span
class="inlinecode"><span class="id" type="var">WHILE</span></span>,
except that the loop guard is checked *after* each execution of the
body, with the loop repeating as long as the guard stays *false*.
Because of this, the body will always execute at least once.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Tactic Notation</span> "com\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "SKIP" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "::=" |
<span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> ";"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "IFB" | <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">c</span> "WHILE"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "CRepeat" ].\
\
 <span class="id" type="keyword">Notation</span> "'SKIP'" :=\
   <span class="id" type="var">CSkip</span>.\
 <span class="id" type="keyword">Notation</span> "c1 ; c2" :=\
   (<span class="id" type="var">CSeq</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c2</span>) (<span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 80, <span class="id" type="var">right</span>
<span class="id" type="var">associativity</span>).\
 <span class="id" type="keyword">Notation</span> "X '::=' a" :=\
   (<span class="id" type="var">CAsgn</span> <span class="id"
type="var">X</span> <span class="id" type="var">a</span>) (<span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 60).\
 <span class="id" type="keyword">Notation</span> "'WHILE' b 'DO' c
'END'" :=\
   (<span class="id" type="var">CWhile</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span>) (<span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 80, <span class="id" type="var">right</span>
<span class="id" type="var">associativity</span>).\
 <span class="id" type="keyword">Notation</span> "'IFB' e1 'THEN' e2
'ELSE' e3 'FI'" :=\
   (<span class="id" type="var">CIf</span> <span class="id"
type="var">e1</span> <span class="id" type="var">e2</span> <span
class="id" type="var">e3</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 80,
<span class="id" type="var">right</span> <span class="id"
type="var">associativity</span>).\
 <span class="id" type="keyword">Notation</span> "'REPEAT' e1 'UNTIL' b2
'END'" :=\
   (<span class="id" type="var">CRepeat</span> <span class="id"
type="var">e1</span> <span class="id" type="var">b2</span>) (<span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 80, <span class="id" type="var">right</span>
<span class="id" type="var">associativity</span>).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ceval</span> : <span class="id" type="var">state</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">com</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">state</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">E\_Skip</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span>,\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> <span class="id" type="var">SKIP</span> <span
class="id" type="var">st</span>\
   | <span class="id" type="var">E\_Ass</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">a1</span> <span
class="id" type="var">n</span> <span class="id" type="var">X</span>,\
       <span class="id" type="var">aeval</span> <span class="id"
type="var">st</span> <span class="id" type="var">a1</span> = <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">X</span> ::= <span
class="id" type="var">a1</span>) (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">X</span> <span class="id" type="var">n</span>)\
   | <span class="id" type="var">E\_Seq</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">c1</span> <span class="id" type="var">c2</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>
<span class="id" type="var">st''</span>,\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st'</span> <span class="id" type="var">c2</span> <span
class="id" type="var">st''</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">c1</span> ; <span
class="id" type="var">c2</span>) <span class="id"
type="var">st''</span>\
   | <span class="id" type="var">E\_IfTrue</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">b1</span> <span class="id" type="var">c1</span>
<span class="id" type="var">c2</span>,\
       <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b1</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">IFB</span> <span
class="id" type="var">b1</span> <span class="id" type="var">THEN</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">ELSE</span> <span class="id" type="var">c2</span> <span
class="id" type="var">FI</span>) <span class="id" type="var">st'</span>\
   | <span class="id" type="var">E\_IfFalse</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">b1</span> <span class="id" type="var">c1</span>
<span class="id" type="var">c2</span>,\
       <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b1</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> <span class="id" type="var">c2</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">IFB</span> <span
class="id" type="var">b1</span> <span class="id" type="var">THEN</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">ELSE</span> <span class="id" type="var">c2</span> <span
class="id" type="var">FI</span>) <span class="id" type="var">st'</span>\
   | <span class="id" type="var">E\_WhileEnd</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">b1</span> <span class="id" type="var">st</span> <span
class="id" type="var">c1</span>,\
       <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b1</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">WHILE</span> <span
class="id" type="var">b1</span> <span class="id" type="var">DO</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">END</span>) <span class="id" type="var">st</span>\
   | <span class="id" type="var">E\_WhileLoop</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">st''</span> <span class="id" type="var">b1</span>
<span class="id" type="var">c1</span>,\
       <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b1</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st'</span> (<span class="id" type="var">WHILE</span> <span
class="id" type="var">b1</span> <span class="id" type="var">DO</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">END</span>) <span class="id" type="var">st''</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">WHILE</span> <span
class="id" type="var">b1</span> <span class="id" type="var">DO</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">END</span>) <span class="id" type="var">st''</span>\
   | <span class="id" type="var">E\_RepeatEnd</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">b1</span> <span class="id" type="var">c1</span>,\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">beval</span> <span class="id"
type="var">st'</span> <span class="id" type="var">b1</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">CRepeat</span> <span
class="id" type="var">c1</span> <span class="id" type="var">b1</span>)
<span class="id" type="var">st'</span>\
   | <span class="id" type="var">E\_RepeatLoop</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">st''</span> <span class="id" type="var">b1</span>
<span class="id" type="var">c1</span>,\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">beval</span> <span class="id"
type="var">st'</span> <span class="id" type="var">b1</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st'</span> (<span class="id" type="var">CRepeat</span> <span
class="id" type="var">c1</span> <span class="id" type="var">b1</span>)
<span class="id" type="var">st''</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">ceval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">CRepeat</span> <span
class="id" type="var">c1</span> <span class="id" type="var">b1</span>)
<span class="id" type="var">st''</span>\
 .\
\
 <span class="id" type="keyword">Tactic Notation</span> "ceval\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_Skip" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"E\_Ass"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_Seq"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_IfTrue" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"E\_IfFalse"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_WhileEnd" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"E\_WhileLoop"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_RepeatEnd" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"E\_RepeatLoop"\
 ].\
\
 <span class="id" type="keyword">Notation</span> "c1 '/' st '<span
style="font-family: arial;">⇓</span>' st'" := (<span class="id"
type="var">ceval</span> <span class="id" type="var">st</span> <span
class="id" type="var">c1</span> <span class="id" type="var">st'</span>)\
                                  (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40,
<span class="id" type="var">st</span> <span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 39).\
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
type="var">E2</span>;\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>;\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>;\
            <span class="id" type="tactic">intros</span> <span
class="id" type="var">st2</span> <span class="id" type="var">E2</span>;
<span class="id" type="var">inv</span> <span class="id"
type="var">E2</span>; <span class="id" type="tactic">try</span> <span
class="id" type="var">find\_rwinv</span>; <span class="id"
type="tactic">repeat</span> <span class="id"
type="var">find\_eqn</span>; <span class="id"
type="tactic">auto</span>.\
   <span class="id" type="var">Case</span> "E\_RepeatEnd".\
     <span class="id" type="var">SCase</span> "b evaluates to false
(contradiction)".\
        <span class="id" type="var">find\_rwinv</span>.\
        <span class="comment">(\* oops: why didn't <span
class="inlinecode"><span class="id"
type="var">find\_rwinv</span></span> solve this for us already? \
           answer: we did things in the wrong order. \*)</span>\
   <span class="id" type="tactic">case</span> "E\_RepeatLoop".\
      <span class="id" type="var">SCase</span> "b evaluates to true
(contradiction)".\
         <span class="id" type="var">find\_rwinv</span>.\
 <span class="id" type="keyword">Qed</span>.\
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
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st1</span> <span class="id" type="var">st2</span>
<span class="id" type="var">E1</span> <span class="id"
type="var">E2</span>;\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>;\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>;\
            <span class="id" type="tactic">intros</span> <span
class="id" type="var">st2</span> <span class="id" type="var">E2</span>;
<span class="id" type="var">inv</span> <span class="id"
type="var">E2</span>; <span class="id" type="tactic">repeat</span> <span
class="id" type="var">find\_eqn</span>; <span class="id"
type="tactic">try</span> <span class="id" type="var">find\_rwinv</span>;
<span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Repeat</span>.\
\

</div>

<div class="doc">

These examples just give a flavor of what "hyper-automation" can do...
<div class="paragraph">

</div>

The details of using <span class="inlinecode"><span class="id"
type="keyword">match</span></span> <span class="inlinecode"><span
class="id" type="var">goal</span></span> are tricky, and debugging is
not pleasant at all. But it is well worth adding at least simple uses to
your proofs to avoid tedium and "future proof" your scripts.
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
