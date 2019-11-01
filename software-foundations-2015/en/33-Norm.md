<div id="page">

<div id="header">

</div>

<div id="main">

Norm<span class="subtitle">Normalization of STLC</span> {.libtitle}
=======================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span
class="comment">(\* Chapter maintained by Andrew Tolmach \*)</span>\
\
 <span class="comment">(\* (Based on TAPL Ch. 12.) \*)</span>\
\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id"
type="var">Smallstep</span>.\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">multi</span>.\
\

</div>

<div class="doc">

<div class="paragraph">

</div>

(This chapter is optional.)
<div class="paragraph">

</div>

In this chapter, we consider another fundamental theoretical property of
the simply typed lambda-calculus: the fact that the evaluation of a
well-typed program is guaranteed to halt in a finite number of
steps—-i.e., every well-typed term is *normalizable*.
<div class="paragraph">

</div>

Unlike the type-safety properties we have considered so far, the
normalization property does not extend to full-blown programming
languages, because these languages nearly always extend the simply typed
lambda-calculus with constructs, such as general recursion (as we
discussed in the MoreStlc chapter) or recursive types, that can be used
to write nonterminating programs. However, the issue of normalization
reappears at the level of *types* when we consider the metatheory of
polymorphic versions of the lambda calculus such as F\_omega: in this
system, the language of types effectively contains a copy of the simply
typed lambda-calculus, and the termination of the typechecking algorithm
will hinge on the fact that a \`\`normalization'' operation on type
expressions is guaranteed to terminate.
<div class="paragraph">

</div>

Another reason for studying normalization proofs is that they are some
of the most beautiful—-and mind-blowing—-mathematics to be found in the
type theory literature, often (as here) involving the fundamental proof
technique of *logical relations*.
<div class="paragraph">

</div>

The calculus we shall consider here is the simply typed lambda-calculus
over a single base type <span class="inlinecode"><span class="id"
type="var">bool</span></span> and with pairs. We'll give full details of
the development for the basic lambda-calculus terms treating <span
class="inlinecode"><span class="id" type="var">bool</span></span> as an
uninterpreted base type, and leave the extension to the boolean
operators and pairs to the reader. Even for the base calculus,
normalization is not entirely trivial to prove, since each reduction of
a term can duplicate redexes in subterms.
<div class="paragraph">

</div>

#### Exercise: 1 star {.section}

Where do we fail if we attempt to prove normalization by a
straightforward induction on the size of a well-typed term?

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

Language {.section}
========

<div class="paragraph">

</div>

We begin by repeating the relevant language definition, which is similar
to those in the MoreStlc chapter, and supporting results including type
preservation and step determinism. (We won't need progress.) You may
just wish to skip down to the Normalization section...

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Syntax and Operational Semantics {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ty</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">TBool</span> : <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TArrow</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TProd</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span>\
 .\
\
 <span class="id" type="keyword">Tactic Notation</span> "T\_cases" <span
class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "TBool" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"TArrow" | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "TProd" ].\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">tm</span> : <span class="id" type="keyword">Type</span> :=\
     <span class="comment">(\* pure STLC \*)</span>\
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
     <span class="comment">(\* pairs \*)</span>\
   | <span class="id" type="var">tpair</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tfst</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">tsnd</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
     <span class="comment">(\* booleans \*)</span>\
   | <span class="id" type="var">ttrue</span> : <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tfalse</span> : <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tif</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>.\
           <span class="comment">(\* i.e., <span
class="inlinecode"><span class="id" type="keyword">if</span></span>
<span class="inlinecode"><span class="id" type="var">t0</span></span>
<span class="inlinecode"><span class="id"
type="keyword">then</span></span> <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> <span class="inlinecode"><span
class="id" type="keyword">else</span></span> <span
class="inlinecode"><span class="id"
type="var">t~2~</span></span> \*)</span>\
\
 <span class="id" type="keyword">Tactic Notation</span> "t\_cases" <span
class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tvar" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tapp"
| <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tabs"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tpair" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tfst"
| <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tsnd"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ttrue" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"tfalse" | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tif" ].\
\

</div>

<div class="doc">

### Substitution {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="tactic">subst</span> (<span class="id" type="var">x</span>:<span
class="id" type="var">id</span>) (<span class="id"
type="var">s</span>:<span class="id" type="var">tm</span>) (<span
class="id" type="var">t</span>:<span class="id" type="var">tm</span>) :
<span class="id" type="var">tm</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">t</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">tvar</span> <span class="id"
type="var">y</span> ⇒ <span class="id" type="keyword">if</span> <span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">s</span> <span class="id" type="keyword">else</span> <span
class="id" type="var">t</span>\
   | <span class="id" type="var">tabs</span> <span class="id"
type="var">y</span> <span class="id" type="var">T</span> <span
class="id" type="var">t~1~</span> ⇒ <span class="id"
type="var">tabs</span> <span class="id" type="var">y</span> <span
class="id" type="var">T</span> (<span class="id"
type="keyword">if</span> <span class="id" type="var">eq\_id\_dec</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y</span> <span class="id" type="keyword">then</span> <span
class="id" type="var">t~1~</span> <span class="id"
type="keyword">else</span> (<span class="id" type="tactic">subst</span>
<span class="id" type="var">x</span> <span class="id"
type="var">s</span> <span class="id" type="var">t~1~</span>))\
   | <span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒ <span
class="id" type="var">tapp</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">tpair</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒ <span
class="id" type="var">tpair</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">tfst</span> <span class="id"
type="var">t~1~</span> ⇒ <span class="id" type="var">tfst</span> (<span
class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">tsnd</span> <span class="id"
type="var">t~1~</span> ⇒ <span class="id" type="var">tsnd</span> (<span
class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">ttrue</span> ⇒ <span class="id"
type="var">ttrue</span>\
   | <span class="id" type="var">tfalse</span> ⇒ <span class="id"
type="var">tfalse</span>\
   | <span class="id" type="var">tif</span> <span class="id"
type="var">t0</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> ⇒ <span class="id"
type="var">tif</span> (<span class="id" type="tactic">subst</span> <span
class="id" type="var">x</span> <span class="id" type="var">s</span>
<span class="id" type="var">t0</span>) (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>)\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Notation</span> "'[' x ':=' s ']' t" :=
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 20).\
\

</div>

<div class="doc">

### Reduction {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">value</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">v\_abs</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>,\
       <span class="id" type="var">value</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>)\
   | <span class="id" type="var">v\_pair</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">v~2~</span>,\
       <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">value</span> <span class="id"
type="var">v~2~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">value</span> (<span class="id"
type="var">tpair</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">v~2~</span>)\
   | <span class="id" type="var">v\_true</span> : <span class="id"
type="var">value</span> <span class="id" type="var">ttrue</span>\
   | <span class="id" type="var">v\_false</span> : <span class="id"
type="var">value</span> <span class="id" type="var">tfalse</span>\
 .\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">value</span>.\
\
 <span class="id" type="keyword">Reserved Notation</span> "t~1~ '<span
style="font-family: arial;">⇒</span>' t~2~" (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">step</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">ST\_AppAbs</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span> <span class="id" type="var">v~2~</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~2~</span> <span style="font-family: arial;">→</span>\
          (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>) <span class="id" type="var">v~2~</span>) <span
style="font-family: arial;">⇒</span> [<span class="id"
type="var">x</span>:=<span class="id" type="var">v~2~</span>]<span
class="id" type="var">t~12~</span>\
   | <span class="id" type="var">ST\_App1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
          <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
          (<span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">ST\_App2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
          (<span class="id" type="var">tapp</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>)\
   <span class="comment">(\* pairs \*)</span>\
   | <span class="id" type="var">ST\_Pair1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
         <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tpair</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tpair</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">ST\_Pair2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
         <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
         <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tpair</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tpair</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>)\
   | <span class="id" type="var">ST\_Fst</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span>,\
         <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tfst</span> <span class="id"
type="var">t~1~</span>) <span style="font-family: arial;">⇒</span>
(<span class="id" type="var">tfst</span> <span class="id"
type="var">t~1~'</span>)\
   | <span class="id" type="var">ST\_FstPair</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">v~2~</span>,\
         <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
         <span class="id" type="var">value</span> <span class="id"
type="var">v~2~</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tfst</span> (<span class="id"
type="var">tpair</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">v~2~</span>)) <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">v~1~</span>\
   | <span class="id" type="var">ST\_Snd</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span>,\
         <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tsnd</span> <span class="id"
type="var">t~1~</span>) <span style="font-family: arial;">⇒</span>
(<span class="id" type="var">tsnd</span> <span class="id"
type="var">t~1~'</span>)\
   | <span class="id" type="var">ST\_SndPair</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">v~2~</span>,\
         <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
         <span class="id" type="var">value</span> <span class="id"
type="var">v~2~</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tsnd</span> (<span class="id"
type="var">tpair</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">v~2~</span>)) <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">v~2~</span>\
   <span class="comment">(\* booleans \*)</span>\
   | <span class="id" type="var">ST\_IfTrue</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
         (<span class="id" type="var">tif</span> <span class="id"
type="var">ttrue</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~</span>\
   | <span class="id" type="var">ST\_IfFalse</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
         (<span class="id" type="var">tif</span> <span class="id"
type="var">tfalse</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~</span>\
   | <span class="id" type="var">ST\_If</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t0</span> <span class="id" type="var">t0'</span> <span
class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
         <span class="id" type="var">t0</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t0'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tif</span> <span class="id"
type="var">t0</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tif</span> <span class="id" type="var">t0'</span> <span
class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>)\
\
 <span class="id" type="keyword">where</span> "t~1~ '<span
style="font-family: arial;">⇒</span>' t~2~" := (<span class="id"
type="var">step</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>).\
\
 <span class="id" type="keyword">Tactic Notation</span> "step\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_AppAbs" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_App1" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "ST\_App2"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Pair1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Pair2"\
     | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Fst" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_FstPair"\
     | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Snd" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_SndPair"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_IfTrue" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_IfFalse" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "ST\_If" ].\
\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">multistep</span> := (<span class="id" type="var">multi</span>
<span class="id" type="var">step</span>).\
 <span class="id" type="keyword">Notation</span> "t~1~ '<span
style="font-family: arial;">⇒\*</span>' t~2~" := (<span class="id"
type="var">multistep</span> <span class="id" type="var">t~1~</span>
<span class="id" type="var">t~2~</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id" type="var">step</span>.\
\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">step\_normal\_form</span> := (<span class="id"
type="var">normal\_form</span> <span class="id"
type="var">step</span>).\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">value\_\_normal</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>, <span class="id" type="var">value</span> <span
class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">step\_normal\_form</span> <span class="id"
type="var">t</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">H</span>; <span
class="id" type="tactic">induction</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">intros</span> [<span
class="id" type="var">t'</span> <span class="id" type="var">ST</span>];
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">ST</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Typing {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">context</span> := <span class="id"
type="var">partial\_map</span> <span class="id" type="var">ty</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">has\_type</span> : <span class="id" type="var">context</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   <span class="comment">(\* Typing rules for proper terms \*)</span>\
   | <span class="id" type="var">T\_Var</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
class="id" type="var">x</span> = <span class="id" type="var">Some</span>
<span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) <span
class="id" type="var">T</span>\
   | <span class="id" type="var">T\_Abs</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T~11~</span> <span
class="id" type="var">T~12~</span> <span class="id"
type="var">t~12~</span>,\
       <span class="id" type="var">has\_type</span> (<span class="id"
type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T~11~</span>) <span
class="id" type="var">t~12~</span> <span class="id"
type="var">T~12~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>) (<span class="id" type="var">TArrow</span>
<span class="id" type="var">T~11~</span> <span class="id"
type="var">T~12~</span>)\
   | <span class="id" type="var">T\_App</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) <span class="id"
type="var">T~2~</span>\
   <span class="comment">(\* pairs \*)</span>\
   | <span class="id" type="var">T\_Pair</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>,\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">T~2~</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tpair</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) (<span class="id"
type="var">TProd</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>)\
   | <span class="id" type="var">T\_Fst</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> (<span class="id" type="var">TProd</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tfst</span> <span class="id" type="var">t</span>) <span
class="id" type="var">T~1~</span>\
   | <span class="id" type="var">T\_Snd</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> (<span class="id" type="var">TProd</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tsnd</span> <span class="id" type="var">t</span>) <span
class="id" type="var">T~2~</span>\
   <span class="comment">(\* booleans \*)</span>\
   | <span class="id" type="var">T\_True</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span>,\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ttrue</span> <span class="id" type="var">TBool</span>\
   | <span class="id" type="var">T\_False</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span>,\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">tfalse</span> <span class="id" type="var">TBool</span>\
   | <span class="id" type="var">T\_If</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t0</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">T</span>,\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t0</span> <span class="id" type="var">TBool</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tif</span> <span class="id" type="var">t0</span> <span
class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>) <span class="id" type="var">T</span>\
 .\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">has\_type</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span>
"has\_type\_cases" <span class="id" type="var">tactic</span>(<span
class="id" type="var">first</span>) <span class="id"
type="var">ident</span>(<span class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Var" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_Abs" | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_App"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Pair" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_Fst" | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Snd"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_True" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_False" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "T\_If" ].\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Extern</span> 2 (<span class="id"
type="var">has\_type</span> <span class="id" type="var">\_</span> (<span
class="id" type="var">tapp</span> <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span>) <span class="id"
type="var">\_</span>) ⇒ <span class="id" type="tactic">eapply</span>
<span class="id" type="var">T\_App</span>; <span class="id"
type="tactic">auto</span>.\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Extern</span> 2 (<span class="id" type="var">\_</span> =
<span class="id" type="var">\_</span>) ⇒ <span class="id"
type="tactic">compute</span>; <span class="id"
type="tactic">reflexivity</span>.\
\

</div>

<div class="doc">

### Context Invariance {.section}

</div>

<div class="code code-space">

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
   <span class="comment">(\* pairs \*)</span>\
   | <span class="id" type="var">afi\_pair1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tpair</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_pair2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tpair</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_fst</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tfst</span>
<span class="id" type="var">t</span>)\
   | <span class="id" type="var">afi\_snd</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tsnd</span>
<span class="id" type="var">t</span>)\
   <span class="comment">(\* booleans \*)</span>\
   | <span class="id" type="var">afi\_if0</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t0</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t0</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif</span>
<span class="id" type="var">t0</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_if1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t0</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif</span>
<span class="id" type="var">t0</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_if2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t0</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif</span>
<span class="id" type="var">t0</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>)\
 .\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">appears\_free\_in</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">closed</span> (<span class="id" type="var">t</span>:<span
class="id" type="var">tm</span>) :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, ¬ <span class="id"
type="var">appears\_free\_in</span> <span class="id" type="var">x</span>
<span class="id" type="var">t</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">context\_invariance</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: serif; font-size:85%;">Γ'</span> <span class="id"
type="var">t</span> <span class="id" type="var">S</span>,\
      <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">S</span> <span
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
      <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ'</span> <span class="id"
type="var">t</span> <span class="id" type="var">S</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ'</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ'</span> <span class="id"
type="var">Heqv</span>...\
   <span class="id" type="var">Case</span> "T\_Var".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Var</span>... <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">Heqv</span>...\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>... <span class="id" type="tactic">apply</span>
<span class="id" type="var">IHhas\_type</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">y</span> <span
class="id" type="var">Hafi</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>. <span class="id" type="tactic">destruct</span>
(<span class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span>)...\
   <span class="id" type="var">Case</span> "T\_Pair".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Pair</span>...\
   <span class="id" type="var">Case</span> "T\_If".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_If</span>...\
 <span class="id" type="keyword">Qed</span>.\
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
    <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
    <span style="font-family: arial;">∃</span><span class="id"
type="var">T'</span>, <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> = <span class="id" type="var">Some</span> <span
class="id" type="var">T'</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">Hafi</span> <span class="id" type="var">Htyp</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Htyp</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hafi</span>;
<span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHtyp</span> <span class="id" type="keyword">as</span>
[<span class="id" type="var">T'</span> <span class="id"
type="var">Hctx</span>]... <span
style="font-family: arial;">∃</span><span class="id"
type="var">T'</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hctx</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">Hctx</span>...\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Corollary</span> <span class="id"
type="var">typable\_empty\_\_closed</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">T</span>,\
     <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">closed</span> <span class="id"
type="var">t</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">closed</span>.
<span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">H1</span>.\
   <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">free\_in\_context</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>
<span class="id" type="var">H1</span> <span class="id"
type="var">H</span>) <span class="id" type="keyword">as</span> [<span
class="id" type="var">T'</span> <span class="id" type="var">C</span>].\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">C</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Preservation {.section}

</div>

<div class="code code-space">

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
   <span
class="comment">(\* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then \
      Gamma |- (<span class="inlinecode"><span class="id"
type="var">x</span>:=<span class="id"
type="var">v</span></span>t) S. \*)</span>\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span> <span
class="id" type="var">v</span> <span class="id" type="var">t</span>
<span class="id" type="var">S</span> <span class="id"
type="var">Htypt</span> <span class="id" type="var">Htypv</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">S</span>.\
   <span
class="comment">(\* Proof: By induction on the term t.  Most cases follow directly\
      from the IH, with the exception of tvar and tabs.\
      The former aren't automatic because we must reason about how the\
      variables interact. \*)</span>\
   <span class="id" type="var">t\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">t</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">S</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">Htypt</span>; <span class="id" type="tactic">simpl</span>;
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">Htypt</span>; <span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "tvar".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rename</span> <span class="id" type="var">i</span> <span
class="id" type="var">into</span> <span class="id" type="var">y</span>.\
     <span class="comment">(\* If t = y, we know that\
          <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">v</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">U</span></span> and\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">S</span></span>\
        and, by inversion, <span class="inlinecode"><span class="id"
type="var">extend</span></span> <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">U</span></span> <span
class="inlinecode"><span class="id" type="var">y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">Some</span></span> <span class="inlinecode"><span class="id"
type="var">S</span></span>.  We want to\
        show that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">y</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">S</span></span>.\
\
        There are two cases to consider: either <span
class="inlinecode"><span class="id" type="var">x</span>=<span class="id"
type="var">y</span></span> or <span class="inlinecode"><span class="id"
type="var">x</span>≠<span class="id"
type="var">y</span></span>. \*)</span>\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>).\
     <span class="id" type="var">SCase</span> "x=y".\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">y</span></span>, then we know that <span
class="inlinecode"><span class="id" type="var">U</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">S</span></span>, and that <span class="inlinecode">[<span
class="id" type="var">x</span>:=<span class="id"
type="var">v</span>]<span class="id" type="var">y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">v</span></span>.\
        So what we really must show is that if <span
class="inlinecode"><span class="id" type="var">empty</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">v</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">U</span></span> then\
        <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">v</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id"
type="var">U</span></span>.  We have already proven a more general version\
        of this theorem, called context invariance. \*)</span>\
       <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H1</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">eq\_id</span>
<span class="id" type="keyword">in</span> <span class="id"
type="var">H1</span>.\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H1</span>; <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H1</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>...\
       <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">Hcontra</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">free\_in\_context</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">S</span> <span class="id" type="var">empty</span>
<span class="id" type="var">Hcontra</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">T'</span> <span
class="id" type="var">HT'</span>]...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT'</span>.\
     <span class="id" type="var">SCase</span> "x≠y".\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">≠</span>
<span class="inlinecode"><span class="id"
type="var">y</span></span>, then <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span class="id" type="var">y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">Some</span></span> <span class="inlinecode"><span class="id"
type="var">S</span></span> and the substitution has no\
        effect.  We can show that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">S</span></span> by <span class="inlinecode"><span
class="id" type="var">T\_Var</span></span>. \*)</span>\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Var</span>... <span class="id" type="tactic">unfold</span>
<span class="id" type="var">extend</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H1</span>. <span
class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H1</span>...\
   <span class="id" type="var">Case</span> "tabs".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y</span>. <span class="id"
type="tactic">rename</span> <span class="id" type="var">t</span> <span
class="id" type="var">into</span> <span class="id"
type="var">T~11~</span>.\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">tabs</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span>
<span class="inlinecode"><span class="id" type="var">T~11~</span></span>
<span class="inlinecode"><span class="id"
type="var">t0</span></span>, then we know that\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">tabs</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span>
<span class="inlinecode"><span class="id" type="var">T~11~</span></span>
<span class="inlinecode"><span class="id" type="var">t0</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T~11~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T~12~</span></span>\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span>,<span
class="id" type="var">y</span>:<span class="id"
type="var">T~11~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~12~</span></span>\
          <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">v</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">U</span></span>\
        As our IH, we know that forall S Gamma, \
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t0</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">S</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t0</span></span> <span class="inlinecode"><span class="id"
type="var">S</span></span>.\
     \
        We can calculate that \
          <span class="inlinecode"><span class="id"
type="var">x</span>:=<span class="id"
type="var">v</span></span>t = tabs y T~11~ (if beq\_id x y then t0 else <span
class="inlinecode"><span class="id" type="var">x</span>:=<span
class="id" type="var">v</span></span>t0)\
        And we must show that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">T~11~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T~12~</span></span>.  We know\
        we will do so using <span class="inlinecode"><span class="id"
type="var">T\_Abs</span></span>, so it remains to be shown that:\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span></span>
<span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="keyword">if</span></span>
<span class="inlinecode"><span class="id"
type="var">beq\_id</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="var">y</span></span> <span class="inlinecode"><span
class="id" type="keyword">then</span></span> <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode"><span class="id" type="keyword">else</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t0</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">T~12~</span></span>\
        We consider two cases: <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">y</span></span> and <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode">≠</span> <span class="inlinecode"><span class="id"
type="var">y</span></span>.\
     \*)</span>\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>...\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>).\
     <span class="id" type="var">SCase</span> "x=y".\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">y</span></span>, then the substitution has no effect.  Context\
        invariance shows that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">U</span>,<span
class="id" type="var">y</span>:<span class="id"
type="var">T~11~</span></span> and <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span></span> are\
        equivalent.  Since the former context shows that <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~12~</span></span>, so\
        does the latter. \*)</span>\
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
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">≠</span>
<span class="inlinecode"><span class="id"
type="var">y</span></span>, then the IH and context invariance allow us to show that\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span>,<span
class="id" type="var">y</span>:<span class="id"
type="var">T~11~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~12~</span></span>       =\>\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span>,<span
class="id" type="var">x</span>:<span class="id"
type="var">U</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~12~</span></span>       =\>\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span></span>
<span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t0</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id"
type="var">T~12~</span></span> \*)</span>\
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
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">t'</span> <span
class="id" type="var">T</span> <span class="id" type="var">HT</span>.\
   <span class="comment">(\* Theorem: If <span class="inlinecode"><span
class="id" type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span> and <span class="inlinecode"><span class="id"
type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id"
type="var">t'</span></span>, then <span class="inlinecode"><span
class="id" type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>. \*)</span>\
   <span class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id"
type="var">HeqGamma</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">t'</span>.\
   <span
class="comment">(\* Proof: By induction on the given typing derivation.  Many cases are\
      contradictory (<span class="inlinecode"><span class="id"
type="var">T\_Var</span></span>, <span class="inlinecode"><span
class="id"
type="var">T\_Abs</span></span>).  We show just the interesting ones. \*)</span>\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">HT</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">t'</span> <span class="id" type="var">HeqGamma</span> <span
class="id" type="var">HE</span>; <span class="id"
type="tactic">subst</span>; <span class="id"
type="tactic">inversion</span> <span class="id" type="var">HE</span>;
<span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="comment">(\* If the last rule used was <span
class="inlinecode"><span class="id"
type="var">T\_App</span></span>, then <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">t~1~</span></span>
<span class="inlinecode"><span class="id"
type="var">t~2~</span></span>, and three rules\
        could have been used to show <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span>: <span
class="inlinecode"><span class="id"
type="var">ST\_App1</span></span>, <span class="inlinecode"><span
class="id" type="var">ST\_App2</span></span>, and \
        <span class="inlinecode"><span class="id"
type="var">ST\_AppAbs</span></span>. In the first two cases, the result follows directly from \
        the IH. \*)</span>\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">SCase</span> "ST\_AppAbs".\
       <span class="comment">(\* For the third case, suppose \
            <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">tabs</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">T~11~</span></span> <span
class="inlinecode"><span class="id" type="var">t~12~</span></span>\
          and\
            <span class="inlinecode"><span class="id"
type="var">t~2~</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">v~2~</span></span>.  \
          We must show that <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v~2~</span>]<span class="id"
type="var">t~12~</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">T~2~</span></span>. \
          We know by assumption that\
              <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">tabs</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">T~11~</span></span> <span
class="inlinecode"><span class="id" type="var">t~12~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~1~</span><span style="font-family: arial;">→</span><span
class="id" type="var">T~2~</span></span>\
          and by inversion\
              <span class="inlinecode"><span class="id"
type="var">x</span>:<span class="id" type="var">T~1~</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t~12~</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T~2~</span></span>\

         We have already proven that substitution\_preserves\_typing and \
              <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">v~2~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~1~</span></span>\
          by assumption, so we are done. \*)</span>\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">substitution\_preserves\_typing</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">T~1~</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT1</span>...\
   <span class="id" type="var">Case</span> "T\_Fst".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT</span>...\
   <span class="id" type="var">Case</span> "T\_Snd".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT</span>...\
 <span class="id" type="keyword">Qed</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Determinism {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_deterministic</span> :\
    <span class="id" type="var">deterministic</span> <span class="id"
type="var">step</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
    <span class="id" type="tactic">unfold</span> <span class="id"
type="var">deterministic</span>.\
    <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Normalization {.section}
=============

<div class="paragraph">

</div>

Now for the actual normalization proof.
<div class="paragraph">

</div>

Our goal is to prove that every well-typed term evaluates to a normal
form. In fact, it turns out to be convenient to prove something slightly
stronger, namely that every well-typed term evaluates to a *value*. This
follows from the weaker property anyway via the Progress lemma (why?)
but otherwise we don't need Progress, and we didn't bother re-proving it
above.
<div class="paragraph">

</div>

Here's the key definition:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">halts</span> (<span class="id" type="var">t</span>:<span
class="id" type="var">tm</span>) : <span class="id"
type="keyword">Prop</span> := <span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>, <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">t'</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">value</span> <span class="id"
type="var">t'</span>.\
\

</div>

<div class="doc">

A trivial fact:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">value\_halts</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v</span>, <span class="id" type="var">value</span> <span
class="id" type="var">v</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">halts</span> <span class="id" type="var">v</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">v</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">halts</span>.\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">v</span>. <span class="id" type="tactic">split</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>.\
   <span class="id" type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The key issue in the normalization proof (as in many proofs by
induction) is finding a strong enough induction hypothesis. To this end,
we begin by defining, for each type <span class="inlinecode"><span
class="id" type="var">T</span></span>, a set <span
class="inlinecode"><span class="id" type="var">R\_T</span></span> of
closed terms of type <span class="inlinecode"><span class="id"
type="var">T</span></span>. We will specify these sets using a relation
<span class="inlinecode"><span class="id" type="var">R</span></span> and
write <span class="inlinecode"><span class="id"
type="var">R</span></span> <span class="inlinecode"><span class="id"
type="var">T</span></span> <span class="inlinecode"><span class="id"
type="var">t</span></span> when <span class="inlinecode"><span
class="id" type="var">t</span></span> is in <span
class="inlinecode"><span class="id" type="var">R\_T</span></span>. (The
sets <span class="inlinecode"><span class="id"
type="var">R\_T</span></span> are sometimes called *saturated sets* or
*reducibility candidates*.)
<div class="paragraph">

</div>

Here is the definition of <span class="inlinecode"><span class="id"
type="var">R</span></span> for the base language:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">R</span></span>
    <span class="inlinecode"><span class="id"
    type="var">bool</span></span> <span class="inlinecode"><span
    class="id" type="var">t</span></span> iff <span
    class="inlinecode"><span class="id" type="var">t</span></span> is a
    closed term of type <span class="inlinecode"><span class="id"
    type="var">bool</span></span> and <span class="inlinecode"><span
    class="id" type="var">t</span></span> halts in a value
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id" type="var">R</span></span>
    <span class="inlinecode">(<span class="id"
    type="var">T~1~</span></span> <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">T~2~</span>)</span>
    <span class="inlinecode"><span class="id" type="var">t</span></span>
    iff <span class="inlinecode"><span class="id"
    type="var">t</span></span> is a closed term of type <span
    class="inlinecode"><span class="id" type="var">T~1~</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">T~2~</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">t</span></span> halts in a value *and* for any term <span
    class="inlinecode"><span class="id" type="var">s</span></span> such
    that <span class="inlinecode"><span class="id"
    type="var">R</span></span> <span class="inlinecode"><span class="id"
    type="var">T~1~</span></span> <span class="inlinecode"><span
    class="id" type="var">s</span></span>, we have <span
    class="inlinecode"><span class="id" type="var">R</span></span> <span
    class="inlinecode"><span class="id" type="var">T~2~</span></span>
    <span class="inlinecode">(<span class="id"
    type="var">t</span></span> <span class="inlinecode"><span class="id"
    type="var">s</span>)</span>.

<div class="paragraph">

</div>

This definition gives us the strengthened induction hypothesis that we
need. Our primary goal is to show that all *programs* —-i.e., all closed
terms of base type—-halt. But closed terms of base type can contain
subterms of functional type, so we need to know something about these as
well. Moreover, it is not enough to know that these subterms halt,
because the application of a normalized function to a normalized
argument involves a substitution, which may enable more evaluation
steps. So we need a stronger condition for terms of functional type: not
only should they halt themselves, but, when applied to halting
arguments, they should yield halting results.
<div class="paragraph">

</div>

The form of <span class="inlinecode"><span class="id"
type="var">R</span></span> is characteristic of the *logical relations*
proof technique. (Since we are just dealing with unary relations here,
we could perhaps more properly say *logical predicates*.) If we want to
prove some property <span class="inlinecode"><span class="id"
type="var">P</span></span> of all closed terms of type <span
class="inlinecode"><span class="id" type="var">A</span></span>, we
proceed by proving, by induction on types, that all terms of type <span
class="inlinecode"><span class="id" type="var">A</span></span> *possess*
property <span class="inlinecode"><span class="id"
type="var">P</span></span>, all terms of type <span
class="inlinecode"><span class="id" type="var">A</span><span
style="font-family: arial;">→</span><span class="id"
type="var">A</span></span> *preserve* property <span
class="inlinecode"><span class="id" type="var">P</span></span>, all
terms of type <span class="inlinecode">(<span class="id"
type="var">A</span><span style="font-family: arial;">→</span><span
class="id" type="var">A</span>)-\>(<span class="id"
type="var">A</span><span style="font-family: arial;">→</span><span
class="id" type="var">A</span>)</span> *preserve the property of
preserving* property <span class="inlinecode"><span class="id"
type="var">P</span></span>, and so on. We do this by defining a family
of predicates, indexed by types. For the base type <span
class="inlinecode"><span class="id" type="var">A</span></span>, the
predicate is just <span class="inlinecode"><span class="id"
type="var">P</span></span>. For functional types, it says that the
function should map values satisfying the predicate at the input type to
values satisfying the predicate at the output type.
<div class="paragraph">

</div>

When we come to formalize the definition of <span
class="inlinecode"><span class="id" type="var">R</span></span> in Coq,
we hit a problem. The most obvious formulation would be as a
parameterized Inductive proposition like this:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

<span class="id" type="keyword">Inductive</span> <span class="id"
type="var">R</span> : <span class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
 | <span class="id" type="var">R\_bool</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">b</span> <span class="id" type="var">t</span>, <span
class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t</span> <span
class="id" type="var">TBool</span> <span
style="font-family: arial;">→</span> \
                 <span class="id" type="var">halts</span> <span
class="id" type="var">t</span> <span
style="font-family: arial;">→</span> \
                 <span class="id" type="var">R</span> <span class="id"
type="var">TBool</span> <span class="id" type="var">t</span>\
 | <span class="id" type="var">R\_arrow</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> <span
class="id" type="var">t</span>, <span class="id"
type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t</span> (<span
class="id" type="var">TArrow</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span>) <span
style="font-family: arial;">→</span> \
                 <span class="id" type="var">halts</span> <span
class="id" type="var">t</span> <span
style="font-family: arial;">→</span> \
                 (<span style="font-family: arial;">∀</span><span
class="id" type="var">s</span>, <span class="id"
type="var">R</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">s</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">T~2~</span> (<span
class="id" type="var">tapp</span> <span class="id"
type="var">t</span> <span class="id" type="var">s</span>)) <span
style="font-family: arial;">→</span> \
                 <span class="id" type="var">R</span> (<span class="id"
type="var">TArrow</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>) <span class="id" type="var">t</span>.
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Unfortunately, Coq rejects this definition because it violates the
*strict positivity requirement* for inductive definitions, which says
that the type being defined must not occur to the left of an arrow in
the type of a constructor argument. Here, it is the third argument to
<span class="inlinecode"><span class="id"
type="var">R\_arrow</span></span>, namely <span
class="inlinecode">(<span style="font-family: arial;">∀</span></span>
<span class="inlinecode"><span class="id" type="var">s</span>,</span>
<span class="inlinecode"><span class="id" type="var">R</span></span>
<span class="inlinecode"><span class="id" type="var">T~1~</span></span>
<span class="inlinecode"><span class="id" type="var">s</span></span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">R</span></span> <span
class="inlinecode"><span class="id" type="var">TS</span></span> <span
class="inlinecode">(<span class="id" type="var">tapp</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode"><span class="id" type="var">s</span>))</span>, and
specifically the <span class="inlinecode"><span class="id"
type="var">R</span></span> <span class="inlinecode"><span class="id"
type="var">T~1~</span></span> <span class="inlinecode"><span class="id"
type="var">s</span></span> part, that violates this rule. (The outermost
arrows separating the constructor arguments don't count when applying
this rule; otherwise we could never have genuinely inductive predicates
at all!) The reason for the rule is that types defined with non-positive
recursion can be used to build non-terminating functions, which as we
know would be a disaster for Coq's logical soundness. Even though the
relation we want in this case might be perfectly innocent, Coq still
rejects it because it fails the positivity test.
<div class="paragraph">

</div>

Fortunately, it turns out that we *can* define <span
class="inlinecode"><span class="id" type="var">R</span></span> using a
<span class="inlinecode"><span class="id"
type="keyword">Fixpoint</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">R</span> (<span class="id" type="var">T</span>:<span
class="id" type="var">ty</span>) (<span class="id"
type="var">t</span>:<span class="id" type="var">tm</span>) {<span
class="id" type="keyword">struct</span> <span class="id"
type="var">T</span>} : <span class="id" type="keyword">Prop</span> :=\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">halts</span> <span class="id" type="var">t</span> <span
style="font-family: arial;">∧</span>\
   (<span class="id" type="keyword">match</span> <span class="id"
type="var">T</span> <span class="id" type="keyword">with</span>\
    | <span class="id" type="var">TBool</span> ⇒ <span class="id"
type="var">True</span>\
    | <span class="id" type="var">TArrow</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> ⇒ (<span
style="font-family: arial;">∀</span><span class="id"
type="var">s</span>, <span class="id" type="var">R</span> <span
class="id" type="var">T~1~</span> <span class="id" type="var">s</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">T~2~</span> (<span
class="id" type="var">tapp</span> <span class="id" type="var">t</span>
<span class="id" type="var">s</span>))\
 <span class="comment">(\* FILL IN HERE \*)</span>\
    | <span class="id" type="var">TProd</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> ⇒ <span
class="id" type="var">False</span> <span
class="comment">(\* ... and delete this line \*)</span>\
    <span class="id" type="keyword">end</span>).\
\

</div>

<div class="doc">

As immediate consequences of this definition, we have that every element
of every set <span class="inlinecode"><span class="id"
type="var">R\_T</span></span> halts in a value and is closed with type
<span class="inlinecode"><span class="id" type="var">t</span></span> :

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">R\_halts</span> : <span
style="font-family: arial;">∀</span>{<span class="id"
type="var">T</span>} {<span class="id" type="var">t</span>}, <span
class="id" type="var">R</span> <span class="id" type="var">T</span>
<span class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">halts</span> <span class="id" type="var">t</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">T</span>;
<span class="id" type="tactic">unfold</span> <span class="id"
type="var">R</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H</span>; <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>;
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">H1</span>; <span class="id" type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">R\_typable\_empty</span> : <span
style="font-family: arial;">∀</span>{<span class="id"
type="var">T</span>} {<span class="id" type="var">t</span>}, <span
class="id" type="var">R</span> <span class="id" type="var">T</span>
<span class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">has\_type</span> <span class="id" type="var">empty</span>
<span class="id" type="var">t</span> <span class="id"
type="var">T</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">T</span>;
<span class="id" type="tactic">unfold</span> <span class="id"
type="var">R</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H</span>; <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>;
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">H1</span>; <span class="id" type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Now we proceed to show the main result, which is that every well-typed
term of type <span class="inlinecode"><span class="id"
type="var">T</span></span> is an element of <span
class="inlinecode"><span class="id" type="var">R\_T</span></span>.
Together with <span class="inlinecode"><span class="id"
type="var">R\_halts</span></span>, that will show that every well-typed
term halts in a value.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Membership in <span class="inlinecode"><span class="id" type="var">R\_T</span></span> is invariant under evaluation {.section}
-------------------------------------------------------------------------------------------------------------------

<div class="paragraph">

</div>

We start with a preliminary lemma that shows a kind of strong
preservation property, namely that membership in <span
class="inlinecode"><span class="id" type="var">R\_T</span></span> is
*invariant* under evaluation. We will need this property in both
directions, i.e. both to show that a term in <span
class="inlinecode"><span class="id" type="var">R\_T</span></span> stays
in <span class="inlinecode"><span class="id"
type="var">R\_T</span></span> when it takes a forward step, and to show
that any term that ends up in <span class="inlinecode"><span class="id"
type="var">R\_T</span></span> after a step must have been in <span
class="inlinecode"><span class="id" type="var">R\_T</span></span> to
begin with.
<div class="paragraph">

</div>

First of all, an easy preliminary lemma. Note that in the forward
direction the proof depends on the fact that our language is
determinstic. This lemma might still be true for non-deterministic
languages, but the proof would be harder!

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_preserves\_halting</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">t'</span>, (<span class="id"
type="var">t</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t'</span>) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">halts</span> <span class="id" type="var">t</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">halts</span> <span class="id" type="var">t'</span>).\
 <span class="id" type="keyword">Proof</span>.\
  <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">t'</span> <span
class="id" type="var">ST</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">halts</span>.\
  <span class="id" type="tactic">split</span>.\
  <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
   <span class="id" type="tactic">intros</span> [<span class="id"
type="var">t''</span> [<span class="id" type="var">STM</span> <span
class="id" type="var">V</span>]].\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">STM</span>; <span class="id" type="tactic">subst</span>.\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">ex\_falso\_quodlibet</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">value\_\_normal</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">V</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">normal\_form</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">V</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">V</span>. <span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>. <span class="id" type="tactic">auto</span>.\
    <span class="id" type="tactic">rewrite</span> (<span class="id"
type="var">step\_deterministic</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">ST</span>
<span class="id" type="var">H</span>). <span
style="font-family: arial;">∃</span><span class="id"
type="var">t''</span>. <span class="id" type="tactic">split</span>;
<span class="id" type="tactic">assumption</span>.\
  <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
   <span class="id" type="tactic">intros</span> [<span class="id"
type="var">t'0</span> [<span class="id" type="var">STM</span> <span
class="id" type="var">V</span>]].\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">t'0</span>. <span class="id" type="tactic">split</span>;
<span class="id" type="tactic">eauto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Now the main lemma, which comes in two parts, one for each direction.
Each proceeds by induction on the structure of the type <span
class="inlinecode"><span class="id" type="var">T</span></span>. In fact,
this is where we make fundamental use of the structure of types.
<div class="paragraph">

</div>

One requirement for staying in <span class="inlinecode"><span class="id"
type="var">R\_T</span></span> is to stay in type <span
class="inlinecode"><span class="id" type="var">T</span></span>. In the
forward direction, we get this from ordinary type Preservation.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_preserves\_R</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">T</span>
<span class="id" type="var">t</span> <span class="id"
type="var">t'</span>, (<span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">R</span> <span class="id" type="var">T</span>
<span class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">T</span> <span
class="id" type="var">t'</span>.\
 <span class="id" type="keyword">Proof</span>.\
  <span class="id" type="tactic">induction</span> <span class="id"
type="var">T</span>; <span class="id" type="tactic">intros</span> <span
class="id" type="var">t</span> <span class="id" type="var">t'</span>
<span class="id" type="var">E</span> <span class="id"
type="var">Rt</span>; <span class="id" type="tactic">unfold</span> <span
class="id" type="var">R</span>; <span class="id" type="var">fold</span>
<span class="id" type="var">R</span>; <span class="id"
type="tactic">unfold</span> <span class="id" type="var">R</span> <span
class="id" type="keyword">in</span> <span class="id"
type="var">Rt</span>; <span class="id" type="var">fold</span> <span
class="id" type="var">R</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">Rt</span>;\
                <span class="id" type="tactic">destruct</span> <span
class="id" type="var">Rt</span> <span class="id"
type="keyword">as</span> [<span class="id"
type="var">typable\_empty\_t</span> [<span class="id"
type="var">halts\_t</span> <span class="id" type="var">RRt</span>]].\
   <span class="comment">(\* TBool \*)</span>\
   <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">preservation</span>; <span class="id"
type="tactic">eauto</span>.\
   <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">apply</span> (<span class="id"
type="var">step\_preserves\_halting</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">E</span>); <span class="id"
type="tactic">eauto</span>.\
   <span class="id" type="tactic">auto</span>.\
   <span class="comment">(\* TArrow \*)</span>\
   <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">preservation</span>; <span class="id"
type="tactic">eauto</span>.\
   <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">apply</span> (<span class="id"
type="var">step\_preserves\_halting</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">E</span>); <span class="id"
type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHT2</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_App1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">E</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">RRt</span>; <span class="id" type="tactic">auto</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

The generalization to multiple steps is trivial:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">multistep\_preserves\_R</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">T</span>
<span class="id" type="var">t</span> <span class="id"
type="var">t'</span>,\
   (<span class="id" type="var">t</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">t'</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">R</span> <span class="id" type="var">T</span>
<span class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">T</span> <span
class="id" type="var">t'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">T</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span> <span class="id" type="var">STM</span>;
<span class="id" type="tactic">induction</span> <span class="id"
type="var">STM</span>; <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">assumption</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHSTM</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">step\_preserves\_R</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

In the reverse direction, we must add the fact that <span
class="inlinecode"><span class="id" type="var">t</span></span> has type
<span class="inlinecode"><span class="id" type="var">T</span></span>
before stepping as an additional hypothesis.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_preserves\_R'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">T</span>
<span class="id" type="var">t</span> <span class="id"
type="var">t'</span>,\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span> (<span class="id"
type="var">t</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t'</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">T</span> <span
class="id" type="var">t'</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">T</span> <span
class="id" type="var">t</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">multistep\_preserves\_R'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">T</span>
<span class="id" type="var">t</span> <span class="id"
type="var">t'</span>,\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span> (<span class="id"
type="var">t</span> <span style="font-family: arial;">⇒\*</span> <span
class="id" type="var">t'</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">T</span> <span
class="id" type="var">t'</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">T</span> <span
class="id" type="var">t</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">T</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span> <span class="id" type="var">HT</span>
<span class="id" type="var">STM</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">STM</span>; <span class="id" type="tactic">intros</span>.\
     <span class="id" type="tactic">assumption</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">step\_preserves\_R'</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">IHSTM</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">preservation</span>; <span class="id"
type="tactic">eauto</span>. <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Closed instances of terms of type <span class="inlinecode"><span class="id" type="var">T</span></span> belong to <span class="inlinecode"><span class="id" type="var">R\_T</span></span> {.section}
----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

<div class="paragraph">

</div>

Now we proceed to show that every term of type <span
class="inlinecode"><span class="id" type="var">T</span></span> belongs
to <span class="inlinecode"><span class="id"
type="var">R\_T</span></span>. Here, the induction will be on typing
derivations (it would be surprising to see a proof about well-typed
terms that did not somewhere involve induction on typing derivations!).
The only technical difficulty here is in dealing with the abstraction
case. Since we are arguing by induction, the demonstration that a term
<span class="inlinecode"><span class="id" type="var">tabs</span></span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode"><span class="id" type="var">T~1~</span></span>
<span class="inlinecode"><span class="id" type="var">t~2~</span></span>
belongs to <span class="inlinecode"><span class="id"
type="var">R\_</span>(<span class="id" type="var">T~1~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T~2~</span>)</span> should involve applying the induction
hypothesis to show that <span class="inlinecode"><span class="id"
type="var">t~2~</span></span> belongs to <span class="inlinecode"><span
class="id" type="var">R\_</span>(<span class="id"
type="var">T~2~</span>)</span>. But <span class="inlinecode"><span
class="id" type="var">R\_</span>(<span class="id"
type="var">T~2~</span>)</span> is defined to be a set of *closed* terms,
while <span class="inlinecode"><span class="id"
type="var">t~2~</span></span> may contain <span class="inlinecode"><span
class="id" type="var">x</span></span> free, so this does not make sense.
<div class="paragraph">

</div>

This problem is resolved by using a standard trick to suitably
generalize the induction hypothesis: instead of proving a statement
involving a closed term, we generalize it to cover all closed
*instances* of an open term <span class="inlinecode"><span class="id"
type="var">t</span></span>. Informally, the statement of the lemma will
look like this:
<div class="paragraph">

</div>

If <span class="inlinecode"><span class="id" type="var">x1</span>:<span
class="id" type="var">T~1~</span>,..<span class="id"
type="var">xn</span>:<span class="id" type="var">Tn</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T</span></span> and <span class="inlinecode"><span
class="id" type="var">v~1~</span>,...,<span class="id"
type="var">vn</span></span> are values such that <span
class="inlinecode"><span class="id" type="var">R</span></span> <span
class="inlinecode"><span class="id" type="var">T~1~</span></span> <span
class="inlinecode"><span class="id" type="var">v~1~</span></span>, <span
class="inlinecode"><span class="id" type="var">R</span></span> <span
class="inlinecode"><span class="id" type="var">T~2~</span></span> <span
class="inlinecode"><span class="id" type="var">v~2~</span></span>, ...,
<span class="inlinecode"><span class="id" type="var">R</span></span>
<span class="inlinecode"><span class="id" type="var">Tn</span></span>
<span class="inlinecode"><span class="id" type="var">vn</span></span>,
then <span class="inlinecode"><span class="id"
type="var">R</span></span> <span class="inlinecode"><span class="id"
type="var">T</span></span> <span class="inlinecode">([<span class="id"
type="var">x1</span>:=<span class="id" type="var">v~1~</span>][<span
class="id" type="var">x2</span>:=<span class="id"
type="var">v~2~</span>]...[<span class="id" type="var">xn</span>:=<span
class="id" type="var">vn</span>]<span class="id"
type="var">t</span>)</span>.
<div class="paragraph">

</div>

The proof will proceed by induction on the typing derivation <span
class="inlinecode"><span class="id" type="var">x1</span>:<span
class="id" type="var">T~1~</span>,..<span class="id"
type="var">xn</span>:<span class="id" type="var">Tn</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>; the most interesting case will be
the one for abstraction.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Multisubstitutions, multi-extensions, and instantiations {.section}

<div class="paragraph">

</div>

However, before we can proceed to formalize the statement and proof of
the lemma, we'll need to build some (rather tedious) machinery to deal
with the fact that we are performing *multiple* substitutions on term
<span class="inlinecode"><span class="id" type="var">t</span></span> and
*multiple* extensions of the typing context. In particular, we must be
precise about the order in which the substitutions occur and how they
act on each other. Often these details are simply elided in informal
paper proofs, but of course Coq won't let us do that. Since here we are
substituting closed terms, we don't need to worry about how one
substitution might affect the term put in place by another. But we still
do need to worry about the *order* of substitutions, because it is quite
possible for the same identifier to appear multiple times among the
<span class="inlinecode"><span class="id" type="var">x1</span>,...<span
class="id" type="var">xn</span></span> with different associated <span
class="inlinecode"><span class="id" type="var">vi</span></span> and
<span class="inlinecode"><span class="id" type="var">Ti</span></span>.
<div class="paragraph">

</div>

To make everything precise, we will assume that environments are
extended from left to right, and multiple substitutions are performed
from right to left. To see that this is consistent, suppose we have an
environment written as <span class="inlinecode">...,<span class="id"
type="var">y</span>:<span class="id" type="var">bool</span>,...,<span
class="id" type="var">y</span>:<span class="id"
type="var">nat</span>,...</span> and a corresponding term substitution
written as <span class="inlinecode">...[<span class="id"
type="var">y</span>:=(<span class="id" type="var">tbool</span></span>
<span class="inlinecode"><span class="id"
type="var">true</span>)]...[<span class="id" type="var">y</span>:=(<span
class="id" type="var">tnat</span></span> <span
class="inlinecode">3)]...<span class="id" type="var">t</span></span>.
Since environments are extended from left to right, the binding <span
class="inlinecode"><span class="id" type="var">y</span>:<span class="id"
type="var">nat</span></span> hides the binding <span
class="inlinecode"><span class="id" type="var">y</span>:<span class="id"
type="var">bool</span></span>; since substitutions are performed right
to left, we do the substitution <span class="inlinecode"><span
class="id" type="var">y</span>:=(<span class="id"
type="var">tnat</span></span> <span class="inlinecode">3)</span> first,
so that the substitution <span class="inlinecode"><span class="id"
type="var">y</span>:=(<span class="id" type="var">tbool</span></span>
<span class="inlinecode"><span class="id" type="var">true</span>)</span>
has no effect. Substitution thus correctly preserves the type of the
term.
<div class="paragraph">

</div>

With these points in mind, the following definitions should make sense.
<div class="paragraph">

</div>

A *multisubstitution* is the result of applying a list of substitutions,
which we call an *environment*.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">env</span> := <span class="id" type="var">list</span> (<span
class="id" type="var">id</span> × <span class="id"
type="var">tm</span>).\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">msubst</span> (<span class="id" type="var">ss</span>:<span
class="id" type="var">env</span>) (<span class="id"
type="var">t</span>:<span class="id" type="var">tm</span>) {<span
class="id" type="keyword">struct</span> <span class="id"
type="var">ss</span>} : <span class="id" type="var">tm</span> :=\
 <span class="id" type="keyword">match</span> <span class="id"
type="var">ss</span> <span class="id" type="keyword">with</span>\
 | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">t</span>\
 | ((<span class="id" type="var">x</span>,<span class="id"
type="var">s</span>)::<span class="id" type="var">ss'</span>) ⇒ <span
class="id" type="var">msubst</span> <span class="id"
type="var">ss'</span> ([<span class="id" type="var">x</span>:=<span
class="id" type="var">s</span>]<span class="id" type="var">t</span>)\
 <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

We need similar machinery to talk about repeated extension of a typing
context using a list of (identifier, type) pairs, which we call a *type
assignment*.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">tass</span> := <span class="id" type="var">list</span> (<span
class="id" type="var">id</span> × <span class="id"
type="var">ty</span>).\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">mextend</span> (<span
style="font-family: serif; font-size:85%;">Γ</span> : <span class="id"
type="var">context</span>) (<span class="id" type="var">xts</span> :
<span class="id" type="var">tass</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">xts</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span
style="font-family: serif; font-size:85%;">Γ</span>\
   | ((<span class="id" type="var">x</span>,<span class="id"
type="var">v</span>)::<span class="id" type="var">xts'</span>) ⇒ <span
class="id" type="var">extend</span> (<span class="id"
type="var">mextend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">xts'</span>) <span class="id" type="var">x</span> <span
class="id" type="var">v</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

We will need some simple operations that work uniformly on environments
and type assigments

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">lookup</span> {<span class="id" type="var">X</span>:<span
class="id" type="keyword">Set</span>} (<span class="id"
type="var">k</span> : <span class="id" type="var">id</span>) (<span
class="id" type="var">l</span> : <span class="id" type="var">list</span>
(<span class="id" type="var">id</span> × <span class="id"
type="var">X</span>)) {<span class="id" type="keyword">struct</span>
<span class="id" type="var">l</span>} : <span class="id"
type="var">option</span> <span class="id" type="var">X</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
     | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">None</span>\
     | (<span class="id" type="var">j</span>,<span class="id"
type="var">x</span>) :: <span class="id" type="var">l'</span> ⇒\
       <span class="id" type="keyword">if</span> <span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">j</span> <span
class="id" type="var">k</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">Some</span> <span
class="id" type="var">x</span> <span class="id"
type="keyword">else</span> <span class="id" type="var">lookup</span>
<span class="id" type="var">k</span> <span class="id"
type="var">l'</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">drop</span> {<span class="id" type="var">X</span>:<span
class="id" type="keyword">Set</span>} (<span class="id"
type="var">n</span>:<span class="id" type="var">id</span>) (<span
class="id" type="var">nxs</span>:<span class="id" type="var">list</span>
(<span class="id" type="var">id</span> × <span class="id"
type="var">X</span>)) {<span class="id" type="keyword">struct</span>
<span class="id" type="var">nxs</span>} : <span class="id"
type="var">list</span> (<span class="id" type="var">id</span> × <span
class="id" type="var">X</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">nxs</span> <span class="id" type="keyword">with</span>\
     | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">nil</span>\
     | ((<span class="id" type="var">n'</span>,<span class="id"
type="var">x</span>)::<span class="id" type="var">nxs'</span>) ⇒ <span
class="id" type="keyword">if</span> <span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">n'</span>
<span class="id" type="var">n</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">drop</span> <span
class="id" type="var">n</span> <span class="id" type="var">nxs'</span>
<span class="id" type="keyword">else</span> (<span class="id"
type="var">n'</span>,<span class="id" type="var">x</span>)::(<span
class="id" type="var">drop</span> <span class="id" type="var">n</span>
<span class="id" type="var">nxs'</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

An *instantiation* combines a type assignment and a value environment
with the same domains, where corresponding elements are in R

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">instantiation</span> : <span class="id"
type="var">tass</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">env</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
 | <span class="id" type="var">V\_nil</span> : <span class="id"
type="var">instantiation</span> <span class="id" type="var">nil</span>
<span class="id" type="var">nil</span>\
 | <span class="id" type="var">V\_cons</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">T</span> <span class="id"
type="var">v</span> <span class="id" type="var">c</span> <span
class="id" type="var">e</span>, <span class="id" type="var">value</span>
<span class="id" type="var">v</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">T</span> <span
class="id" type="var">v</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">instantiation</span> <span class="id" type="var">c</span>
<span class="id" type="var">e</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">instantiation</span> ((<span class="id"
type="var">x</span>,<span class="id" type="var">T</span>)::<span
class="id" type="var">c</span>) ((<span class="id"
type="var">x</span>,<span class="id" type="var">v</span>)::<span
class="id" type="var">e</span>).\
\

</div>

<div class="doc">

We now proceed to prove various properties of these definitions.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### More Substitution Facts {.section}

<div class="paragraph">

</div>

First we need some additional lemmas on (ordinary) substitution.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">vacuous\_substitution</span> : <span
style="font-family: arial;">∀</span> <span class="id"
type="var">t</span> <span class="id" type="var">x</span>,\
      ¬ <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
      <span style="font-family: arial;">∀</span><span class="id"
type="var">t'</span>, [<span class="id" type="var">x</span>:=<span
class="id" type="var">t'</span>]<span class="id" type="var">t</span> =
<span class="id" type="var">t</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">subst\_closed</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>,\
      <span class="id" type="var">closed</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">→</span>\
      <span style="font-family: arial;">∀</span><span class="id"
type="var">x</span> <span class="id" type="var">t'</span>, [<span
class="id" type="var">x</span>:=<span class="id"
type="var">t'</span>]<span class="id" type="var">t</span> = <span
class="id" type="var">t</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">vacuous\_substitution</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>. <span
class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">subst\_not\_afi</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">x</span> <span class="id"
type="var">v</span>, <span class="id" type="var">closed</span> <span
class="id" type="var">v</span> <span
style="font-family: arial;">→</span> ¬ <span class="id"
type="var">appears\_free\_in</span> <span class="id" type="var">x</span>
([<span class="id" type="var">x</span>:=<span class="id"
type="var">v</span>]<span class="id" type="var">t</span>).\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.
<span class="comment">(\* rather slow this way \*)</span>\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">closed</span>, <span class="id" type="var">not</span>.\
   <span class="id" type="var">t\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">t</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">x</span> <span
class="id" type="var">v</span> <span class="id" type="var">P</span>
<span class="id" type="var">A</span>; <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">A</span>.\
     <span class="id" type="var">Case</span> "tvar".\
      <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">i</span>)...\
        <span class="id" type="tactic">inversion</span> <span class="id"
type="var">A</span>; <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">auto</span>.\
     <span class="id" type="var">Case</span> "tapp".\
      <span class="id" type="tactic">inversion</span> <span class="id"
type="var">A</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">Case</span> "tabs".\
      <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">i</span>)...\
        <span class="id" type="tactic">inversion</span> <span class="id"
type="var">A</span>; <span class="id" type="tactic">subst</span>...\
        <span class="id" type="tactic">inversion</span> <span class="id"
type="var">A</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">Case</span> "tpair".\
      <span class="id" type="tactic">inversion</span> <span class="id"
type="var">A</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">Case</span> "tfst".\
      <span class="id" type="tactic">inversion</span> <span class="id"
type="var">A</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">Case</span> "tsnd".\
      <span class="id" type="tactic">inversion</span> <span class="id"
type="var">A</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">Case</span> "ttrue".\
      <span class="id" type="tactic">inversion</span> <span class="id"
type="var">A</span>.\
     <span class="id" type="var">Case</span> "tfalse".\
      <span class="id" type="tactic">inversion</span> <span class="id"
type="var">A</span>.\
     <span class="id" type="var">Case</span> "tif".\
      <span class="id" type="tactic">inversion</span> <span class="id"
type="var">A</span>; <span class="id" type="tactic">subst</span>...\
 <span class="id" type="keyword">Qed</span>.\
\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">duplicate\_subst</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t'</span> <span class="id" type="var">x</span> <span
class="id" type="var">t</span> <span class="id" type="var">v</span>,\
   <span class="id" type="var">closed</span> <span class="id"
type="var">v</span> <span style="font-family: arial;">→</span> [<span
class="id" type="var">x</span>:=<span class="id"
type="var">t</span>]([<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id" type="var">t'</span>) =
[<span class="id" type="var">x</span>:=<span class="id"
type="var">v</span>]<span class="id" type="var">t'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">vacuous\_substitution</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">subst\_not\_afi</span>. <span class="id"
type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">swap\_subst</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">x</span> <span class="id"
type="var">x1</span> <span class="id" type="var">v</span> <span
class="id" type="var">v~1~</span>, <span class="id" type="var">x</span>
≠ <span class="id" type="var">x1</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">closed</span> <span class="id" type="var">v</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">closed</span> <span class="id" type="var">v~1~</span> <span
style="font-family: arial;">→</span>\
                    [<span class="id" type="var">x1</span>:=<span
class="id" type="var">v~1~</span>]([<span class="id"
type="var">x</span>:=<span class="id" type="var">v</span>]<span
class="id" type="var">t</span>) = [<span class="id"
type="var">x</span>:=<span class="id" type="var">v</span>]([<span
class="id" type="var">x1</span>:=<span class="id"
type="var">v~1~</span>]<span class="id" type="var">t</span>).\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
  <span class="id" type="var">t\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">t</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span>; <span class="id"
type="tactic">simpl</span>.\
   <span class="id" type="var">Case</span> "tvar".\
    <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">i</span>); <span class="id"
type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x1</span>
<span class="id" type="var">i</span>).\
       <span class="id" type="tactic">subst</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">ex\_falso\_quodlibet</span>...\
       <span class="id" type="tactic">subst</span>. <span class="id"
type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">eq\_id</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">subst\_closed</span>...\
       <span class="id" type="tactic">subst</span>. <span class="id"
type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">eq\_id</span>.
<span class="id" type="tactic">rewrite</span> <span class="id"
type="var">subst\_closed</span>...\
       <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>... <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>...\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

### Properties of multi-substitutions {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">msubst\_closed</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>, <span class="id" type="var">closed</span> <span
class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span
style="font-family: arial;">∀</span><span class="id"
type="var">ss</span>, <span class="id" type="var">msubst</span> <span
class="id" type="var">ss</span> <span class="id" type="var">t</span> =
<span class="id" type="var">t</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">ss</span>.\
     <span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">a</span>. <span class="id" type="tactic">simpl</span>. <span
class="id" type="tactic">rewrite</span> <span class="id"
type="var">subst\_closed</span>; <span class="id"
type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Closed environments are those that contain only closed terms.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">closed\_env</span> (<span class="id"
type="var">env</span>:<span class="id" type="var">env</span>) {<span
class="id" type="keyword">struct</span> <span class="id"
type="var">env</span>} :=\
 <span class="id" type="keyword">match</span> <span class="id"
type="var">env</span> <span class="id" type="keyword">with</span>\
 | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">True</span>\
 | (<span class="id" type="var">x</span>,<span class="id"
type="var">t</span>)::<span class="id" type="var">env'</span> ⇒ <span
class="id" type="var">closed</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">closed\_env</span> <span class="id" type="var">env'</span>\
 <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Next come a series of lemmas charcterizing how <span
class="inlinecode"><span class="id" type="var">msubst</span></span> of
closed terms distributes over <span class="inlinecode"><span class="id"
type="tactic">subst</span></span> and over each term form

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">subst\_msubst</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">env</span> <span class="id" type="var">x</span> <span
class="id" type="var">v</span> <span class="id" type="var">t</span>,
<span class="id" type="var">closed</span> <span class="id"
type="var">v</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">closed\_env</span> <span class="id"
type="var">env</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">msubst</span> <span class="id"
type="var">env</span> ([<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id" type="var">t</span>) =
[<span class="id" type="var">x</span>:=<span class="id"
type="var">v</span>](<span class="id" type="var">msubst</span> (<span
class="id" type="var">drop</span> <span class="id" type="var">x</span>
<span class="id" type="var">env</span>) <span class="id"
type="var">t</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">env0</span>; <span class="id" type="tactic">intros</span>.\
     <span class="id" type="tactic">auto</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">a</span>. <span class="id" type="tactic">simpl</span>.\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span>. <span class="id" type="var">fold</span> <span
class="id" type="var">closed\_env</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H2</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">i</span> <span
class="id" type="var">x</span>).\
       <span class="id" type="tactic">subst</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">duplicate\_subst</span>; <span class="id"
type="tactic">auto</span>.\
       <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">swap\_subst</span>; <span class="id"
type="tactic">eauto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">msubst\_var</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">ss</span> <span class="id" type="var">x</span>, <span
class="id" type="var">closed\_env</span> <span class="id"
type="var">ss</span> <span style="font-family: arial;">→</span>\
    <span class="id" type="var">msubst</span> <span class="id"
type="var">ss</span> (<span class="id" type="var">tvar</span> <span
class="id" type="var">x</span>) =\
    <span class="id" type="keyword">match</span> <span class="id"
type="var">lookup</span> <span class="id" type="var">x</span> <span
class="id" type="var">ss</span> <span class="id"
type="keyword">with</span>\
    | <span class="id" type="var">Some</span> <span class="id"
type="var">t</span> ⇒ <span class="id" type="var">t</span>\
    | <span class="id" type="var">None</span> ⇒ <span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>\
   <span class="id" type="keyword">end</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">ss</span>; <span class="id" type="tactic">intros</span>.\
     <span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">a</span>.\
      <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">i</span> <span
class="id" type="var">x</span>).\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">msubst\_closed</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>;
<span class="id" type="tactic">auto</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHss</span>. <span class="id" type="tactic">inversion</span>
<span class="id" type="var">H</span>; <span class="id"
type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">msubst\_abs</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">ss</span> <span class="id" type="var">x</span> <span
class="id" type="var">T</span> <span class="id" type="var">t</span>,\
   <span class="id" type="var">msubst</span> <span class="id"
type="var">ss</span> (<span class="id" type="var">tabs</span> <span
class="id" type="var">x</span> <span class="id" type="var">T</span>
<span class="id" type="var">t</span>) = <span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T</span> (<span class="id"
type="var">msubst</span> (<span class="id" type="var">drop</span> <span
class="id" type="var">x</span> <span class="id" type="var">ss</span>)
<span class="id" type="var">t</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">ss</span>; <span class="id" type="tactic">intros</span>.\
     <span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">a</span>.\
       <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">i</span> <span
class="id" type="var">x</span>); <span class="id"
type="tactic">simpl</span>; <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">msubst\_app</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ss</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>, <span class="id"
type="var">msubst</span> <span class="id" type="var">ss</span> (<span
class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>) = <span
class="id" type="var">tapp</span> (<span class="id"
type="var">msubst</span> <span class="id" type="var">ss</span> <span
class="id" type="var">t~1~</span>) (<span class="id"
type="var">msubst</span> <span class="id" type="var">ss</span> <span
class="id" type="var">t~2~</span>).\
 <span class="id" type="keyword">Proof</span>.\
  <span class="id" type="tactic">induction</span> <span class="id"
type="var">ss</span>; <span class="id" type="tactic">intros</span>.\
    <span class="id" type="tactic">reflexivity</span>.\
    <span class="id" type="tactic">destruct</span> <span class="id"
type="var">a</span>.\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">IHss</span>. <span class="id"
type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

You'll need similar functions for the other term constructors.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\

</div>

<div class="doc">

### Properties of multi-extensions {.section}

<div class="paragraph">

</div>

We need to connect the behavior of type assignments with that of their
corresponding contexts.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">mextend\_lookup</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">c</span> : <span class="id" type="var">tass</span>) (<span
class="id" type="var">x</span>:<span class="id" type="var">id</span>),
<span class="id" type="var">lookup</span> <span class="id"
type="var">x</span> <span class="id" type="var">c</span> = (<span
class="id" type="var">mextend</span> <span class="id"
type="var">empty</span> <span class="id" type="var">c</span>) <span
class="id" type="var">x</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">c</span>; <span class="id" type="tactic">intros</span>.\
     <span class="id" type="tactic">auto</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">a</span>. <span class="id" type="tactic">unfold</span> <span
class="id" type="var">lookup</span>, <span class="id"
type="var">mextend</span>, <span class="id" type="var">extend</span>.
<span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">i</span> <span
class="id" type="var">x</span>); <span class="id"
type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">mextend\_drop</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">c</span>: <span class="id" type="var">tass</span>) <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">x'</span>,\
        <span class="id" type="var">mextend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">drop</span> <span class="id" type="var">x</span> <span
class="id" type="var">c</span>) <span class="id" type="var">x'</span> =
<span class="id" type="keyword">if</span> <span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x'</span> <span class="id"
type="keyword">then</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x'</span> <span class="id" type="keyword">else</span> <span
class="id" type="var">mextend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">c</span> <span class="id" type="var">x'</span>.\
    <span class="id" type="tactic">induction</span> <span class="id"
type="var">c</span>; <span class="id" type="tactic">intros</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x'</span>); <span class="id"
type="tactic">auto</span>.\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">a</span>. <span class="id" type="tactic">simpl</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">i</span> <span
class="id" type="var">x</span>).\
          <span class="id" type="tactic">subst</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHc</span>.\
             <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">x'</span>). <span
class="id" type="tactic">auto</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">extend</span>.
<span class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>; <span class="id" type="tactic">auto</span>.\
          <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">extend</span>.
<span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">i</span> <span
class="id" type="var">x'</span>).\
             <span class="id" type="tactic">subst</span>.\
                <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">x'</span>).\
                   <span class="id" type="tactic">subst</span>. <span
class="id" type="var">exfalso</span>. <span class="id"
type="tactic">auto</span>.\
                   <span class="id" type="tactic">auto</span>.\
            <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Properties of Instantiations {.section}

<div class="paragraph">

</div>

These are strightforward.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">instantiation\_domains\_match</span>: <span
style="font-family: arial;">∀</span>{<span class="id"
type="var">c</span>} {<span class="id" type="var">e</span>},\
   <span class="id" type="var">instantiation</span> <span class="id"
type="var">c</span> <span class="id" type="var">e</span> <span
style="font-family: arial;">→</span> <span
style="font-family: arial;">∀</span>{<span class="id"
type="var">x</span>} {<span class="id" type="var">T</span>}, <span
class="id" type="var">lookup</span> <span class="id" type="var">x</span>
<span class="id" type="var">c</span> = <span class="id"
type="var">Some</span> <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">t</span>, <span class="id" type="var">lookup</span> <span
class="id" type="var">x</span> <span class="id" type="var">e</span> =
<span class="id" type="var">Some</span> <span class="id"
type="var">t</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">e</span> <span
class="id" type="var">V</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">V</span>;
<span class="id" type="tactic">intros</span> <span class="id"
type="var">x0</span> <span class="id" type="var">T0</span> <span
class="id" type="var">C</span>.\
     <span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id" type="tactic">inversion</span>
.\
     <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> ×.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x0</span>); <span class="id"
type="tactic">eauto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">instantiation\_env\_closed</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">e</span>, <span class="id"
type="var">instantiation</span> <span class="id" type="var">c</span>
<span class="id" type="var">e</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">closed\_env</span> <span class="id" type="var">e</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">e</span> <span
class="id" type="var">V</span>; <span class="id"
type="tactic">induction</span> <span class="id" type="var">V</span>;
<span class="id" type="tactic">intros</span>.\
     <span class="id" type="var">econstructor</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">closed\_env</span>. <span class="id" type="var">fold</span>
<span class="id" type="var">closed\_env</span>.\
     <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">typable\_empty\_\_closed</span>. <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">R\_typable\_empty</span>. <span class="id"
type="tactic">eauto</span>.\
         <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">instantiation\_R</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">e</span>, <span class="id"
type="var">instantiation</span> <span class="id" type="var">c</span>
<span class="id" type="var">e</span> <span
style="font-family: arial;">→</span>\
                         <span style="font-family: arial;">∀</span><span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span class="id" type="var">T</span>, <span class="id"
type="var">lookup</span> <span class="id" type="var">x</span> <span
class="id" type="var">c</span> = <span class="id" type="var">Some</span>
<span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
                                       <span class="id"
type="var">lookup</span> <span class="id" type="var">x</span> <span
class="id" type="var">e</span> = <span class="id" type="var">Some</span>
<span class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">T</span> <span
class="id" type="var">t</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">e</span> <span
class="id" type="var">V</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">V</span>;
<span class="id" type="tactic">intros</span> <span class="id"
type="var">x'</span> <span class="id" type="var">t'</span> <span
class="id" type="var">T'</span> <span class="id" type="var">G</span>
<span class="id" type="var">E</span>.\
     <span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">lookup</span> <span class="id" type="keyword">in</span> ×.
<span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x'</span>).\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">G</span>; <span class="id" type="tactic">inversion</span>
<span class="id" type="var">E</span>; <span class="id"
type="tactic">subst</span>. <span class="id" type="tactic">auto</span>.\
       <span class="id" type="tactic">eauto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">instantiation\_drop</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">env</span>,\
   <span class="id" type="var">instantiation</span> <span class="id"
type="var">c</span> <span class="id" type="var">env</span> <span
style="font-family: arial;">→</span> <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span class="id" type="var">instantiation</span>
(<span class="id" type="var">drop</span> <span class="id"
type="var">x</span> <span class="id" type="var">c</span>) (<span
class="id" type="var">drop</span> <span class="id" type="var">x</span>
<span class="id" type="var">env</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">e</span> <span
class="id" type="var">V</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">V</span>.\
     <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">simpl</span>. <span class="id"
type="var">constructor</span>.\
     <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">drop</span>.
<span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x0</span>); <span class="id"
type="tactic">auto</span>. <span class="id"
type="var">constructor</span>; <span class="id"
type="tactic">eauto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Congruence lemmas on multistep {.section}

<div class="paragraph">

</div>

We'll need just a few of these; add them as the demand arises.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">multistep\_App2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">v</span>
<span class="id" type="var">t</span> <span class="id"
type="var">t'</span>,\
   <span class="id" type="var">value</span> <span class="id"
type="var">v</span> <span style="font-family: arial;">→</span> (<span
class="id" type="var">t</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">t'</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">tapp</span> <span class="id" type="var">v</span>
<span class="id" type="var">t</span>) <span
style="font-family: arial;">⇒\*</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">v</span> <span
class="id" type="var">t'</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">v</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span> <span class="id" type="var">V</span>
<span class="id" type="var">STM</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">STM</span>.\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>.\
    <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>.\
      <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_App2</span>; <span class="id" type="tactic">eauto</span>.
<span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\

</div>

<div class="doc">

### The R Lemma. {.section}

<div class="paragraph">

</div>

We finally put everything together.
<div class="paragraph">

</div>

The key lemma about preservation of typing under substitution can be
lifted to multi-substitutions:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">msubst\_preserves\_typing</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">e</span>,\
      <span class="id" type="var">instantiation</span> <span class="id"
type="var">c</span> <span class="id" type="var">e</span> <span
style="font-family: arial;">→</span>\
      <span style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">S</span>, <span
class="id" type="var">has\_type</span> (<span class="id"
type="var">mextend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">c</span>) <span class="id" type="var">t</span> <span
class="id" type="var">S</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">msubst</span> <span class="id" type="var">e</span> <span
class="id" type="var">t</span>) <span class="id" type="var">S</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">induction</span> 1; <span class="id"
type="tactic">intros</span>.\
     <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">auto</span>.\
     <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H2</span>. <span
class="id" type="tactic">simpl</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHinstantiation</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">substitution\_preserves\_typing</span>; <span class="id"
type="tactic">eauto</span>.\
     <span class="id" type="tactic">apply</span> (<span class="id"
type="var">R\_typable\_empty</span> <span class="id"
type="var">H0</span>).\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

And at long last, the main lemma.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">msubst\_R</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">env</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span>,\
   <span class="id" type="var">has\_type</span> (<span class="id"
type="var">mextend</span> <span class="id" type="var">empty</span> <span
class="id" type="var">c</span>) <span class="id" type="var">t</span>
<span class="id" type="var">T</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">instantiation</span> <span class="id" type="var">c</span>
<span class="id" type="var">env</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">T</span> (<span
class="id" type="var">msubst</span> <span class="id"
type="var">env</span> <span class="id" type="var">t</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">env0</span> <span
class="id" type="var">t</span> <span class="id" type="var">T</span>
<span class="id" type="var">HT</span> <span class="id"
type="var">V</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">env0</span>.\
   <span
class="comment">(\* We need to generalize the hypothesis a bit before setting up the induction. \*)</span>\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">mextend</span> <span class="id" type="var">empty</span> <span
class="id" type="var">c</span>) <span class="id"
type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="tactic">assert</span> (<span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>, <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> = <span class="id" type="var">lookup</span> <span
class="id" type="var">x</span> <span class="id" type="var">c</span>).\
     <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">HeqGamma</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">mextend\_lookup</span>. <span class="id"
type="tactic">auto</span>.\
   <span class="id" type="tactic">clear</span> <span class="id"
type="var">HeqGamma</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">c</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">HT</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span>.\
\
   <span class="id" type="var">Case</span> "T\_Var".\
    <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">destruct</span> (<span class="id"
type="var">instantiation\_domains\_match</span> <span class="id"
type="var">V</span> <span class="id" type="var">H</span>) <span
class="id" type="keyword">as</span> [<span class="id"
type="var">t</span> <span class="id" type="var">P</span>].\
    <span class="id" type="tactic">eapply</span> <span class="id"
type="var">instantiation\_R</span>; <span class="id"
type="tactic">eauto</span>.\
    <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">msubst\_var</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">P</span>. <span
class="id" type="tactic">auto</span>. <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">instantiation\_env\_closed</span>; <span class="id"
type="tactic">eauto</span>.\
\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">msubst\_abs</span>.\
     <span
class="comment">(\* We'll need variants of the following fact several times, so its simplest to\
        establish it just once. \*)</span>\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">WT</span>: <span class="id" type="var">has\_type</span> <span
class="id" type="var">empty</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> (<span class="id"
type="var">msubst</span> (<span class="id" type="var">drop</span> <span
class="id" type="var">x</span> <span class="id" type="var">env0</span>)
<span class="id" type="var">t~12~</span>)) (<span class="id"
type="var">TArrow</span> <span class="id" type="var">T~11~</span> <span
class="id" type="var">T~12~</span>)).\
      <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Abs</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">msubst\_preserves\_typing</span>. <span
class="id" type="tactic">eapply</span> <span class="id"
type="var">instantiation\_drop</span>; <span class="id"
type="tactic">eauto</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">HT</span>.\
       <span class="id" type="tactic">intros</span>.\
       <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>. <span class="id" type="tactic">rewrite</span>
<span class="id" type="var">mextend\_drop</span>. <span class="id"
type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x0</span>). <span class="id"
type="tactic">auto</span>.\
         <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span>.\
           <span class="id" type="tactic">clear</span> - <span
class="id" type="var">c</span> <span class="id" type="var">n</span>.
<span class="id" type="tactic">induction</span> <span class="id"
type="var">c</span>.\
               <span class="id" type="tactic">simpl</span>. <span
class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>; <span class="id" type="tactic">auto</span>.\
               <span class="id" type="tactic">simpl</span>. <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">a</span>. <span class="id" type="tactic">unfold</span> <span
class="id" type="var">extend</span>. <span class="id"
type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">i</span> <span
class="id" type="var">x0</span>); <span class="id"
type="tactic">auto</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">R</span>. <span class="id" type="var">fold</span> <span
class="id" type="var">R</span>. <span class="id"
type="tactic">split</span>.\
        <span class="id" type="tactic">auto</span>.\
      <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">value\_halts</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">v\_abs</span>.\
      <span class="id" type="tactic">intros</span>.\
      <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">R\_halts</span> <span class="id" type="var">H0</span>) <span
class="id" type="keyword">as</span> [<span class="id"
type="var">v</span> [<span class="id" type="var">P</span> <span
class="id" type="var">Q</span>]].\
      <span class="id" type="var">pose</span> <span class="id"
type="var">proof</span> (<span class="id"
type="var">multistep\_preserves\_R</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">P</span>
<span class="id" type="var">H0</span>).\
      <span class="id" type="tactic">apply</span> <span class="id"
type="var">multistep\_preserves\_R'</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">msubst</span>
((<span class="id" type="var">x</span>,<span class="id"
type="var">v</span>)::<span class="id" type="var">env0</span>) <span
class="id" type="var">t~12~</span>).\
        <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_App</span>. <span class="id" type="tactic">eauto</span>.\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">R\_typable\_empty</span>; <span class="id"
type="tactic">auto</span>.\
        <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_trans</span>. <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">multistep\_App2</span>; <span class="id"
type="tactic">eauto</span>.\
        <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_R</span>.\
        <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">subst\_msubst</span>.\
        <span class="id" type="tactic">eapply</span> <span class="id"
type="var">ST\_AppAbs</span>; <span class="id"
type="tactic">eauto</span>.\
        <span class="id" type="tactic">eapply</span> <span class="id"
type="var">typable\_empty\_\_closed</span>.\
        <span class="id" type="tactic">apply</span> (<span class="id"
type="var">R\_typable\_empty</span> <span class="id"
type="var">H1</span>).\
        <span class="id" type="tactic">eapply</span> <span class="id"
type="var">instantiation\_env\_closed</span>; <span class="id"
type="tactic">eauto</span>.\
        <span class="id" type="tactic">eapply</span> (<span class="id"
type="var">IHHT</span> ((<span class="id" type="var">x</span>,<span
class="id" type="var">T~11~</span>)::<span class="id"
type="var">c</span>)).\
           <span class="id" type="tactic">intros</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>, <span class="id" type="var">lookup</span>.
<span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x0</span>); <span class="id"
type="tactic">auto</span>.\
        <span class="id" type="var">constructor</span>; <span class="id"
type="tactic">auto</span>.\
\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">msubst\_app</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHHT1</span> <span class="id" type="var">c</span> <span
class="id" type="var">H</span> <span class="id" type="var">env0</span>
<span class="id" type="var">V</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">\_</span> [<span
class="id" type="var">\_</span> <span class="id"
type="var">P1</span>]].\
     <span class="id" type="var">pose</span> <span class="id"
type="var">proof</span> (<span class="id" type="var">IHHT2</span> <span
class="id" type="var">c</span> <span class="id" type="var">H</span>
<span class="id" type="var">env0</span> <span class="id"
type="var">V</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">P2</span>. <span class="id" type="var">fold</span>
<span class="id" type="var">R</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">P1</span>. <span
class="id" type="tactic">auto</span>.\
\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

### Normalization Theorem {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">normalization</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">T</span>, <span class="id"
type="var">has\_type</span> <span class="id" type="var">empty</span>
<span class="id" type="var">t</span> <span class="id"
type="var">T</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">halts</span> <span class="id"
type="var">t</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">replace</span> <span class="id"
type="var">t</span> <span class="id" type="keyword">with</span> (<span
class="id" type="var">msubst</span> <span class="id"
type="var">nil</span> <span class="id" type="var">t</span>) <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="tactic">apply</span> (@<span class="id"
type="var">R\_halts</span> <span class="id" type="var">T</span>).\
   <span class="id" type="tactic">apply</span> (<span class="id"
type="var">msubst\_R</span> <span class="id" type="var">nil</span>);
<span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">V\_nil</span>.\
 <span class="id" type="keyword">Qed</span>.\
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
