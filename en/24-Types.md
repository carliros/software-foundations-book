<div id="page">

<div id="header">

</div>

<div id="main">

Types<span class="subtitle">Type Systems</span> {.libtitle}
===============================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id"
type="var">Smallstep</span>.\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">multi</span>.\
\

</div>

<div class="doc">

Our next major topic is *type systems* — static program analyses that
classify expressions according to the "shapes" of their results. We'll
begin with a typed version of a very simple language with just booleans
and numbers, to introduce the basic ideas of types, typing rules, and
the fundamental theorems about type systems: *type preservation* and
*progress*. Then we'll move on to the *simply typed lambda-calculus*,
which lives at the core of every modern functional programming language
(including Coq).

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Typed Arithmetic Expressions {.section}
============================

<div class="paragraph">

</div>

To motivate the discussion of type systems, let's begin as usual with an
extremely simple toy language. We want it to have the potential for
programs "going wrong" because of runtime type errors, so we need
something a tiny bit more complex than the language of constants and
addition that we used in chapter <span class="inlinecode"><span
class="id" type="var">Smallstep</span></span>: a single kind of data
(just numbers) is too simple, but just two kinds (numbers and booleans)
already gives us enough material to tell an interesting story.
<div class="paragraph">

</div>

The language definition is completely routine.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Syntax {.section}
------

<div class="paragraph">

</div>

Informally:
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="var">t</span> ::= <span class="id"
type="var">true</span>\
         | <span class="id" type="var">false</span>\
         | <span class="id" type="keyword">if</span> <span class="id"
type="var">t</span> <span class="id" type="keyword">then</span> <span
class="id" type="var">t</span> <span class="id"
type="keyword">else</span> <span class="id" type="var">t</span>\
         | 0\
         | <span class="id" type="var">succ</span> <span class="id"
type="var">t</span>\
         | <span class="id" type="var">pred</span> <span class="id"
type="var">t</span>\
         | <span class="id" type="var">iszero</span> <span class="id"
type="var">t</span>
<div class="paragraph">

</div>

</div>

Formally:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">tm</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">ttrue</span> : <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tfalse</span> : <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tif</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">tzero</span> : <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tsucc</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">tpred</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">tiszero</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>.\
\

</div>

<div class="doc">

*Values* are <span class="inlinecode"><span class="id"
type="var">true</span></span>, <span class="inlinecode"><span class="id"
type="var">false</span></span>, and numeric values...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">bvalue</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">bv\_true</span> : <span class="id"
type="var">bvalue</span> <span class="id" type="var">ttrue</span>\
   | <span class="id" type="var">bv\_false</span> : <span class="id"
type="var">bvalue</span> <span class="id" type="var">tfalse</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">nvalue</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">nv\_zero</span> : <span class="id"
type="var">nvalue</span> <span class="id" type="var">tzero</span>\
   | <span class="id" type="var">nv\_succ</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>, <span class="id" type="var">nvalue</span> <span
class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nvalue</span> (<span class="id" type="var">tsucc</span> <span
class="id" type="var">t</span>).\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">value</span> (<span class="id" type="var">t</span>:<span
class="id" type="var">tm</span>) := <span class="id"
type="var">bvalue</span> <span class="id" type="var">t</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">nvalue</span> <span class="id" type="var">t</span>.\
\
<div id="proofcontrol1" class="togglescript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')">

<span class="show"></span>

</div>

<div id="proof1" class="proofscript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')"
style="display: none;">

<span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id" type="var">bvalue</span>
<span class="id" type="var">nvalue</span>.\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Unfold</span> <span class="id" type="var">value</span>.\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Unfold</span> <span class="id" type="var">extend</span>.\

</div>

\

</div>

<div class="doc">

Operational Semantics {.section}
---------------------

<div class="paragraph">

</div>

Informally:
<div class="paragraph">

</div>

  
(ST\_IfTrue)  

------------------------------------------------------------------------

if true then t~1~ else t~2~ <span
style="font-family: arial;">⇒</span> t~1~
  
(ST\_IfFalse)  

------------------------------------------------------------------------

if false then t~1~ else t~2~ <span
style="font-family: arial;">⇒</span> t~2~
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_If)  

------------------------------------------------------------------------

if t~1~ then t~2~ else t~3~ <span style="font-family: arial;">⇒</span>
if t~1~' then t~2~ else t~3~
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Succ)  

------------------------------------------------------------------------

succ t~1~ <span style="font-family: arial;">⇒</span> succ t~1~'
  
(ST\_PredZero)  

------------------------------------------------------------------------

pred 0 <span style="font-family: arial;">⇒</span> 0
numeric value v~1~
(ST\_PredSucc)  

------------------------------------------------------------------------

pred (succ v~1~) <span style="font-family: arial;">⇒</span> v~1~
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Pred)  

------------------------------------------------------------------------

pred t~1~ <span style="font-family: arial;">⇒</span> pred t~1~'
  
(ST\_IszeroZero)  

------------------------------------------------------------------------

iszero 0 <span style="font-family: arial;">⇒</span> true
numeric value v~1~
(ST\_IszeroSucc)  

------------------------------------------------------------------------

iszero (succ v~1~) <span style="font-family: arial;">⇒</span> false
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Iszero)  

------------------------------------------------------------------------

iszero t~1~ <span style="font-family: arial;">⇒</span> iszero t~1~'
<div class="paragraph">

</div>

Formally:

</div>

<div class="code code-tight">

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
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>,\
       <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">tif</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tif</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>)\
   | <span class="id" type="var">ST\_Succ</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span>,\
       <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">tsucc</span> <span class="id"
type="var">t~1~</span>) <span style="font-family: arial;">⇒</span>
(<span class="id" type="var">tsucc</span> <span class="id"
type="var">t~1~'</span>)\
   | <span class="id" type="var">ST\_PredZero</span> :\
       (<span class="id" type="var">tpred</span> <span class="id"
type="var">tzero</span>) <span style="font-family: arial;">⇒</span>
<span class="id" type="var">tzero</span>\
   | <span class="id" type="var">ST\_PredSucc</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span>,\
       <span class="id" type="var">nvalue</span> <span class="id"
type="var">t~1~</span> <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">tpred</span> (<span class="id"
type="var">tsucc</span> <span class="id" type="var">t~1~</span>)) <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~</span>\
   | <span class="id" type="var">ST\_Pred</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span>,\
       <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">tpred</span> <span class="id"
type="var">t~1~</span>) <span style="font-family: arial;">⇒</span>
(<span class="id" type="var">tpred</span> <span class="id"
type="var">t~1~'</span>)\
   | <span class="id" type="var">ST\_IszeroZero</span> :\
       (<span class="id" type="var">tiszero</span> <span class="id"
type="var">tzero</span>) <span style="font-family: arial;">⇒</span>
<span class="id" type="var">ttrue</span>\
   | <span class="id" type="var">ST\_IszeroSucc</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span>,\
        <span class="id" type="var">nvalue</span> <span class="id"
type="var">t~1~</span> <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">tiszero</span> (<span class="id"
type="var">tsucc</span> <span class="id" type="var">t~1~</span>)) <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tfalse</span>\
   | <span class="id" type="var">ST\_Iszero</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span>,\
       <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">tiszero</span> <span class="id"
type="var">t~1~</span>) <span style="font-family: arial;">⇒</span>
(<span class="id" type="var">tiszero</span> <span class="id"
type="var">t~1~'</span>)\
\
 <span class="id" type="keyword">where</span> "t~1~ '<span
style="font-family: arial;">⇒</span>' t~2~" := (<span class="id"
type="var">step</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>).\
\
<div id="proofcontrol2" class="togglescript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')">

<span class="show"></span>

</div>

<div id="proof2" class="proofscript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')"
style="display: none;">

<span class="id" type="keyword">Tactic Notation</span> "step\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_IfTrue" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_IfFalse" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "ST\_If"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Succ" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_PredZero"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_PredSucc" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Pred"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_IszeroZero" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_IszeroSucc"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Iszero" ].\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id" type="var">step</span>.\

</div>

</div>

<div class="doc">

Notice that the <span class="inlinecode"><span class="id"
type="var">step</span></span> relation doesn't care about whether
expressions make global sense — it just checks that the operation in the
*next* reduction step is being applied to the right kinds of operands.
<div class="paragraph">

</div>

For example, the term <span class="inlinecode"><span class="id"
type="var">succ</span></span> <span class="inlinecode"><span class="id"
type="var">true</span></span> (i.e., <span class="inlinecode"><span
class="id" type="var">tsucc</span></span> <span class="inlinecode"><span
class="id" type="var">ttrue</span></span> in the formal syntax) cannot
take a step, but the almost as obviously nonsensical term
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="var">succ</span> (<span class="id"
type="keyword">if</span> <span class="id" type="var">true</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">true</span> <span class="id" type="keyword">else</span> <span
class="id" type="var">true</span>) 
<div class="paragraph">

</div>

</div>

can take a step (once, before becoming stuck).

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Normal Forms and Values {.section}
-----------------------

<div class="paragraph">

</div>

The first interesting thing about the <span class="inlinecode"><span
class="id" type="var">step</span></span> relation in this language is
that the strong progress theorem from the Smallstep chapter fails! That
is, there are terms that are normal forms (they can't take a step) but
not values (because we have not included them in our definition of
possible "results of evaluation"). Such terms are *stuck*.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">step\_normal\_form</span> := (<span class="id"
type="var">normal\_form</span> <span class="id"
type="var">step</span>).\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">stuck</span> (<span class="id" type="var">t</span>:<span
class="id" type="var">tm</span>) : <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">step\_normal\_form</span> <span
class="id" type="var">t</span> <span
style="font-family: arial;">∧</span> ¬ <span class="id"
type="var">value</span> <span class="id" type="var">t</span>.\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Unfold</span> <span class="id" type="var">stuck</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (some\_term\_is\_stuck) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">some\_term\_is\_stuck</span> :\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">t</span>, <span class="id" type="var">stuck</span> <span
class="id" type="var">t</span>.\
<div id="proofcontrol3" class="togglescript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')">

<span class="show"></span>

</div>

<div id="proof3" class="proofscript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

However, although values and normal forms are not the same in this
language, the former set is included in the latter. This is important
because it shows we did not accidentally define things so that some
value could still take a step.
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (value\_is\_nf) {.section}

Hint: You will reach a point in this proof where you need to use an
induction to reason about a term that is known to be a numeric value.
This induction can be performed either over the term itself or over the
evidence that it is a numeric value. The proof goes through in either
case, but you will find that one way is quite a bit shorter than the
other. For the sake of the exercise, try to complete the proof both
ways.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">value\_is\_nf</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>,\
   <span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">step\_normal\_form</span> <span class="id"
type="var">t</span>.\
<div id="proofcontrol4" class="togglescript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')">

<span class="show"></span>

</div>

<div id="proof4" class="proofscript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (step\_deterministic) {.section}

Using <span class="inlinecode"><span class="id"
type="var">value\_is\_nf</span></span>, we can show that the <span
class="inlinecode"><span class="id" type="var">step</span></span>
relation is also deterministic...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">step\_deterministic</span>:\
   <span class="id" type="var">deterministic</span> <span class="id"
type="var">step</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
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

Typing {.section}
------

<div class="paragraph">

</div>

The next critical observation about this language is that, although
there are stuck terms, they are all "nonsensical", mixing booleans and
numbers in a way that we don't even *want* to have a meaning. We can
easily exclude such ill-typed terms by defining a *typing relation* that
relates terms to the types (either numeric or boolean) of their final
results.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ty</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">TBool</span> : <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TNat</span> : <span class="id"
type="var">ty</span>.\
\

</div>

<div class="doc">

In informal notation, the typing relation is often written <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">∈</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>, pronounced "<span
class="inlinecode"><span class="id" type="var">t</span></span> has type
<span class="inlinecode"><span class="id" type="var">T</span></span>."
The <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> symbol is called a
"turnstile". (Below, we're going to see richer typing relations where an
additional "context" argument is written to the left of the turnstile.
Here, the context is always empty.)
  
(T\_True)  

------------------------------------------------------------------------

<span style="font-family: arial;">⊢</span> true ∈ Bool
  
(T\_False)  

------------------------------------------------------------------------

<span style="font-family: arial;">⊢</span> false ∈ Bool
<span style="font-family: arial;">⊢</span> t~1~ ∈ Bool    <span
style="font-family: arial;">⊢</span> t~2~ ∈ T    <span
style="font-family: arial;">⊢</span> t~3~ ∈ T
(T\_If)  

------------------------------------------------------------------------

<span
style="font-family: arial;">⊢</span> if t~1~ then t~2~ else t~3~ ∈ T
  
(T\_Zero)  

------------------------------------------------------------------------

<span style="font-family: arial;">⊢</span> 0 ∈ Nat
<span style="font-family: arial;">⊢</span> t~1~ ∈ Nat
(T\_Succ)  

------------------------------------------------------------------------

<span style="font-family: arial;">⊢</span> succ t~1~ ∈ Nat
<span style="font-family: arial;">⊢</span> t~1~ ∈ Nat
(T\_Pred)  

------------------------------------------------------------------------

<span style="font-family: arial;">⊢</span> pred t~1~ ∈ Nat
<span style="font-family: arial;">⊢</span> t~1~ ∈ Nat
(T\_IsZero)  

------------------------------------------------------------------------

<span style="font-family: arial;">⊢</span> iszero t~1~ ∈ Bool

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> "'<span
style="font-family: arial;">⊢</span>' t '∈' T" (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">has\_type</span> : <span class="id" type="var">tm</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">T\_True</span> :\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">ttrue</span> ∈ <span class="id" type="var">TBool</span>\
   | <span class="id" type="var">T\_False</span> :\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">tfalse</span> ∈ <span class="id" type="var">TBool</span>\
   | <span class="id" type="var">T\_If</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> <span class="id" type="var">T</span>,\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TBool</span> <span
style="font-family: arial;">→</span>\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t~3~</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">tif</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span> ∈ <span class="id" type="var">T</span>\
   | <span class="id" type="var">T\_Zero</span> :\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">tzero</span> ∈ <span class="id" type="var">TNat</span>\
   | <span class="id" type="var">T\_Succ</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span>,\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">tsucc</span> <span class="id" type="var">t~1~</span> ∈ <span
class="id" type="var">TNat</span>\
   | <span class="id" type="var">T\_Pred</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span>,\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">tpred</span> <span class="id" type="var">t~1~</span> ∈ <span
class="id" type="var">TNat</span>\
   | <span class="id" type="var">T\_Iszero</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span>,\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
        <span style="font-family: arial;">⊢</span> <span class="id"
type="var">tiszero</span> <span class="id" type="var">t~1~</span> ∈
<span class="id" type="var">TBool</span>\
\
 <span class="id" type="keyword">where</span> "'<span
style="font-family: arial;">⊢</span>' t '∈' T" := (<span class="id"
type="var">has\_type</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span>).\
\
<div id="proofcontrol5" class="togglescript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')">

<span class="show"></span>

</div>

<div id="proof5" class="proofscript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')"
style="display: none;">

<span class="id" type="keyword">Tactic Notation</span>
"has\_type\_cases" <span class="id" type="var">tactic</span>(<span
class="id" type="var">first</span>) <span class="id"
type="var">ident</span>(<span class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_True" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_False" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "T\_If"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Zero" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_Succ" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "T\_Pred"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Iszero" ].\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">has\_type</span>.\

</div>

\

</div>

<div class="doc">

### Examples {.section}

<div class="paragraph">

</div>

It's important to realize that the typing relation is a *conservative*
(or *static*) approximation: it does not calculate the type of the
normal form of a term.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">has\_type\_1</span> :\
   <span style="font-family: arial;">⊢</span> <span class="id"
type="var">tif</span> <span class="id" type="var">tfalse</span> <span
class="id" type="var">tzero</span> (<span class="id"
type="var">tsucc</span> <span class="id" type="var">tzero</span>) ∈
<span class="id" type="var">TNat</span>.\
<div id="proofcontrol6" class="togglescript"
onclick="toggleDisplay('proof6');toggleDisplay('proofcontrol6')">

<span class="show"></span>

</div>

<div id="proof6" class="proofscript"
onclick="toggleDisplay('proof6');toggleDisplay('proofcontrol6')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_If</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_False</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Zero</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Succ</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Zero</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

(Since we've included all the constructors of the typing relation in the
hint database, the <span class="inlinecode"><span class="id"
type="tactic">auto</span></span> tactic can actually find this proof
automatically.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">has\_type\_not</span> :\
   ¬ (<span style="font-family: arial;">⊢</span> <span class="id"
type="var">tif</span> <span class="id" type="var">tfalse</span> <span
class="id" type="var">tzero</span> <span class="id"
type="var">ttrue</span> ∈ <span class="id" type="var">TBool</span>).\
<div id="proofcontrol7" class="togglescript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')">

<span class="show"></span>

</div>

<div id="proof7" class="proofscript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">Contra</span>. <span class="id" type="var">solve</span> <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">inversion</span> 2. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 1 star, optional (succ\_hastype\_nat\_\_hastype\_nat) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">succ\_hastype\_nat\_\_hastype\_nat</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>,\
   <span style="font-family: arial;">⊢</span> <span class="id"
type="var">tsucc</span> <span class="id" type="var">t</span> ∈ <span
class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
   <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">TNat</span>.\
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

Canonical forms {.section}
---------------

<div class="paragraph">

</div>

The following two lemmas capture the basic property that defines the
shape of well-typed values. They say that the definition of value and
the typing relation agree.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">bool\_canonical</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>,\
   <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">TBool</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">value</span> <span class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bvalue</span> <span class="id" type="var">t</span>.\
<div id="proofcontrol8" class="togglescript"
onclick="toggleDisplay('proof8');toggleDisplay('proofcontrol8')">

<span class="show"></span>

</div>

<div id="proof8" class="proofscript"
onclick="toggleDisplay('proof8');toggleDisplay('proofcontrol8')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">HT</span> <span
class="id" type="var">HV</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HV</span>; <span class="id" type="tactic">auto</span>.\
\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">inversion</span>
<span class="id" type="var">HT</span>; <span class="id"
type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">nat\_canonical</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>,\
   <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">value</span> <span class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nvalue</span> <span class="id" type="var">t</span>.\
<div id="proofcontrol9" class="togglescript"
onclick="toggleDisplay('proof9');toggleDisplay('proofcontrol9')">

<span class="show"></span>

</div>

<div id="proof9" class="proofscript"
onclick="toggleDisplay('proof9');toggleDisplay('proofcontrol9')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">HT</span> <span
class="id" type="var">HV</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HV</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">HT</span>.\
\
   <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Progress {.section}
--------

<div class="paragraph">

</div>

The typing relation enjoys two critical properties. The first is that
well-typed normal forms are values (i.e., not stuck).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="tactic">progress</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">T</span>,\
   <span style="font-family: arial;">⊢</span> <span class="id"
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

#### Exercise: 3 stars (finish\_progress) {.section}

Complete the formal proof of the <span class="inlinecode"><span
class="id" type="tactic">progress</span></span> property. (Make sure you
understand the informal proof fragment in the following exercise before
starting — this will save you a lot of time.)

</div>

<div class="code code-tight">

\
<div id="proofcontrol10" class="togglescript"
onclick="toggleDisplay('proof10');toggleDisplay('proofcontrol10')">

<span class="show"></span>

</div>

<div id="proof10" class="proofscript"
onclick="toggleDisplay('proof10');toggleDisplay('proofcontrol10')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
class="id" type="var">HT</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">HT</span>)
<span class="id" type="var">Case</span>...\
   <span
class="comment">(\* The cases that were obviously values, like T\_True and\
      T\_False, were eliminated immediately by auto \*)</span>\
   <span class="id" type="var">Case</span> "T\_If".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">IHHT1</span>;
<span class="id" type="tactic">clear</span> <span class="id"
type="var">IHHT1</span>.\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
     <span class="id" type="tactic">apply</span> (<span class="id"
type="var">bool\_canonical</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">HT1</span>) <span
class="id" type="keyword">in</span> <span class="id"
type="var">H</span>.\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>.\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">t~2~</span>...\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">t~3~</span>...\
     <span class="id" type="var">SCase</span> "t~1~ can take a step".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">H1</span>].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tif</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>)...\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

</div>

\

</div>

<div class="doc">

#### Exercise: 3 stars, advanced (finish\_progress\_informal) {.section}

Complete the corresponding informal proof:
<div class="paragraph">

</div>

*Theorem*: If <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">∈</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>, then either <span class="inlinecode"><span
class="id" type="var">t</span></span> is a value or else <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span>
<span class="inlinecode"><span class="id" type="var">t'</span></span>
for some <span class="inlinecode"><span class="id"
type="var">t'</span></span>.
<div class="paragraph">

</div>

*Proof*: By induction on a derivation of <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">∈</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>.
<div class="paragraph">

</div>

-   If the last rule in the derivation is <span class="inlinecode"><span
    class="id" type="var">T\_If</span></span>, then <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="keyword">if</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="keyword">then</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> <span
    class="inlinecode"><span class="id"
    type="keyword">else</span></span> <span class="inlinecode"><span
    class="id" type="var">t~3~</span></span>, with <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode">∈</span>
    <span class="inlinecode"><span class="id"
    type="var">Bool</span></span>, <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span>
    <span class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span> and <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~3~</span></span> <span class="inlinecode">∈</span>
    <span class="inlinecode"><span class="id"
    type="var">T</span></span>. By the IH, either <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span> is
    a value or else <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> can step to some <span
    class="inlinecode"><span class="id" type="var">t~1~'</span></span>.
    <div class="paragraph">

    </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> is a value, then by the canonical
        forms lemmas and the fact that <span class="inlinecode"><span
        style="font-family: arial;">⊢</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode">∈</span>
        <span class="inlinecode"><span class="id"
        type="var">Bool</span></span> we have that <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> is a <span
        class="inlinecode"><span class="id"
        type="var">bvalue</span></span> — i.e., it is either <span
        class="inlinecode"><span class="id"
        type="var">true</span></span> or <span class="inlinecode"><span
        class="id" type="var">false</span></span>. If <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode">=</span>
        <span class="inlinecode"><span class="id"
        type="var">true</span></span>, then <span
        class="inlinecode"><span class="id" type="var">t</span></span>
        steps to <span class="inlinecode"><span class="id"
        type="var">t~2~</span></span> by <span class="inlinecode"><span
        class="id" type="var">ST\_IfTrue</span></span>, while if <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode">=</span>
        <span class="inlinecode"><span class="id"
        type="var">false</span></span>, then <span
        class="inlinecode"><span class="id" type="var">t</span></span>
        steps to <span class="inlinecode"><span class="id"
        type="var">t~3~</span></span> by <span class="inlinecode"><span
        class="id" type="var">ST\_IfFalse</span></span>. Either way,
        <span class="inlinecode"><span class="id"
        type="var">t</span></span> can step, which is what we wanted to
        show.
        <div class="paragraph">

        </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> itself can take a step, then, by
        <span class="inlinecode"><span class="id"
        type="var">ST\_If</span></span>, so can <span
        class="inlinecode"><span class="id" type="var">t</span></span>.

<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

This is more interesting than the strong progress theorem that we saw in
the Smallstep chapter, where *all* normal forms were values. Here, a
term can be stuck, but only if it is ill typed.
<div class="paragraph">

</div>

#### Exercise: 1 star (step\_review) {.section}

Quick review. Answer *true* or *false*. In this language...
<div class="paragraph">

</div>

-   Every well-typed normal form is a value.
    <div class="paragraph">

    </div>

-   Every value is a normal form.
    <div class="paragraph">

    </div>

-   The single-step evaluation relation is a partial function (i.e., it
    is deterministic).
    <div class="paragraph">

    </div>

-   The single-step evaluation relation is a *total* function.

<div class="paragraph">

</div>

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Type Preservation {.section}
-----------------

<div class="paragraph">

</div>

The second critical property of typing is that, when a well-typed term
takes a step, the result is also a well-typed term.
<div class="paragraph">

</div>

This theorem is often called the *subject reduction* property, because
it tells us what happens when the "subject" of the typing relation is
reduced. This terminology comes from thinking of typing statements as
sentences, where the term is the subject and the type is the predicate.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">preservation</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">t'</span> <span class="id"
type="var">T</span>,\
   <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span> <span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t'</span> ∈ <span class="id" type="var">T</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (finish\_preservation) {.section}

Complete the formal proof of the <span class="inlinecode"><span
class="id" type="var">preservation</span></span> property. (Again, make
sure you understand the informal proof fragment in the following
exercise first.)

</div>

<div class="code code-tight">

\
<div id="proofcontrol11" class="togglescript"
onclick="toggleDisplay('proof11');toggleDisplay('proofcontrol11')">

<span class="show"></span>

</div>

<div id="proof11" class="proofscript"
onclick="toggleDisplay('proof11');toggleDisplay('proofcontrol11')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">t'</span> <span
class="id" type="var">T</span> <span class="id" type="var">HT</span>
<span class="id" type="var">HE</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">t'</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">HT</span>)
<span class="id" type="var">Case</span>;\
          <span
class="comment">(\* every case needs to introduce a couple of things \*)</span>\
          <span class="id" type="tactic">intros</span> <span class="id"
type="var">t'</span> <span class="id" type="var">HE</span>;\
          <span
class="comment">(\* and we can deal with several impossible\
             cases all at once \*)</span>\
          <span class="id" type="tactic">try</span> (<span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>).\
     <span class="id" type="var">Case</span> "T\_If". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">HE</span>;
<span class="id" type="tactic">subst</span>; <span class="id"
type="tactic">clear</span> <span class="id" type="var">HE</span>.\
       <span class="id" type="var">SCase</span> "ST\_IFTrue". <span
class="id" type="tactic">assumption</span>.\
       <span class="id" type="var">SCase</span> "ST\_IfFalse". <span
class="id" type="tactic">assumption</span>.\
       <span class="id" type="var">SCase</span> "ST\_If". <span
class="id" type="tactic">apply</span> <span class="id"
type="var">T\_If</span>; <span class="id" type="tactic">try</span> <span
class="id" type="tactic">assumption</span>.\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHHT1</span>; <span class="id"
type="tactic">assumption</span>.\
     <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (finish\_preservation\_informal) {.section}

Complete the following proof:
<div class="paragraph">

</div>

*Theorem*: If <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">∈</span> <span class="inlinecode"><span class="id"
type="var">T</span></span> and <span class="inlinecode"><span class="id"
type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span>, then
<span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> <span
class="inlinecode">∈</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>.
<div class="paragraph">

</div>

*Proof*: By induction on a derivation of <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">∈</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>.
<div class="paragraph">

</div>

-   If the last rule in the derivation is <span class="inlinecode"><span
    class="id" type="var">T\_If</span></span>, then <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="keyword">if</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="keyword">then</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> <span
    class="inlinecode"><span class="id"
    type="keyword">else</span></span> <span class="inlinecode"><span
    class="id" type="var">t~3~</span></span>, with <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode">∈</span>
    <span class="inlinecode"><span class="id"
    type="var">Bool</span></span>, <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span>
    <span class="inlinecode">∈</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span> and <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~3~</span></span> <span class="inlinecode">∈</span>
    <span class="inlinecode"><span class="id"
    type="var">T</span></span>.
    <div class="paragraph">

    </div>

    Inspecting the rules for the small-step reduction relation and
    remembering that <span class="inlinecode"><span class="id"
    type="var">t</span></span> has the form <span
    class="inlinecode"><span class="id" type="keyword">if</span></span>
    <span class="inlinecode">...</span>, we see that the only ones that
    could have been used to prove <span class="inlinecode"><span
    class="id" type="var">t</span></span> <span class="inlinecode"><span
    style="font-family: arial;">⇒</span></span> <span
    class="inlinecode"><span class="id" type="var">t'</span></span> are
    <span class="inlinecode"><span class="id"
    type="var">ST\_IfTrue</span></span>, <span class="inlinecode"><span
    class="id" type="var">ST\_IfFalse</span></span>, or <span
    class="inlinecode"><span class="id" type="var">ST\_If</span></span>.
    <div class="paragraph">

    </div>

    -   If the last rule was <span class="inlinecode"><span class="id"
        type="var">ST\_IfTrue</span></span>, then <span
        class="inlinecode"><span class="id" type="var">t'</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span>. But we know that <span
        class="inlinecode"><span
        style="font-family: arial;">⊢</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~2~</span></span> <span class="inlinecode">∈</span>
        <span class="inlinecode"><span class="id"
        type="var">T</span></span>, so we are done.
        <div class="paragraph">

        </div>

    -   If the last rule was <span class="inlinecode"><span class="id"
        type="var">ST\_IfFalse</span></span>, then <span
        class="inlinecode"><span class="id" type="var">t'</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">t~3~</span></span>. But we know that <span
        class="inlinecode"><span
        style="font-family: arial;">⊢</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~3~</span></span> <span class="inlinecode">∈</span>
        <span class="inlinecode"><span class="id"
        type="var">T</span></span>, so we are done.
        <div class="paragraph">

        </div>

    -   If the last rule was <span class="inlinecode"><span class="id"
        type="var">ST\_If</span></span>, then <span
        class="inlinecode"><span class="id" type="var">t'</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="keyword">if</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span> <span class="inlinecode"><span
        class="id" type="keyword">then</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~2~</span></span> <span class="inlinecode"><span
        class="id" type="keyword">else</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~3~</span></span>, where <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode"><span
        style="font-family: arial;">⇒</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span>. We know <span
        class="inlinecode"><span
        style="font-family: arial;">⊢</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode">∈</span>
        <span class="inlinecode"><span class="id"
        type="var">Bool</span></span> so, by the IH, <span
        class="inlinecode"><span
        style="font-family: arial;">⊢</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span> <span class="inlinecode">∈</span>
        <span class="inlinecode"><span class="id"
        type="var">Bool</span></span>. The <span
        class="inlinecode"><span class="id"
        type="var">T\_If</span></span> rule then gives us <span
        class="inlinecode"><span
        style="font-family: arial;">⊢</span></span> <span
        class="inlinecode"><span class="id"
        type="keyword">if</span></span> <span class="inlinecode"><span
        class="id" type="var">t~1~'</span></span> <span
        class="inlinecode"><span class="id"
        type="keyword">then</span></span> <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span> <span
        class="inlinecode"><span class="id"
        type="keyword">else</span></span> <span class="inlinecode"><span
        class="id" type="var">t~3~</span></span> <span
        class="inlinecode">∈</span> <span class="inlinecode"><span
        class="id" type="var">T</span></span>, as required.

<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (preservation\_alternate\_proof) {.section}

Now prove the same property again by induction on the *evaluation*
derivation instead of on the typing derivation. Begin by carefully
reading and thinking about the first few lines of the above proof to
make sure you understand what each one is doing. The set-up for this
proof is similar, but not exactly the same.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">preservation'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">t'</span> <span class="id"
type="var">T</span>,\
   <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span> <span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t'</span> ∈ <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
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

Type Soundness {.section}
--------------

<div class="paragraph">

</div>

Putting progress and preservation together, we can see that a well-typed
term can *never* reach a stuck state.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">multistep</span> := (<span class="id" type="var">multi</span>
<span class="id" type="var">step</span>).\
 <span class="id" type="keyword">Notation</span> "t~1~ '<span
style="font-family: arial;">⇒\*</span>' t~2~" := (<span class="id"
type="var">multistep</span> <span class="id" type="var">t~1~</span>
<span class="id" type="var">t~2~</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Corollary</span> <span class="id"
type="var">soundness</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">t'</span> <span class="id"
type="var">T</span>,\
   <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">t'</span> <span style="font-family: arial;">→</span>\
   \~(<span class="id" type="var">stuck</span> <span class="id"
type="var">t'</span>).\
<div id="proofcontrol12" class="togglescript"
onclick="toggleDisplay('proof12');toggleDisplay('proofcontrol12')">

<span class="show"></span>

</div>

<div id="proof12" class="proofscript"
onclick="toggleDisplay('proof12');toggleDisplay('proofcontrol12')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">t'</span> <span
class="id" type="var">T</span> <span class="id" type="var">HT</span>
<span class="id" type="var">P</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">P</span>;
<span class="id" type="tactic">intros</span> [<span class="id"
type="var">R</span> <span class="id" type="var">S</span>].\
   <span class="id" type="tactic">destruct</span> (<span class="id"
type="tactic">progress</span> <span class="id" type="var">x</span> <span
class="id" type="var">T</span> <span class="id" type="var">HT</span>);
<span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHP</span>. <span class="id" type="tactic">apply</span>
(<span class="id" type="var">preservation</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="var">T</span> <span class="id" type="var">HT</span>
<span class="id" type="var">H</span>).\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">stuck</span>. <span class="id" type="tactic">split</span>;
<span class="id" type="tactic">auto</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Aside: the <span class="inlinecode"><span class="id" type="var">normalize</span></span> Tactic {.section}
==============================================================================================

<div class="paragraph">

</div>

When experimenting with definitions of programming languages in Coq, we
often want to see what a particular concrete term steps to — i.e., we
want to find proofs for goals of the form <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒\*</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span>, where
<span class="inlinecode"><span class="id" type="var">t</span></span> is
a completely concrete term and <span class="inlinecode"><span class="id"
type="var">t'</span></span> is unknown. These proofs are simple but
repetitive to do by hand. Consider for example reducing an arithmetic
expression using the small-step relation <span class="inlinecode"><span
class="id" type="var">astep</span></span>.

</div>

<div class="code code-tight">

\
<div id="proofcontrol13" class="togglescript"
onclick="toggleDisplay('proof13');toggleDisplay('proofcontrol13')">

<span class="show"></span>

</div>

<div id="proof13" class="proofscript"
onclick="toggleDisplay('proof13');toggleDisplay('proofcontrol13')"
style="display: none;">

<span class="id" type="keyword">Definition</span> <span class="id"
type="var">amultistep</span> <span class="id" type="var">st</span> :=
<span class="id" type="var">multi</span> (<span class="id"
type="var">astep</span> <span class="id" type="var">st</span>).\
 <span class="id" type="keyword">Notation</span> " t '/' st '<span
style="font-family: arial;">⇒</span>~a~×' t' " := (<span class="id"
type="var">amultistep</span> <span class="id" type="var">st</span> <span
class="id" type="var">t</span> <span class="id" type="var">t'</span>)\
   (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 40, <span class="id" type="var">st</span> <span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 39).\

</div>

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">astep\_example1</span> :\
   (<span class="id" type="var">APlus</span> (<span class="id"
type="var">ANum</span> 3) (<span class="id" type="var">AMult</span>
(<span class="id" type="var">ANum</span> 3) (<span class="id"
type="var">ANum</span> 4))) / <span class="id"
type="var">empty\_state</span>\
   <span style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span>× (<span class="id" type="var">ANum</span> 15).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_step</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">APlus</span>
(<span class="id" type="var">ANum</span> 3) (<span class="id"
type="var">ANum</span> 12)).\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">AS\_Plus2</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">av\_num</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">AS\_Mult</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_step</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">ANum</span>
15).\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">AS\_Plus</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

We repeatedly apply <span class="inlinecode"><span class="id"
type="var">multi\_step</span></span> until we get to a normal form. The
proofs that the intermediate steps are possible are simple enough that
<span class="inlinecode"><span class="id"
type="tactic">auto</span></span>, with appropriate hints, can solve
them.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id" type="var">astep</span>
<span class="id" type="var">aval</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">astep\_example1'</span> :\
   (<span class="id" type="var">APlus</span> (<span class="id"
type="var">ANum</span> 3) (<span class="id" type="var">AMult</span>
(<span class="id" type="var">ANum</span> 3) (<span class="id"
type="var">ANum</span> 4))) / <span class="id"
type="var">empty\_state</span>\
   <span style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span>× (<span class="id" type="var">ANum</span> 15).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The following custom <span class="inlinecode"><span class="id"
type="keyword">Tactic</span></span> <span class="inlinecode"><span
class="id" type="keyword">Notation</span></span> definition captures
this pattern. In addition, before each <span class="inlinecode"><span
class="id" type="var">multi\_step</span></span> we print out the current
goal, so that the user can follow how the term is being evaluated.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Tactic Notation</span> "print\_goal" :=
<span class="id" type="keyword">match</span> <span class="id"
type="var">goal</span> <span class="id" type="keyword">with</span> <span
style="font-family: arial;">⊢</span> ?<span class="id"
type="var">x</span> ⇒ <span class="id" type="var">idtac</span> <span
class="id" type="var">x</span> <span class="id"
type="keyword">end</span>.\
 <span class="id" type="keyword">Tactic Notation</span> "normalize" :=\
    <span class="id" type="tactic">repeat</span> (<span class="id"
type="var">print\_goal</span>; <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span> ;\
              [ (<span class="id" type="tactic">eauto</span> 10; <span
class="id" type="tactic">fail</span>) | (<span class="id"
type="var">instantiate</span>; <span class="id"
type="tactic">simpl</span>)]);\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">astep\_example1''</span> :\
   (<span class="id" type="var">APlus</span> (<span class="id"
type="var">ANum</span> 3) (<span class="id" type="var">AMult</span>
(<span class="id" type="var">ANum</span> 3) (<span class="id"
type="var">ANum</span> 4))) / <span class="id"
type="var">empty\_state</span>\
   <span style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span>× (<span class="id" type="var">ANum</span> 15).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">normalize</span>.\
   <span
class="comment">(\* At this point in the proof script, the Coq response shows \
      a trace of how the expression evaluated. \
\

   (APlus (ANum 3) (AMult (ANum 3) (ANum 4)) / empty\_state ==\>a\* ANum 15)\
    (multi (astep empty\_state) (APlus (ANum 3) (ANum 12)) (ANum 15))\
    (multi (astep empty\_state) (ANum 15) (ANum 15))\
 \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="var">normalize</span></span> tactic also provides a simple way to
calculate what the normal form of a term is, by proving a goal with an
existential variable in it.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">astep\_example1'''</span> : <span
style="font-family: arial;">∃</span><span class="id"
type="var">e'</span>,\
   (<span class="id" type="var">APlus</span> (<span class="id"
type="var">ANum</span> 3) (<span class="id" type="var">AMult</span>
(<span class="id" type="var">ANum</span> 3) (<span class="id"
type="var">ANum</span> 4))) / <span class="id"
type="var">empty\_state</span>\
   <span style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span>× <span class="id" type="var">e'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">ex\_intro</span>. <span class="id"
type="var">normalize</span>.\
\
 <span class="comment">(\* This time, the trace will be:\
\

    (APlus (ANum 3) (AMult (ANum 3) (ANum 4)) / empty\_state ==\>a\* ??)\
     (multi (astep empty\_state) (APlus (ANum 3) (ANum 12)) ??)\
     (multi (astep empty\_state) (ANum 15) ??)\
\
    where ?? is the variable \`\`guessed'' by eapply.\
 \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star (normalize\_ex) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">normalize\_ex</span> : <span
style="font-family: arial;">∃</span><span class="id"
type="var">e'</span>,\
   (<span class="id" type="var">AMult</span> (<span class="id"
type="var">ANum</span> 3) (<span class="id" type="var">AMult</span>
(<span class="id" type="var">ANum</span> 2) (<span class="id"
type="var">ANum</span> 1))) / <span class="id"
type="var">empty\_state</span>\
   <span style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span>× <span class="id" type="var">e'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (normalize\_ex') {.section}

For comparison, prove it using <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> instead of <span
class="inlinecode"><span class="id" type="tactic">eapply</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">normalize\_ex'</span> : <span
style="font-family: arial;">∃</span><span class="id"
type="var">e'</span>,\
   (<span class="id" type="var">AMult</span> (<span class="id"
type="var">ANum</span> 3) (<span class="id" type="var">AMult</span>
(<span class="id" type="var">ANum</span> 2) (<span class="id"
type="var">ANum</span> 1))) / <span class="id"
type="var">empty\_state</span>\
   <span style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span>× <span class="id" type="var">e'</span>.\
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
--------------------

<div class="paragraph">

</div>

#### Exercise: 2 stars (subject\_expansion) {.section}

Having seen the subject reduction property, it is reasonable to wonder
whether the opposity property — subject *expansion* — also holds. That
is, is it always the case that, if <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> and
<span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> <span
class="inlinecode">∈</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>, then <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">∈</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>? If so, prove it. If not, give a
counter-example. (You do not need to prove your counter-example in Coq,
but feel free to do so if you like.)
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (variation1) {.section}

Suppose, that we add this new rule to the typing relation:
<div class="paragraph">

</div>

<div class="code code-tight">

      | <span class="id" type="var">T\_SuccBool</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>,\
            <span style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">TBool</span> <span
style="font-family: arial;">→</span>\
            <span style="font-family: arial;">⊢</span> <span class="id"
type="var">tsucc</span> <span class="id" type="var">t</span> ∈ <span
class="id" type="var">TBool</span>
<div class="paragraph">

</div>

</div>

Which of the following properties remain true in the presence of this
rule? For each one, write either "remains true" or else "becomes false."
If a property becomes false, give a counterexample.
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

#### Exercise: 2 stars (variation2) {.section}

Suppose, instead, that we add this new rule to the <span
class="inlinecode"><span class="id" type="var">step</span></span>
relation:
<div class="paragraph">

</div>

<div class="code code-tight">

      | <span class="id" type="var">ST\_Funny1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
            (<span class="id" type="var">tif</span> <span class="id"
type="var">ttrue</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span>) <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~3~</span>
<div class="paragraph">

</div>

</div>

Which of the above properties become false in the presence of this rule?
For each one that does, give a counter-example.
<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (variation3) {.section}

Suppose instead that we add this rule:
<div class="paragraph">

</div>

<div class="code code-tight">

      | <span class="id" type="var">ST\_Funny2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span> <span class="id"
type="var">t~3~</span>,\
            <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
            (<span class="id" type="var">tif</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tif</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~'</span> <span class="id"
type="var">t~3~</span>)
<div class="paragraph">

</div>

</div>

Which of the above properties become false in the presence of this rule?
For each one that does, give a counter-example.
<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (variation4) {.section}

Suppose instead that we add this rule:
<div class="paragraph">

</div>

<div class="code code-tight">

      | <span class="id" type="var">ST\_Funny3</span> : \
           (<span class="id" type="var">tpred</span> <span class="id"
type="var">tfalse</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tpred</span> (<span class="id" type="var">tpred</span> <span
class="id" type="var">tfalse</span>))
<div class="paragraph">

</div>

</div>

Which of the above properties become false in the presence of this rule?
For each one that does, give a counter-example.
<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (variation5) {.section}

Suppose instead that we add this rule:
<div class="paragraph">

</div>

<div class="code code-tight">

      | <span class="id" type="var">T\_Funny4</span> : \
             <span style="font-family: arial;">⊢</span> <span class="id"
type="var">tzero</span> ∈ <span class="id" type="var">TBool</span>
<div class="paragraph">

</div>

</div>

Which of the above properties become false in the presence of this rule?
For each one that does, give a counter-example.
<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (variation6) {.section}

Suppose instead that we add this rule:
<div class="paragraph">

</div>

<div class="code code-tight">

      | <span class="id" type="var">T\_Funny5</span> : \
             <span style="font-family: arial;">⊢</span> <span class="id"
type="var">tpred</span> <span class="id" type="var">tzero</span> ∈ <span
class="id" type="var">TBool</span>
<div class="paragraph">

</div>

</div>

Which of the above properties become false in the presence of this rule?
For each one that does, give a counter-example.
<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (more\_variations) {.section}

Make up some exercises of your own along the same lines as the ones
above. Try to find ways of selectively breaking properties — i.e., ways
of changing the definitions that break just one of the properties and
leave the others alone. ☐
<div class="paragraph">

</div>

#### Exercise: 1 star (remove\_predzero) {.section}

The evaluation rule <span class="inlinecode"><span class="id"
type="var">E\_PredZero</span></span> is a bit counter-intuitive: we
might feel that it makes more sense for the predecessor of zero to be
undefined, rather than being defined to be zero. Can we achieve this
simply by removing the rule from the definition of <span
class="inlinecode"><span class="id" type="var">step</span></span>? Would
doing so create any problems elsewhere?
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, advanced (prog\_pres\_bigstep) {.section}

Suppose our evaluation relation is defined in the big-step style. What
are the appropriate analogs of the progress and preservation properties?
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
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
