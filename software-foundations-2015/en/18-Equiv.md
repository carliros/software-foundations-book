<div id="page">

<div id="header">

</div>

<div id="main">

Equiv<span class="subtitle">Program Equivalence</span> {.libtitle}
======================================================

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

### Some general advice for working on exercises: {.section}

<div class="paragraph">

</div>

-   Most of the Coq proofs we ask you to do are similar to proofs that
    we've provided. Before starting to work on the homework problems,
    take the time to work through our proofs (both informally, on paper,
    and in Coq) and make sure you understand them in detail. This will
    save you a lot of time.
    <div class="paragraph">

    </div>

-   The Coq proofs we're doing now are sufficiently complicated that it
    is more or less impossible to complete them simply by random
    experimentation or "following your nose." You need to start with an
    idea about why the property is true and how the proof is going to
    go. The best way to do this is to write out at least a sketch of an
    informal proof on paper — one that intuitively convinces you of the
    truth of the theorem — before starting to work on the formal one.
    Alternately, grab a friend and try to convince them that the theorem
    is true; then try to formalize your explanation.
    <div class="paragraph">

    </div>

-   Use automation to save work! Some of the proofs in this chapter's
    exercises are pretty long if you try to write out all the cases
    explicitly.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Behavioral Equivalence {.section}
======================

<div class="paragraph">

</div>

In the last chapter, we investigated the correctness of a very simple
program transformation: the <span class="inlinecode"><span class="id"
type="var">optimize\_0plus</span></span> function. The programming
language we were considering was the first version of the language of
arithmetic expressions — with no variables — so in that setting it was
very easy to define what it *means* for a program transformation to be
correct: it should always yield a program that evaluates to the same
number as the original.
<div class="paragraph">

</div>

To go further and talk about the correctness of program transformations
in the full Imp language, we need to consider the role of variables and
state.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Definitions {.section}
-----------

<div class="paragraph">

</div>

For <span class="inlinecode"><span class="id"
type="var">aexp</span></span>s and <span class="inlinecode"><span
class="id" type="var">bexp</span></span>s with variables, the definition
we want is clear. We say that two <span class="inlinecode"><span
class="id" type="var">aexp</span></span>s or <span
class="inlinecode"><span class="id" type="var">bexp</span></span>s are
*behaviorally equivalent* if they evaluate to the same result *in every
state*.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">aequiv</span> (<span class="id" type="var">a1</span> <span
class="id" type="var">a2</span> : <span class="id"
type="var">aexp</span>) : <span class="id" type="keyword">Prop</span>
:=\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">st</span>:<span class="id" type="var">state</span>),\
     <span class="id" type="var">aeval</span> <span class="id"
type="var">st</span> <span class="id" type="var">a1</span> = <span
class="id" type="var">aeval</span> <span class="id" type="var">st</span>
<span class="id" type="var">a2</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">bequiv</span> (<span class="id" type="var">b1</span> <span
class="id" type="var">b2</span> : <span class="id"
type="var">bexp</span>) : <span class="id" type="keyword">Prop</span>
:=\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">st</span>:<span class="id" type="var">state</span>),\
     <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b1</span> = <span
class="id" type="var">beval</span> <span class="id" type="var">st</span>
<span class="id" type="var">b2</span>.\
\

</div>

<div class="doc">

For commands, the situation is a little more subtle. We can't simply say
"two commands are behaviorally equivalent if they evaluate to the same
ending state whenever they are started in the same initial state,"
because some commands (in some starting states) don't terminate in any
final state at all! What we need instead is this: two commands are
behaviorally equivalent if, for any given starting state, they either
both diverge or both terminate in the same final state. A compact way to
express this is "if the first one terminates in a particular state then
so does the second, and vice versa."

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">cequiv</span> (<span class="id" type="var">c1</span> <span
class="id" type="var">c2</span> : <span class="id"
type="var">com</span>) : <span class="id" type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">st</span> <span class="id" type="var">st'</span> : <span
class="id" type="var">state</span>),\
     (<span class="id" type="var">c1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span>) <span
style="font-family: arial;">↔</span> (<span class="id"
type="var">c2</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span>).\
\

</div>

<div class="doc">

#### Exercise: 2 stars (equiv\_classes) {.section}

<div class="paragraph">

</div>

Given the following programs, group together those that are equivalent
in <span class="inlinecode"><span class="id"
type="var">Imp</span></span>. Your answer should be given as a list of
lists, where each sub-list represents a group of equivalent programs.
For example, if you think programs (a) through (h) are all equivalent to
each other, but not to (i), your answer should look like this:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

    [ [<span class="id" type="var">prog\_a</span>;<span class="id"
type="var">prog\_b</span>;<span class="id"
type="var">prog\_c</span>;<span class="id"
type="var">prog\_d</span>;<span class="id"
type="var">prog\_e</span>;<span class="id"
type="var">prog\_f</span>;<span class="id"
type="var">prog\_g</span>;<span class="id" type="var">prog\_h</span>] ;\
       [<span class="id" type="var">prog\_i</span>] ]
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Write down your answer below in the definition of <span
class="inlinecode"><span class="id"
type="var">equiv\_classes</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">prog\_a</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">BNot</span> (<span class="id" type="var">BLe</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 0)) <span class="id"
type="var">DO</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1)\
   <span class="id" type="var">END</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">prog\_b</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">IFB</span> <span class="id"
type="var">BEq</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
0) <span class="id" type="var">THEN</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1);;\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 1\
   <span class="id" type="var">ELSE</span>\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 0\
   <span class="id" type="var">FI</span>;;\
   <span class="id" type="var">X</span> ::= <span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">AId</span>
<span class="id" type="var">Y</span>);;\
   <span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 0.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">prog\_c</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">SKIP</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">prog\_d</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 0)) <span class="id"
type="var">DO</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AMult</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">AId</span> <span class="id"
type="var">Y</span>)) (<span class="id" type="var">ANum</span> 1)\
   <span class="id" type="var">END</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">prog\_e</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 0.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">prog\_f</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">Y</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1);;\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">AId</span> <span class="id"
type="var">Y</span>)) <span class="id" type="var">DO</span>\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1)\
   <span class="id" type="var">END</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">prog\_g</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">BTrue</span> <span class="id" type="var">DO</span>\
     <span class="id" type="var">SKIP</span>\
   <span class="id" type="var">END</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">prog\_h</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">AId</span> <span class="id"
type="var">X</span>)) <span class="id" type="var">DO</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1)\
   <span class="id" type="var">END</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">prog\_i</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">AId</span> <span class="id"
type="var">Y</span>)) <span class="id" type="var">DO</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">Y</span>) (<span class="id" type="var">ANum</span>
1)\
   <span class="id" type="var">END</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">equiv\_classes</span> : <span class="id"
type="var">list</span> (<span class="id" type="var">list</span> <span
class="id" type="var">com</span>) :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
 <span
class="comment">(\* GRADE\_TEST 2: check\_equiv\_classes equiv\_classes \*)</span>\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Examples {.section}
--------

<div class="paragraph">

</div>

Here are some simple examples of equivalences of arithmetic and boolean
expressions.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">aequiv\_example</span>:\
   <span class="id" type="var">aequiv</span> (<span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">AId</span>
<span class="id" type="var">X</span>)) (<span class="id"
type="var">ANum</span> 0).\
<div id="proofcontrol1" class="togglescript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')">

<span class="show"></span>

</div>

<div id="proof1" class="proofscript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span>. <span class="id" type="tactic">simpl</span>. <span
class="id" type="tactic">omega</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">bequiv\_example</span>:\
   <span class="id" type="var">bequiv</span> (<span class="id"
type="var">BEq</span> (<span class="id" type="var">AMinus</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">AId</span> <span class="id"
type="var">X</span>)) (<span class="id" type="var">ANum</span> 0)) <span
class="id" type="var">BTrue</span>.\
<div id="proofcontrol2" class="togglescript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')">

<span class="show"></span>

</div>

<div id="proof2" class="proofscript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span>. <span class="id" type="tactic">unfold</span> <span
class="id" type="var">beval</span>.\
   <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">aequiv\_example</span>. <span class="id"
type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

For examples of command equivalence, let's start by looking at some
trivial program transformations involving <span class="inlinecode"><span
class="id" type="var">SKIP</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">skip\_left</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">c</span>,\
   <span class="id" type="var">cequiv</span>\
      (<span class="id" type="var">SKIP</span>;; <span class="id"
type="var">c</span>)\
      <span class="id" type="var">c</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span>.\
   <span class="id" type="tactic">split</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">H</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">subst</span>.\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H2</span>. <span class="id" type="tactic">subst</span>.\
     <span class="id" type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Seq</span> <span class="id" type="keyword">with</span>
<span class="id" type="var">st</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Skip</span>.\
     <span class="id" type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (skip\_right) {.section}

Prove that adding a SKIP after a command results in an equivalent
program

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">skip\_right</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">c</span>,\
   <span class="id" type="var">cequiv</span>\
     (<span class="id" type="var">c</span>;; <span class="id"
type="var">SKIP</span>)\
     <span class="id" type="var">c</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Similarly, here is a simple transformations that simplifies <span
class="inlinecode"><span class="id" type="var">IFB</span></span>
commands:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">IFB\_true\_simple</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">c1</span> <span class="id" type="var">c2</span>,\
   <span class="id" type="var">cequiv</span>\
     (<span class="id" type="var">IFB</span> <span class="id"
type="var">BTrue</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span>)\
     <span class="id" type="var">c1</span>.\
<div id="proofcontrol3" class="togglescript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')">

<span class="show"></span>

</div>

<div id="proof3" class="proofscript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c2</span>.\
   <span class="id" type="tactic">split</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">H</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">assumption</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H5</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_IfTrue</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Of course, few programmers would be tempted to write a conditional whose
guard is literally <span class="inlinecode"><span class="id"
type="var">BTrue</span></span>. A more interesting case is when the
guard is *equivalent* to true:
<div class="paragraph">

</div>

*Theorem*: If <span class="inlinecode"><span class="id"
type="var">b</span></span> is equivalent to <span
class="inlinecode"><span class="id" type="var">BTrue</span></span>, then
<span class="inlinecode"><span class="id" type="var">IFB</span></span>
<span class="inlinecode"><span class="id" type="var">b</span></span>
<span class="inlinecode"><span class="id" type="var">THEN</span></span>
<span class="inlinecode"><span class="id" type="var">c1</span></span>
<span class="inlinecode"><span class="id" type="var">ELSE</span></span>
<span class="inlinecode"><span class="id" type="var">c2</span></span>
<span class="inlinecode"><span class="id" type="var">FI</span></span> is
equivalent to <span class="inlinecode"><span class="id"
type="var">c1</span></span>.
###  {.section}

<div class="paragraph">

</div>

*Proof*:
<div class="paragraph">

</div>

-   (<span class="inlinecode"><span
    style="font-family: arial;">→</span></span>) We must show, for all
    <span class="inlinecode"><span class="id"
    type="var">st</span></span> and <span class="inlinecode"><span
    class="id" type="var">st'</span></span>, that if <span
    class="inlinecode"><span class="id" type="var">IFB</span></span>
    <span class="inlinecode"><span class="id" type="var">b</span></span>
    <span class="inlinecode"><span class="id"
    type="var">THEN</span></span> <span class="inlinecode"><span
    class="id" type="var">c1</span></span> <span
    class="inlinecode"><span class="id" type="var">ELSE</span></span>
    <span class="inlinecode"><span class="id"
    type="var">c2</span></span> <span class="inlinecode"><span
    class="id" type="var">FI</span></span> <span
    class="inlinecode">/</span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⇓</span></span>
    <span class="inlinecode"><span class="id"
    type="var">st'</span></span> then <span class="inlinecode"><span
    class="id" type="var">c1</span></span> <span
    class="inlinecode">/</span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⇓</span></span>
    <span class="inlinecode"><span class="id"
    type="var">st'</span></span>.
    <div class="paragraph">

    </div>

    Proceed by cases on the rules that could possibly have been used to
    show <span class="inlinecode"><span class="id"
    type="var">IFB</span></span> <span class="inlinecode"><span
    class="id" type="var">b</span></span> <span class="inlinecode"><span
    class="id" type="var">THEN</span></span> <span
    class="inlinecode"><span class="id" type="var">c1</span></span>
    <span class="inlinecode"><span class="id"
    type="var">ELSE</span></span> <span class="inlinecode"><span
    class="id" type="var">c2</span></span> <span
    class="inlinecode"><span class="id" type="var">FI</span></span>
    <span class="inlinecode">/</span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⇓</span></span>
    <span class="inlinecode"><span class="id"
    type="var">st'</span></span>, namely <span class="inlinecode"><span
    class="id" type="var">E\_IfTrue</span></span> and <span
    class="inlinecode"><span class="id"
    type="var">E\_IfFalse</span></span>.
    <div class="paragraph">

    </div>

    -   Suppose the final rule rule in the derivation of <span
        class="inlinecode"><span class="id" type="var">IFB</span></span>
        <span class="inlinecode"><span class="id"
        type="var">b</span></span> <span class="inlinecode"><span
        class="id" type="var">THEN</span></span> <span
        class="inlinecode"><span class="id" type="var">c1</span></span>
        <span class="inlinecode"><span class="id"
        type="var">ELSE</span></span> <span class="inlinecode"><span
        class="id" type="var">c2</span></span> <span
        class="inlinecode"><span class="id" type="var">FI</span></span>
        <span class="inlinecode">/</span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span
        style="font-family: arial;">⇓</span></span> <span
        class="inlinecode"><span class="id" type="var">st'</span></span>
        was <span class="inlinecode"><span class="id"
        type="var">E\_IfTrue</span></span>. We then have, by the
        premises of <span class="inlinecode"><span class="id"
        type="var">E\_IfTrue</span></span>, that <span
        class="inlinecode"><span class="id" type="var">c1</span></span>
        <span class="inlinecode">/</span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span
        style="font-family: arial;">⇓</span></span> <span
        class="inlinecode"><span class="id"
        type="var">st'</span></span>. This is exactly what we set out to
        prove.
        <div class="paragraph">

        </div>

    -   On the other hand, suppose the final rule in the derivation of
        <span class="inlinecode"><span class="id"
        type="var">IFB</span></span> <span class="inlinecode"><span
        class="id" type="var">b</span></span> <span
        class="inlinecode"><span class="id"
        type="var">THEN</span></span> <span class="inlinecode"><span
        class="id" type="var">c1</span></span> <span
        class="inlinecode"><span class="id"
        type="var">ELSE</span></span> <span class="inlinecode"><span
        class="id" type="var">c2</span></span> <span
        class="inlinecode"><span class="id" type="var">FI</span></span>
        <span class="inlinecode">/</span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span
        style="font-family: arial;">⇓</span></span> <span
        class="inlinecode"><span class="id" type="var">st'</span></span>
        was <span class="inlinecode"><span class="id"
        type="var">E\_IfFalse</span></span>. We then know that <span
        class="inlinecode"><span class="id"
        type="var">beval</span></span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span class="id" type="var">b</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">false</span></span> and <span
        class="inlinecode"><span class="id" type="var">c2</span></span>
        <span class="inlinecode">/</span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span
        style="font-family: arial;">⇓</span></span> <span
        class="inlinecode"><span class="id"
        type="var">st'</span></span>.
        <div class="paragraph">

        </div>

        Recall that <span class="inlinecode"><span class="id"
        type="var">b</span></span> is equivalent to <span
        class="inlinecode"><span class="id"
        type="var">BTrue</span></span>, i.e. forall <span
        class="inlinecode"><span class="id" type="var">st</span></span>,
        <span class="inlinecode"><span class="id"
        type="var">beval</span></span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span class="id" type="var">b</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">beval</span></span> <span
        class="inlinecode"><span class="id" type="var">st</span></span>
        <span class="inlinecode"><span class="id"
        type="var">BTrue</span></span>. In particular, this means that
        <span class="inlinecode"><span class="id"
        type="var">beval</span></span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span class="id" type="var">b</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">true</span></span>, since <span
        class="inlinecode"><span class="id"
        type="var">beval</span></span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span class="id"
        type="var">BTrue</span></span> <span class="inlinecode">=</span>
        <span class="inlinecode"><span class="id"
        type="var">true</span></span>. But this is a contradiction,
        since <span class="inlinecode"><span class="id"
        type="var">E\_IfFalse</span></span> requires that <span
        class="inlinecode"><span class="id"
        type="var">beval</span></span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span class="id" type="var">b</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">false</span></span>. Thus, the final rule
        could not have been <span class="inlinecode"><span class="id"
        type="var">E\_IfFalse</span></span>.
        <div class="paragraph">

        </div>
-   (<span class="inlinecode"><span
    style="font-family: arial;">←</span></span>) We must show, for all
    <span class="inlinecode"><span class="id"
    type="var">st</span></span> and <span class="inlinecode"><span
    class="id" type="var">st'</span></span>, that if <span
    class="inlinecode"><span class="id" type="var">c1</span></span>
    <span class="inlinecode">/</span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⇓</span></span>
    <span class="inlinecode"><span class="id"
    type="var">st'</span></span> then <span class="inlinecode"><span
    class="id" type="var">IFB</span></span> <span
    class="inlinecode"><span class="id" type="var">b</span></span> <span
    class="inlinecode"><span class="id" type="var">THEN</span></span>
    <span class="inlinecode"><span class="id"
    type="var">c1</span></span> <span class="inlinecode"><span
    class="id" type="var">ELSE</span></span> <span
    class="inlinecode"><span class="id" type="var">c2</span></span>
    <span class="inlinecode"><span class="id"
    type="var">FI</span></span> <span class="inlinecode">/</span> <span
    class="inlinecode"><span class="id" type="var">st</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⇓</span></span> <span
    class="inlinecode"><span class="id" type="var">st'</span></span>.
    <div class="paragraph">

    </div>

    Since <span class="inlinecode"><span class="id"
    type="var">b</span></span> is equivalent to <span
    class="inlinecode"><span class="id" type="var">BTrue</span></span>,
    we know that <span class="inlinecode"><span class="id"
    type="var">beval</span></span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span class="id" type="var">b</span></span> =
    <span class="inlinecode"><span class="id"
    type="var">beval</span></span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span class="id" type="var">BTrue</span></span> =
    <span class="inlinecode"><span class="id"
    type="var">true</span></span>. Together with the assumption that
    <span class="inlinecode"><span class="id"
    type="var">c1</span></span> <span class="inlinecode">/</span> <span
    class="inlinecode"><span class="id" type="var">st</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⇓</span></span> <span
    class="inlinecode"><span class="id" type="var">st'</span></span>, we
    can apply <span class="inlinecode"><span class="id"
    type="var">E\_IfTrue</span></span> to derive <span
    class="inlinecode"><span class="id" type="var">IFB</span></span>
    <span class="inlinecode"><span class="id" type="var">b</span></span>
    <span class="inlinecode"><span class="id"
    type="var">THEN</span></span> <span class="inlinecode"><span
    class="id" type="var">c1</span></span> <span
    class="inlinecode"><span class="id" type="var">ELSE</span></span>
    <span class="inlinecode"><span class="id"
    type="var">c2</span></span> <span class="inlinecode"><span
    class="id" type="var">FI</span></span> <span
    class="inlinecode">/</span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⇓</span></span>
    <span class="inlinecode"><span class="id"
    type="var">st'</span></span>. ☐

<div class="paragraph">

</div>

Here is the formal version of this proof:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">IFB\_true</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">c2</span>,\
      <span class="id" type="var">bequiv</span> <span class="id"
type="var">b</span> <span class="id" type="var">BTrue</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">cequiv</span>\
        (<span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span>)\
        <span class="id" type="var">c1</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c2</span> <span class="id" type="var">Hb</span>.\
   <span class="id" type="tactic">split</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">H</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>.\
     <span class="id" type="var">SCase</span> "b evaluates to true".\
       <span class="id" type="tactic">assumption</span>.\
     <span class="id" type="var">SCase</span> "b evaluates to false
(contradiction)".\
       <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bequiv</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hb</span>. <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">Hb</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">Hb</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>.\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H5</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_IfTrue</span>; <span class="id" type="tactic">try</span>
<span class="id" type="tactic">assumption</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bequiv</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hb</span>. <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">Hb</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">Hb</span>. <span class="id" type="tactic">reflexivity</span>.
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (IFB\_false) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">IFB\_false</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">c2</span>,\
   <span class="id" type="var">bequiv</span> <span class="id"
type="var">b</span> <span class="id" type="var">BFalse</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">cequiv</span>\
     (<span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span>)\
     <span class="id" type="var">c2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (swap\_if\_branches) {.section}

Show that we can swap the branches of an IF by negating its condition

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">swap\_if\_branches</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">e1</span> <span class="id"
type="var">e2</span>,\
   <span class="id" type="var">cequiv</span>\
     (<span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">e1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">e2</span> <span class="id"
type="var">FI</span>)\
     (<span class="id" type="var">IFB</span> <span class="id"
type="var">BNot</span> <span class="id" type="var">b</span> <span
class="id" type="var">THEN</span> <span class="id" type="var">e2</span>
<span class="id" type="var">ELSE</span> <span class="id"
type="var">e1</span> <span class="id" type="var">FI</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

For <span class="inlinecode"><span class="id"
type="var">WHILE</span></span> loops, we can give a similar pair of
theorems. A loop whose guard is equivalent to <span
class="inlinecode"><span class="id" type="var">BFalse</span></span> is
equivalent to <span class="inlinecode"><span class="id"
type="var">SKIP</span></span>, while a loop whose guard is equivalent to
<span class="inlinecode"><span class="id" type="var">BTrue</span></span>
is equivalent to <span class="inlinecode"><span class="id"
type="var">WHILE</span></span> <span class="inlinecode"><span class="id"
type="var">BTrue</span></span> <span class="inlinecode"><span class="id"
type="var">DO</span></span> <span class="inlinecode"><span class="id"
type="var">SKIP</span></span> <span class="inlinecode"><span class="id"
type="var">END</span></span> (or any other non-terminating program). The
first of these facts is easy.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">WHILE\_false</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span>,\
      <span class="id" type="var">bequiv</span> <span class="id"
type="var">b</span> <span class="id" type="var">BFalse</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">cequiv</span>\
        (<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span>)\
        <span class="id" type="var">SKIP</span>.\
<div id="proofcontrol4" class="togglescript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')">

<span class="show"></span>

</div>

<div id="proof4" class="proofscript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> <span
class="id" type="var">Hb</span>. <span class="id"
type="tactic">split</span>; <span class="id" type="tactic">intros</span>
<span class="id" type="var">H</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>.\
     <span class="id" type="var">SCase</span> "E\_WhileEnd".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Skip</span>.\
     <span class="id" type="var">SCase</span> "E\_WhileLoop".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">Hb</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H2</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H2</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_WhileEnd</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">Hb</span>.\
     <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 2 stars, advanced, optional (WHILE\_false\_informal) {.section}

Write an informal proof of <span class="inlinecode"><span class="id"
type="var">WHILE\_false</span></span>.
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

###  {.section}

To prove the second fact, we need an auxiliary lemma stating that <span
class="inlinecode"><span class="id" type="var">WHILE</span></span> loops
whose guards are equivalent to <span class="inlinecode"><span class="id"
type="var">BTrue</span></span> never terminate:
<div class="paragraph">

</div>

*Lemma*: If <span class="inlinecode"><span class="id"
type="var">b</span></span> is equivalent to <span
class="inlinecode"><span class="id" type="var">BTrue</span></span>, then
it cannot be the case that <span class="inlinecode">(<span class="id"
type="var">WHILE</span></span> <span class="inlinecode"><span class="id"
type="var">b</span></span> <span class="inlinecode"><span class="id"
type="var">DO</span></span> <span class="inlinecode"><span class="id"
type="var">c</span></span> <span class="inlinecode"><span class="id"
type="var">END</span>)</span> <span class="inlinecode">/</span> <span
class="inlinecode"><span class="id" type="var">st</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇓</span></span>
<span class="inlinecode"><span class="id" type="var">st'</span></span>.
<div class="paragraph">

</div>

*Proof*: Suppose that <span class="inlinecode">(<span class="id"
type="var">WHILE</span></span> <span class="inlinecode"><span class="id"
type="var">b</span></span> <span class="inlinecode"><span class="id"
type="var">DO</span></span> <span class="inlinecode"><span class="id"
type="var">c</span></span> <span class="inlinecode"><span class="id"
type="var">END</span>)</span> <span class="inlinecode">/</span> <span
class="inlinecode"><span class="id" type="var">st</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇓</span></span>
<span class="inlinecode"><span class="id" type="var">st'</span></span>.
We show, by induction on a derivation of <span class="inlinecode">(<span
class="id" type="var">WHILE</span></span> <span class="inlinecode"><span
class="id" type="var">b</span></span> <span class="inlinecode"><span
class="id" type="var">DO</span></span> <span class="inlinecode"><span
class="id" type="var">c</span></span> <span class="inlinecode"><span
class="id" type="var">END</span>)</span> <span
class="inlinecode">/</span> <span class="inlinecode"><span class="id"
type="var">st</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇓</span></span> <span
class="inlinecode"><span class="id" type="var">st'</span></span>, that
this assumption leads to a contradiction.
<div class="paragraph">

</div>

-   Suppose <span class="inlinecode">(<span class="id"
    type="var">WHILE</span></span> <span class="inlinecode"><span
    class="id" type="var">b</span></span> <span class="inlinecode"><span
    class="id" type="var">DO</span></span> <span
    class="inlinecode"><span class="id" type="var">c</span></span> <span
    class="inlinecode"><span class="id" type="var">END</span>)</span>
    <span class="inlinecode">/</span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⇓</span></span>
    <span class="inlinecode"><span class="id"
    type="var">st'</span></span> is proved using rule <span
    class="inlinecode"><span class="id"
    type="var">E\_WhileEnd</span></span>. Then by assumption <span
    class="inlinecode"><span class="id" type="var">beval</span></span>
    <span class="inlinecode"><span class="id"
    type="var">st</span></span> <span class="inlinecode"><span
    class="id" type="var">b</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">false</span></span>. But this contradicts the
    assumption that <span class="inlinecode"><span class="id"
    type="var">b</span></span> is equivalent to <span
    class="inlinecode"><span class="id" type="var">BTrue</span></span>.
    <div class="paragraph">

    </div>

-   Suppose <span class="inlinecode">(<span class="id"
    type="var">WHILE</span></span> <span class="inlinecode"><span
    class="id" type="var">b</span></span> <span class="inlinecode"><span
    class="id" type="var">DO</span></span> <span
    class="inlinecode"><span class="id" type="var">c</span></span> <span
    class="inlinecode"><span class="id" type="var">END</span>)</span>
    <span class="inlinecode">/</span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⇓</span></span>
    <span class="inlinecode"><span class="id"
    type="var">st'</span></span> is proved using rule <span
    class="inlinecode"><span class="id"
    type="var">E\_WhileLoop</span></span>. Then we are given the
    induction hypothesis that <span class="inlinecode">(<span class="id"
    type="var">WHILE</span></span> <span class="inlinecode"><span
    class="id" type="var">b</span></span> <span class="inlinecode"><span
    class="id" type="var">DO</span></span> <span
    class="inlinecode"><span class="id" type="var">c</span></span> <span
    class="inlinecode"><span class="id" type="var">END</span>)</span>
    <span class="inlinecode">/</span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⇓</span></span>
    <span class="inlinecode"><span class="id"
    type="var">st'</span></span> is contradictory, which is exactly what
    we are trying to prove!
    <div class="paragraph">

    </div>

-   Since these are the only rules that could have been used to prove
    <span class="inlinecode">(<span class="id"
    type="var">WHILE</span></span> <span class="inlinecode"><span
    class="id" type="var">b</span></span> <span class="inlinecode"><span
    class="id" type="var">DO</span></span> <span
    class="inlinecode"><span class="id" type="var">c</span></span> <span
    class="inlinecode"><span class="id" type="var">END</span>)</span>
    <span class="inlinecode">/</span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⇓</span></span>
    <span class="inlinecode"><span class="id"
    type="var">st'</span></span>, the other cases of the induction are
    immediately contradictory. ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">WHILE\_true\_nonterm</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span> <span class="id"
type="var">st</span> <span class="id" type="var">st'</span>,\
      <span class="id" type="var">bequiv</span> <span class="id"
type="var">b</span> <span class="id" type="var">BTrue</span> <span
style="font-family: arial;">→</span>\
      \~( (<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span>) /
<span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span> ).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>
<span class="id" type="var">Hb</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">WHILE</span> <span class="id" type="var">b</span> <span
class="id" type="var">DO</span> <span class="id" type="var">c</span>
<span class="id" type="var">END</span>) <span class="id"
type="keyword">as</span> <span class="id" type="var">cw</span> <span
class="id" type="var">eqn</span>:<span class="id"
type="var">Heqcw</span>.\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>)
<span class="id" type="var">Case</span>;\
     <span
class="comment">(\* Most rules don't apply, and we can rule them out \
        by inversion \*)</span>\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heqcw</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">clear</span> <span class="id"
type="var">Heqcw</span>.\
   <span
class="comment">(\* The two interesting cases are the ones for WHILE loops: \*)</span>\
   <span class="id" type="var">Case</span> "E\_WhileEnd". <span
class="comment">(\* contradictory -- b is always true! \*)</span>\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bequiv</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hb</span>.\
     <span class="comment">(\* <span class="inlinecode"><span class="id"
type="tactic">rewrite</span></span> is able to instantiate the quantifier in <span
class="inlinecode"><span class="id"
type="var">st</span></span> \*)</span>\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">Hb</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>.\
   <span class="id" type="var">Case</span> "E\_WhileLoop". <span
class="comment">(\* immediate from the IH \*)</span>\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHceval2</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (WHILE\_true\_nonterm\_informal) {.section}

Explain what the lemma <span class="inlinecode"><span class="id"
type="var">WHILE\_true\_nonterm</span></span> means in English.
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (WHILE\_true) {.section}

Prove the following theorem. *Hint*: You'll want to use <span
class="inlinecode"><span class="id"
type="var">WHILE\_true\_nonterm</span></span> here.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">WHILE\_true</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span>,\
      <span class="id" type="var">bequiv</span> <span class="id"
type="var">b</span> <span class="id" type="var">BTrue</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">cequiv</span>\
        (<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span>)\
        (<span class="id" type="var">WHILE</span> <span class="id"
type="var">BTrue</span> <span class="id" type="var">DO</span> <span
class="id" type="var">SKIP</span> <span class="id"
type="var">END</span>).\
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
type="var">loop\_unrolling</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span>,\
   <span class="id" type="var">cequiv</span>\
     (<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span>)\
     (<span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> (<span
class="id" type="var">c</span>;; <span class="id"
type="var">WHILE</span> <span class="id" type="var">b</span> <span
class="id" type="var">DO</span> <span class="id" type="var">c</span>
<span class="id" type="var">END</span>) <span class="id"
type="var">ELSE</span> <span class="id" type="var">SKIP</span> <span
class="id" type="var">FI</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
<div id="proofcontrol5" class="togglescript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')">

<span class="show"></span>

</div>

<div id="proof5" class="proofscript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')"
style="display: none;">

  <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>.\
   <span class="id" type="tactic">split</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">Hce</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hce</span>; <span class="id" type="tactic">subst</span>.\
     <span class="id" type="var">SCase</span> "loop doesn't run".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_IfFalse</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">E\_Skip</span>.\
     <span class="id" type="var">SCase</span> "loop runs".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_IfTrue</span>. <span class="id"
type="tactic">assumption</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Seq</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">st'</span> := <span class="id"
type="var">st'0</span>). <span class="id"
type="tactic">assumption</span>. <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hce</span>; <span class="id" type="tactic">subst</span>.\
     <span class="id" type="var">SCase</span> "loop runs".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H5</span>; <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_WhileLoop</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">st'</span> :=
<span class="id" type="var">st'0</span>).\
       <span class="id" type="tactic">assumption</span>. <span
class="id" type="tactic">assumption</span>. <span class="id"
type="tactic">assumption</span>.\
     <span class="id" type="var">SCase</span> "loop doesn't run".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H5</span>; <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">E\_WhileEnd</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (seq\_assoc) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">seq\_assoc</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">c1</span> <span class="id" type="var">c2</span> <span
class="id" type="var">c3</span>,\
   <span class="id" type="var">cequiv</span> ((<span class="id"
type="var">c1</span>;;<span class="id" type="var">c2</span>);;<span
class="id" type="var">c3</span>) (<span class="id"
type="var">c1</span>;;(<span class="id" type="var">c2</span>;;<span
class="id" type="var">c3</span>)).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

The Functional Equivalence Axiom {.section}
--------------------------------

<div class="paragraph">

</div>

Finally, let's look at simple equivalences involving assignments. For
example, we might expect to be able to show that <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">::=</span> <span class="inlinecode"><span class="id"
type="var">AId</span></span> <span class="inlinecode"><span class="id"
type="var">X</span></span> is equivalent to <span
class="inlinecode"><span class="id" type="var">SKIP</span></span>.
However, when we try to show it, we get stuck in an interesting way.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">identity\_assignment\_first\_try</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="var">id</span>),\
   <span class="id" type="var">cequiv</span> (<span class="id"
type="var">X</span> ::= <span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) <span class="id"
type="var">SKIP</span>.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">split</span>; <span class="id" type="tactic">intro</span>
<span class="id" type="var">H</span>.\
      <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
        <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">simpl</span>.\
        <span class="id" type="tactic">replace</span> (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">X</span> (<span class="id" type="var">st</span>
<span class="id" type="var">X</span>)) <span class="id"
type="keyword">with</span> <span class="id" type="var">st</span>.\
        <span class="id" type="var">constructor</span>.\
        <span class="comment">(\* Stuck... \*)</span> <span class="id"
type="keyword">Abort</span>.\
\

</div>

<div class="doc">

Here we're stuck. The goal looks reasonable, but in fact it is not
provable! If we look back at the set of lemmas we proved about <span
class="inlinecode"><span class="id" type="var">update</span></span> in
the last chapter, we can see that lemma <span class="inlinecode"><span
class="id" type="var">update\_same</span></span> almost does the job,
but not quite: it says that the original and updated states agree at all
values, but this is not the same thing as saying that they are <span
class="inlinecode">=</span> in Coq's sense!
<div class="paragraph">

</div>

What is going on here? Recall that our states are just functions from
identifiers to values. For Coq, functions are only equal when their
definitions are syntactically the same, modulo simplification. (This is
the only way we can legally apply the <span class="inlinecode"><span
class="id" type="var">refl\_equal</span></span> constructor of the
inductively defined proposition <span class="inlinecode"><span
class="id" type="var">eq</span></span>!) In practice, for functions
built up by repeated uses of the <span class="inlinecode"><span
class="id" type="var">update</span></span> operation, this means that
two functions can be proven equal only if they were constructed using
the *same* <span class="inlinecode"><span class="id"
type="var">update</span></span> operations, applied in the same order.
In the theorem above, the sequence of updates on the first parameter
<span class="inlinecode"><span class="id"
type="var">cequiv</span></span> is one longer than for the second
parameter, so it is no wonder that the equality doesn't hold.
<div class="paragraph">

</div>

###  {.section}

This problem is actually quite general. If we try to prove other simple
facts, such as
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="var">cequiv</span> (<span class="id"
type="var">X</span> ::= <span class="id" type="var">X</span> + 1;;\
             <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> + 1)\
            (<span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> + 2)
<div class="paragraph">

</div>

</div>

or
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="var">cequiv</span> (<span class="id"
type="var">X</span> ::= 1;; <span class="id" type="var">Y</span> ::= 2)\
            (<span class="id" type="var">y</span> ::= 2;; <span
class="id" type="var">X</span> ::= 1)\
   
<div class="paragraph">

</div>

</div>

we'll get stuck in the same way: we'll have two functions that behave
the same way on all inputs, but cannot be proven to be <span
class="inlinecode"><span class="id" type="var">eq</span></span> to each
other.
<div class="paragraph">

</div>

The reasoning principle we would like to use in these situations is
called *functional extensionality*:
<span style="font-family: arial;">∀</span>x, f x = g x
 

------------------------------------------------------------------------

f = g
Although this principle is not derivable in Coq's built-in logic, it is
safe to add it as an additional *axiom*.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Axiom</span> <span class="id"
type="var">functional\_extensionality</span> : <span
style="font-family: arial;">∀</span>{<span class="id"
type="var">X</span> <span class="id" type="var">Y</span>: <span
class="id" type="keyword">Type</span>} {<span class="id"
type="var">f</span> <span class="id" type="var">g</span> : <span
class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Y</span>},\
     (<span style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span>: <span class="id" type="var">X</span>), <span
class="id" type="var">f</span> <span class="id" type="var">x</span> =
<span class="id" type="var">g</span> <span class="id"
type="var">x</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">f</span> = <span class="id" type="var">g</span>.\
\

</div>

<div class="doc">

It can be shown that adding this axiom doesn't introduce any
inconsistencies into Coq. (In this way, it is similar to adding one of
the classical logic axioms, such as <span class="inlinecode"><span
class="id" type="var">excluded\_middle</span></span>.)
<div class="paragraph">

</div>

With the benefit of this axiom we can prove our theorem.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">identity\_assignment</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="var">id</span>),\
   <span class="id" type="var">cequiv</span>\
     (<span class="id" type="var">X</span> ::= <span class="id"
type="var">AId</span> <span class="id" type="var">X</span>)\
     <span class="id" type="var">SKIP</span>.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">split</span>; <span class="id" type="tactic">intro</span>
<span class="id" type="var">H</span>.\
      <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
        <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">simpl</span>.\
        <span class="id" type="tactic">replace</span> (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">X</span> (<span class="id" type="var">st</span>
<span class="id" type="var">X</span>)) <span class="id"
type="keyword">with</span> <span class="id" type="var">st</span>.\
        <span class="id" type="var">constructor</span>.\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">functional\_extensionality</span>. <span class="id"
type="tactic">intro</span>.\
        <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">update\_same</span>; <span class="id"
type="tactic">reflexivity</span>.\
      <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
        <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>.\
        <span class="id" type="tactic">assert</span> (<span class="id"
type="var">st'</span> = (<span class="id" type="var">update</span> <span
class="id" type="var">st'</span> <span class="id" type="var">X</span>
(<span class="id" type="var">st'</span> <span class="id"
type="var">X</span>))).\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">functional\_extensionality</span>. <span class="id"
type="tactic">intro</span>.\
           <span class="id" type="tactic">rewrite</span> <span
class="id" type="var">update\_same</span>; <span class="id"
type="tactic">reflexivity</span>.\
        <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H0</span> <span class="id" type="tactic">at</span> 2.\
        <span class="id" type="var">constructor</span>. <span class="id"
type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (assign\_aequiv) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">assign\_aequiv</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">X</span>
<span class="id" type="var">e</span>,\
   <span class="id" type="var">aequiv</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>) <span
class="id" type="var">e</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">cequiv</span> <span class="id"
type="var">SKIP</span> (<span class="id" type="var">X</span> ::= <span
class="id" type="var">e</span>).\
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

Properties of Behavioral Equivalence {.section}
====================================

<div class="paragraph">

</div>

We now turn to developing some of the properties of the program
equivalences we have defined.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Behavioral Equivalence is an Equivalence {.section}
----------------------------------------

<div class="paragraph">

</div>

First, we verify that the equivalences on <span class="inlinecode"><span
class="id" type="var">aexps</span></span>, <span
class="inlinecode"><span class="id" type="var">bexps</span></span>, and
<span class="inlinecode"><span class="id" type="var">com</span></span>s
really are *equivalences* — i.e., that they are reflexive, symmetric,
and transitive. The proofs are all easy.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">refl\_aequiv</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a</span> : <span class="id" type="var">aexp</span>), <span
class="id" type="var">aequiv</span> <span class="id" type="var">a</span>
<span class="id" type="var">a</span>.\
<div id="proofcontrol6" class="togglescript"
onclick="toggleDisplay('proof6');toggleDisplay('proofcontrol6')">

<span class="show"></span>

</div>

<div id="proof6" class="proofscript"
onclick="toggleDisplay('proof6');toggleDisplay('proofcontrol6')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">a</span> <span class="id" type="var">st</span>. <span
class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">sym\_aequiv</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> : <span
class="id" type="var">aexp</span>),\
   <span class="id" type="var">aequiv</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aequiv</span> <span class="id" type="var">a2</span> <span
class="id" type="var">a1</span>.\
<div id="proofcontrol7" class="togglescript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')">

<span class="show"></span>

</div>

<div id="proof7" class="proofscript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">st</span>. <span
class="id" type="tactic">symmetry</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>. <span
class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">trans\_aequiv</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> <span
class="id" type="var">a3</span> : <span class="id"
type="var">aexp</span>),\
   <span class="id" type="var">aequiv</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aequiv</span> <span class="id" type="var">a2</span> <span
class="id" type="var">a3</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aequiv</span> <span class="id" type="var">a1</span> <span
class="id" type="var">a3</span>.\
<div id="proofcontrol8" class="togglescript"
onclick="toggleDisplay('proof8');toggleDisplay('proofcontrol8')">

<span class="show"></span>

</div>

<div id="proof8" class="proofscript"
onclick="toggleDisplay('proof8');toggleDisplay('proofcontrol8')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">aequiv</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">a1</span> <span class="id"
type="var">a2</span> <span class="id" type="var">a3</span> <span
class="id" type="var">H12</span> <span class="id" type="var">H23</span>
<span class="id" type="var">st</span>.\
   <span class="id" type="tactic">rewrite</span> (<span class="id"
type="var">H12</span> <span class="id" type="var">st</span>). <span
class="id" type="tactic">rewrite</span> (<span class="id"
type="var">H23</span> <span class="id" type="var">st</span>). <span
class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">refl\_bequiv</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">b</span> : <span class="id" type="var">bexp</span>), <span
class="id" type="var">bequiv</span> <span class="id" type="var">b</span>
<span class="id" type="var">b</span>.\
<div id="proofcontrol9" class="togglescript"
onclick="toggleDisplay('proof9');toggleDisplay('proofcontrol9')">

<span class="show"></span>

</div>

<div id="proof9" class="proofscript"
onclick="toggleDisplay('proof9');toggleDisplay('proofcontrol9')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bequiv</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">b</span> <span class="id"
type="var">st</span>. <span class="id" type="tactic">reflexivity</span>.
<span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">sym\_bequiv</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">b1</span> <span class="id" type="var">b2</span> : <span
class="id" type="var">bexp</span>),\
   <span class="id" type="var">bequiv</span> <span class="id"
type="var">b1</span> <span class="id" type="var">b2</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bequiv</span> <span class="id" type="var">b2</span> <span
class="id" type="var">b1</span>.\
<div id="proofcontrol10" class="togglescript"
onclick="toggleDisplay('proof10');toggleDisplay('proofcontrol10')">

<span class="show"></span>

</div>

<div id="proof10" class="proofscript"
onclick="toggleDisplay('proof10');toggleDisplay('proofcontrol10')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bequiv</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">b1</span> <span class="id"
type="var">b2</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">intros</span> <span class="id"
type="var">st</span>. <span class="id" type="tactic">symmetry</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">H</span>. <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">trans\_bequiv</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">b1</span> <span class="id" type="var">b2</span> <span
class="id" type="var">b3</span> : <span class="id"
type="var">bexp</span>),\
   <span class="id" type="var">bequiv</span> <span class="id"
type="var">b1</span> <span class="id" type="var">b2</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bequiv</span> <span class="id" type="var">b2</span> <span
class="id" type="var">b3</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bequiv</span> <span class="id" type="var">b1</span> <span
class="id" type="var">b3</span>.\
<div id="proofcontrol11" class="togglescript"
onclick="toggleDisplay('proof11');toggleDisplay('proofcontrol11')">

<span class="show"></span>

</div>

<div id="proof11" class="proofscript"
onclick="toggleDisplay('proof11');toggleDisplay('proofcontrol11')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bequiv</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">b1</span> <span class="id"
type="var">b2</span> <span class="id" type="var">b3</span> <span
class="id" type="var">H12</span> <span class="id" type="var">H23</span>
<span class="id" type="var">st</span>.\
   <span class="id" type="tactic">rewrite</span> (<span class="id"
type="var">H12</span> <span class="id" type="var">st</span>). <span
class="id" type="tactic">rewrite</span> (<span class="id"
type="var">H23</span> <span class="id" type="var">st</span>). <span
class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">refl\_cequiv</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">c</span> : <span class="id" type="var">com</span>), <span
class="id" type="var">cequiv</span> <span class="id" type="var">c</span>
<span class="id" type="var">c</span>.\
<div id="proofcontrol12" class="togglescript"
onclick="toggleDisplay('proof12');toggleDisplay('proofcontrol12')">

<span class="show"></span>

</div>

<div id="proof12" class="proofscript"
onclick="toggleDisplay('proof12');toggleDisplay('proofcontrol12')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">cequiv</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">c</span> <span class="id"
type="var">st</span> <span class="id" type="var">st'</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">iff\_refl</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">sym\_cequiv</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">c1</span> <span class="id" type="var">c2</span> : <span
class="id" type="var">com</span>),\
   <span class="id" type="var">cequiv</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c2</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">cequiv</span> <span class="id" type="var">c2</span> <span
class="id" type="var">c1</span>.\
<div id="proofcontrol13" class="togglescript"
onclick="toggleDisplay('proof13');toggleDisplay('proofcontrol13')">

<span class="show"></span>

</div>

<div id="proof13" class="proofscript"
onclick="toggleDisplay('proof13');toggleDisplay('proofcontrol13')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">cequiv</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">c2</span> <span class="id" type="var">H</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>.\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">c1</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span> <span style="font-family: arial;">↔</span> <span
class="id" type="var">c2</span> / <span class="id" type="var">st</span>
<span style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">H'</span>.\
     <span class="id" type="var">SCase</span> "Proof of assertion".
<span class="id" type="tactic">apply</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">iff\_sym</span>. <span class="id"
type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">iff\_trans</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P1</span> <span class="id" type="var">P2</span> <span
class="id" type="var">P3</span> : <span class="id"
type="keyword">Prop</span>),\
   (<span class="id" type="var">P1</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">P2</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">P2</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">P3</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">P1</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">P3</span>).\
<div id="proofcontrol14" class="togglescript"
onclick="toggleDisplay('proof14');toggleDisplay('proofcontrol14')">

<span class="show"></span>

</div>

<div id="proof14" class="proofscript"
onclick="toggleDisplay('proof14');toggleDisplay('proofcontrol14')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P1</span> <span class="id" type="var">P2</span> <span
class="id" type="var">P3</span> <span class="id" type="var">H12</span>
<span class="id" type="var">H23</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H12</span>. <span class="id" type="tactic">inversion</span>
<span class="id" type="var">H23</span>.\
   <span class="id" type="tactic">split</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">A</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">H1</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">A</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">H0</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">H2</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">A</span>. <span
class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">trans\_cequiv</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">c1</span> <span class="id" type="var">c2</span> <span
class="id" type="var">c3</span> : <span class="id"
type="var">com</span>),\
   <span class="id" type="var">cequiv</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c2</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">cequiv</span> <span class="id" type="var">c2</span> <span
class="id" type="var">c3</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">cequiv</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c3</span>.\
<div id="proofcontrol15" class="togglescript"
onclick="toggleDisplay('proof15');toggleDisplay('proofcontrol15')">

<span class="show"></span>

</div>

<div id="proof15" class="proofscript"
onclick="toggleDisplay('proof15');toggleDisplay('proofcontrol15')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">cequiv</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">c2</span> <span class="id" type="var">c3</span> <span
class="id" type="var">H12</span> <span class="id" type="var">H23</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">iff\_trans</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">c2</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span>). <span class="id"
type="tactic">apply</span> <span class="id" type="var">H12</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">H23</span>. <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Behavioral Equivalence is a Congruence {.section}
--------------------------------------

<div class="paragraph">

</div>

Less obviously, behavioral equivalence is also a *congruence*. That is,
the equivalence of two subprograms implies the equivalence of the larger
programs in which they are embedded:
aequiv a1 a1'
 

------------------------------------------------------------------------

cequiv (i ::= a1) (i ::= a1')
cequiv c1 c1'
cequiv c2 c2'
 

------------------------------------------------------------------------

cequiv (c1;;c2) (c1';;c2')
...and so on.
<div class="paragraph">

</div>

(Note that we are using the inference rule notation here not as part of
a definition, but simply to write down some valid implications in a
readable format. We prove these implications below.)
<div class="paragraph">

</div>

We will see a concrete example of why these congruence properties are
important in the following section (in the proof of <span
class="inlinecode"><span class="id"
type="var">fold\_constants\_com\_sound</span></span>), but the main idea
is that they allow us to replace a small part of a large program with an
equivalent small part and know that the whole large programs are
equivalent *without* doing an explicit proof about the non-varying parts
— i.e., the "proof burden" of a small change to a large program is
proportional to the size of the change, not the program.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">CAss\_congruence</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">i</span>
<span class="id" type="var">a1</span> <span class="id"
type="var">a1'</span>,\
   <span class="id" type="var">aequiv</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a1'</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">cequiv</span> (<span class="id"
type="var">CAss</span> <span class="id" type="var">i</span> <span
class="id" type="var">a1</span>) (<span class="id"
type="var">CAss</span> <span class="id" type="var">i</span> <span
class="id" type="var">a1'</span>).\
<div id="proofcontrol16" class="togglescript"
onclick="toggleDisplay('proof16');toggleDisplay('proofcontrol16')">

<span class="show"></span>

</div>

<div id="proof16" class="proofscript"
onclick="toggleDisplay('proof16');toggleDisplay('proofcontrol16')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">i</span> <span class="id" type="var">a1</span> <span
class="id" type="var">a2</span> <span class="id" type="var">Heqv</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span>.\
   <span class="id" type="tactic">split</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">Hceval</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hceval</span>. <span class="id" type="tactic">subst</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Ass</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">Heqv</span>. <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hceval</span>. <span class="id" type="tactic">subst</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Ass</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">Heqv</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

The congruence property for loops is a little more interesting, since it
requires induction.
<div class="paragraph">

</div>

*Theorem*: Equivalence is a congruence for <span
class="inlinecode"><span class="id" type="var">WHILE</span></span> —
that is, if <span class="inlinecode"><span class="id"
type="var">b1</span></span> is equivalent to <span
class="inlinecode"><span class="id" type="var">b1'</span></span> and
<span class="inlinecode"><span class="id" type="var">c1</span></span> is
equivalent to <span class="inlinecode"><span class="id"
type="var">c1'</span></span>, then <span class="inlinecode"><span
class="id" type="var">WHILE</span></span> <span class="inlinecode"><span
class="id" type="var">b1</span></span> <span class="inlinecode"><span
class="id" type="var">DO</span></span> <span class="inlinecode"><span
class="id" type="var">c1</span></span> <span class="inlinecode"><span
class="id" type="var">END</span></span> is equivalent to <span
class="inlinecode"><span class="id" type="var">WHILE</span></span> <span
class="inlinecode"><span class="id" type="var">b1'</span></span> <span
class="inlinecode"><span class="id" type="var">DO</span></span> <span
class="inlinecode"><span class="id" type="var">c1'</span></span> <span
class="inlinecode"><span class="id" type="var">END</span></span>.
<div class="paragraph">

</div>

*Proof*: Suppose <span class="inlinecode"><span class="id"
type="var">b1</span></span> is equivalent to <span
class="inlinecode"><span class="id" type="var">b1'</span></span> and
<span class="inlinecode"><span class="id" type="var">c1</span></span> is
equivalent to <span class="inlinecode"><span class="id"
type="var">c1'</span></span>. We must show, for every <span
class="inlinecode"><span class="id" type="var">st</span></span> and
<span class="inlinecode"><span class="id" type="var">st'</span></span>,
that <span class="inlinecode"><span class="id"
type="var">WHILE</span></span> <span class="inlinecode"><span class="id"
type="var">b1</span></span> <span class="inlinecode"><span class="id"
type="var">DO</span></span> <span class="inlinecode"><span class="id"
type="var">c1</span></span> <span class="inlinecode"><span class="id"
type="var">END</span></span> <span class="inlinecode">/</span> <span
class="inlinecode"><span class="id" type="var">st</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇓</span></span>
<span class="inlinecode"><span class="id" type="var">st'</span></span>
iff <span class="inlinecode"><span class="id"
type="var">WHILE</span></span> <span class="inlinecode"><span class="id"
type="var">b1'</span></span> <span class="inlinecode"><span class="id"
type="var">DO</span></span> <span class="inlinecode"><span class="id"
type="var">c1'</span></span> <span class="inlinecode"><span class="id"
type="var">END</span></span> <span class="inlinecode">/</span> <span
class="inlinecode"><span class="id" type="var">st</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇓</span></span>
<span class="inlinecode"><span class="id" type="var">st'</span></span>.
We consider the two directions separately.
<div class="paragraph">

</div>

-   (<span class="inlinecode"><span
    style="font-family: arial;">→</span></span>) We show that <span
    class="inlinecode"><span class="id" type="var">WHILE</span></span>
    <span class="inlinecode"><span class="id"
    type="var">b1</span></span> <span class="inlinecode"><span
    class="id" type="var">DO</span></span> <span
    class="inlinecode"><span class="id" type="var">c1</span></span>
    <span class="inlinecode"><span class="id"
    type="var">END</span></span> <span class="inlinecode">/</span> <span
    class="inlinecode"><span class="id" type="var">st</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⇓</span></span> <span
    class="inlinecode"><span class="id" type="var">st'</span></span>
    implies <span class="inlinecode"><span class="id"
    type="var">WHILE</span></span> <span class="inlinecode"><span
    class="id" type="var">b1'</span></span> <span
    class="inlinecode"><span class="id" type="var">DO</span></span>
    <span class="inlinecode"><span class="id"
    type="var">c1'</span></span> <span class="inlinecode"><span
    class="id" type="var">END</span></span> <span
    class="inlinecode">/</span> <span class="inlinecode"><span
    class="id" type="var">st</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⇓</span></span>
    <span class="inlinecode"><span class="id"
    type="var">st'</span></span>, by induction on a derivation of <span
    class="inlinecode"><span class="id" type="var">WHILE</span></span>
    <span class="inlinecode"><span class="id"
    type="var">b1</span></span> <span class="inlinecode"><span
    class="id" type="var">DO</span></span> <span
    class="inlinecode"><span class="id" type="var">c1</span></span>
    <span class="inlinecode"><span class="id"
    type="var">END</span></span> <span class="inlinecode">/</span> <span
    class="inlinecode"><span class="id" type="var">st</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⇓</span></span> <span
    class="inlinecode"><span class="id" type="var">st'</span></span>.
    The only nontrivial cases are when the final rule in the derivation
    is <span class="inlinecode"><span class="id"
    type="var">E\_WhileEnd</span></span> or <span
    class="inlinecode"><span class="id"
    type="var">E\_WhileLoop</span></span>.
    <div class="paragraph">

    </div>

    -   <span class="inlinecode"><span class="id"
        type="var">E\_WhileEnd</span></span>: In this case, the form of
        the rule gives us <span class="inlinecode"><span class="id"
        type="var">beval</span></span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span class="id" type="var">b1</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">false</span></span> and <span
        class="inlinecode"><span class="id" type="var">st</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">st'</span></span>. But then, since <span
        class="inlinecode"><span class="id" type="var">b1</span></span>
        and <span class="inlinecode"><span class="id"
        type="var">b1'</span></span> are equivalent, we have <span
        class="inlinecode"><span class="id"
        type="var">beval</span></span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span class="id" type="var">b1'</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">false</span></span>, and <span
        class="inlinecode"><span class="id" type="var">E</span>-<span
        class="id" type="var">WhileEnd</span></span> applies, giving us
        <span class="inlinecode"><span class="id"
        type="var">WHILE</span></span> <span class="inlinecode"><span
        class="id" type="var">b1'</span></span> <span
        class="inlinecode"><span class="id" type="var">DO</span></span>
        <span class="inlinecode"><span class="id"
        type="var">c1'</span></span> <span class="inlinecode"><span
        class="id" type="var">END</span></span> <span
        class="inlinecode">/</span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span
        style="font-family: arial;">⇓</span></span> <span
        class="inlinecode"><span class="id"
        type="var">st'</span></span>, as required.
        <div class="paragraph">

        </div>

    -   <span class="inlinecode"><span class="id"
        type="var">E\_WhileLoop</span></span>: The form of the rule now
        gives us <span class="inlinecode"><span class="id"
        type="var">beval</span></span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span class="id" type="var">b1</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">true</span></span>, with <span
        class="inlinecode"><span class="id" type="var">c1</span></span>
        <span class="inlinecode">/</span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span
        style="font-family: arial;">⇓</span></span> <span
        class="inlinecode"><span class="id"
        type="var">st'0</span></span> and <span class="inlinecode"><span
        class="id" type="var">WHILE</span></span> <span
        class="inlinecode"><span class="id" type="var">b1</span></span>
        <span class="inlinecode"><span class="id"
        type="var">DO</span></span> <span class="inlinecode"><span
        class="id" type="var">c1</span></span> <span
        class="inlinecode"><span class="id" type="var">END</span></span>
        <span class="inlinecode">/</span> <span class="inlinecode"><span
        class="id" type="var">st'0</span></span> <span
        class="inlinecode"><span
        style="font-family: arial;">⇓</span></span> <span
        class="inlinecode"><span class="id" type="var">st'</span></span>
        for some state <span class="inlinecode"><span class="id"
        type="var">st'0</span></span>, with the induction hypothesis
        <span class="inlinecode"><span class="id"
        type="var">WHILE</span></span> <span class="inlinecode"><span
        class="id" type="var">b1'</span></span> <span
        class="inlinecode"><span class="id" type="var">DO</span></span>
        <span class="inlinecode"><span class="id"
        type="var">c1'</span></span> <span class="inlinecode"><span
        class="id" type="var">END</span></span> <span
        class="inlinecode">/</span> <span class="inlinecode"><span
        class="id" type="var">st'0</span></span> <span
        class="inlinecode"><span
        style="font-family: arial;">⇓</span></span> <span
        class="inlinecode"><span class="id"
        type="var">st'</span></span>.
        <div class="paragraph">

        </div>

        Since <span class="inlinecode"><span class="id"
        type="var">c1</span></span> and <span class="inlinecode"><span
        class="id" type="var">c1'</span></span> are equivalent, we know
        that <span class="inlinecode"><span class="id"
        type="var">c1'</span></span> <span class="inlinecode">/</span>
        <span class="inlinecode"><span class="id"
        type="var">st</span></span> <span class="inlinecode"><span
        style="font-family: arial;">⇓</span></span> <span
        class="inlinecode"><span class="id"
        type="var">st'0</span></span>. And since <span
        class="inlinecode"><span class="id" type="var">b1</span></span>
        and <span class="inlinecode"><span class="id"
        type="var">b1'</span></span> are equivalent, we have <span
        class="inlinecode"><span class="id"
        type="var">beval</span></span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span class="id" type="var">b1'</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">true</span></span>. Now <span
        class="inlinecode"><span class="id" type="var">E</span>-<span
        class="id" type="var">WhileLoop</span></span> applies, giving us
        <span class="inlinecode"><span class="id"
        type="var">WHILE</span></span> <span class="inlinecode"><span
        class="id" type="var">b1'</span></span> <span
        class="inlinecode"><span class="id" type="var">DO</span></span>
        <span class="inlinecode"><span class="id"
        type="var">c1'</span></span> <span class="inlinecode"><span
        class="id" type="var">END</span></span> <span
        class="inlinecode">/</span> <span class="inlinecode"><span
        class="id" type="var">st</span></span> <span
        class="inlinecode"><span
        style="font-family: arial;">⇓</span></span> <span
        class="inlinecode"><span class="id"
        type="var">st'</span></span>, as required.
        <div class="paragraph">

        </div>
-   (<span class="inlinecode"><span
    style="font-family: arial;">←</span></span>) Similar. ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">CWhile\_congruence</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">b1</span> <span class="id" type="var">b1'</span> <span
class="id" type="var">c1</span> <span class="id" type="var">c1'</span>,\
   <span class="id" type="var">bequiv</span> <span class="id"
type="var">b1</span> <span class="id" type="var">b1'</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">cequiv</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c1'</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">cequiv</span> (<span class="id"
type="var">WHILE</span> <span class="id" type="var">b1</span> <span
class="id" type="var">DO</span> <span class="id" type="var">c1</span>
<span class="id" type="var">END</span>) (<span class="id"
type="var">WHILE</span> <span class="id" type="var">b1'</span> <span
class="id" type="var">DO</span> <span class="id" type="var">c1'</span>
<span class="id" type="var">END</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bequiv</span>,<span class="id" type="var">cequiv</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b1</span> <span class="id" type="var">b1'</span> <span
class="id" type="var">c1</span> <span class="id" type="var">c1'</span>
<span class="id" type="var">Hb1e</span> <span class="id"
type="var">Hc1e</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span>.\
   <span class="id" type="tactic">split</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">Hce</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">WHILE</span> <span class="id" type="var">b1</span> <span
class="id" type="var">DO</span> <span class="id" type="var">c1</span>
<span class="id" type="var">END</span>) <span class="id"
type="keyword">as</span> <span class="id" type="var">cwhile</span> <span
class="id" type="var">eqn</span>:<span class="id"
type="var">Heqcwhile</span>.\
     <span class="id" type="tactic">induction</span> <span class="id"
type="var">Hce</span>; <span class="id" type="tactic">inversion</span>
<span class="id" type="var">Heqcwhile</span>; <span class="id"
type="tactic">subst</span>.\
     <span class="id" type="var">SCase</span> "E\_WhileEnd".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_WhileEnd</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">Hb1e</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>.\
     <span class="id" type="var">SCase</span> "E\_WhileLoop".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_WhileLoop</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">st'</span> :=
<span class="id" type="var">st'</span>).\
       <span class="id" type="var">SSCase</span> "show loop runs". <span
class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">Hb1e</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">H</span>.\
       <span class="id" type="var">SSCase</span> "body execution".\
         <span class="id" type="tactic">apply</span> (<span class="id"
type="var">Hc1e</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span>). <span class="id"
type="tactic">apply</span> <span class="id" type="var">Hce1</span>.\
       <span class="id" type="var">SSCase</span> "subsequent loop
execution".\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHHce2</span>. <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">WHILE</span> <span class="id" type="var">b1'</span> <span
class="id" type="var">DO</span> <span class="id" type="var">c1'</span>
<span class="id" type="var">END</span>) <span class="id"
type="keyword">as</span> <span class="id" type="var">c'while</span>
<span class="id" type="var">eqn</span>:<span class="id"
type="var">Heqc'while</span>.\
     <span class="id" type="tactic">induction</span> <span class="id"
type="var">Hce</span>; <span class="id" type="tactic">inversion</span>
<span class="id" type="var">Heqc'while</span>; <span class="id"
type="tactic">subst</span>.\
     <span class="id" type="var">SCase</span> "E\_WhileEnd".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_WhileEnd</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">Hb1e</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>.\
     <span class="id" type="var">SCase</span> "E\_WhileLoop".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_WhileLoop</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">st'</span> :=
<span class="id" type="var">st'</span>).\
       <span class="id" type="var">SSCase</span> "show loop runs". <span
class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Hb1e</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">H</span>.\
       <span class="id" type="var">SSCase</span> "body execution".\
         <span class="id" type="tactic">apply</span> (<span class="id"
type="var">Hc1e</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span>). <span class="id"
type="tactic">apply</span> <span class="id" type="var">Hce1</span>.\
       <span class="id" type="var">SSCase</span> "subsequent loop
execution".\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHHce2</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars, optional (CSeq\_congruence) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">CSeq\_congruence</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">c1</span> <span class="id" type="var">c1'</span> <span
class="id" type="var">c2</span> <span class="id" type="var">c2'</span>,\
   <span class="id" type="var">cequiv</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c1'</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">cequiv</span> <span class="id" type="var">c2</span> <span
class="id" type="var">c2'</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">cequiv</span> (<span class="id"
type="var">c1</span>;;<span class="id" type="var">c2</span>) (<span
class="id" type="var">c1'</span>;;<span class="id"
type="var">c2'</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (CIf\_congruence) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">CIf\_congruence</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">b'</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c1'</span> <span
class="id" type="var">c2</span> <span class="id" type="var">c2'</span>,\
   <span class="id" type="var">bequiv</span> <span class="id"
type="var">b</span> <span class="id" type="var">b'</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">cequiv</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c1'</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">cequiv</span> <span class="id" type="var">c2</span> <span
class="id" type="var">c2'</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">cequiv</span> (<span class="id"
type="var">IFB</span> <span class="id" type="var">b</span> <span
class="id" type="var">THEN</span> <span class="id" type="var">c1</span>
<span class="id" type="var">ELSE</span> <span class="id"
type="var">c2</span> <span class="id" type="var">FI</span>) (<span
class="id" type="var">IFB</span> <span class="id" type="var">b'</span>
<span class="id" type="var">THEN</span> <span class="id"
type="var">c1'</span> <span class="id" type="var">ELSE</span> <span
class="id" type="var">c2'</span> <span class="id"
type="var">FI</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

For example, here are two equivalent programs and a proof of their
equivalence...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">congruence\_example</span>:\
   <span class="id" type="var">cequiv</span>\
     <span class="comment">(\* Program 1: \*)</span>\
     (<span class="id" type="var">X</span> ::= <span class="id"
type="var">ANum</span> 0;;\
      <span class="id" type="var">IFB</span> (<span class="id"
type="var">BEq</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
0))\
      <span class="id" type="var">THEN</span>\
        <span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 0\
      <span class="id" type="var">ELSE</span>\
        <span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 42\
      <span class="id" type="var">FI</span>)\
     <span class="comment">(\* Program 2: \*)</span>\
     (<span class="id" type="var">X</span> ::= <span class="id"
type="var">ANum</span> 0;;\
      <span class="id" type="var">IFB</span> (<span class="id"
type="var">BEq</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
0))\
      <span class="id" type="var">THEN</span>\
        <span class="id" type="var">Y</span> ::= <span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">AId</span>
<span class="id" type="var">X</span>) <span
class="comment">(\* \<--- changed here \*)</span>\
      <span class="id" type="var">ELSE</span>\
        <span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 42\
      <span class="id" type="var">FI</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">CSeq\_congruence</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">refl\_cequiv</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">CIf\_congruence</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">refl\_bequiv</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">CAss\_congruence</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">aequiv</span>.
<span class="id" type="tactic">simpl</span>.\
         <span class="id" type="tactic">symmetry</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">minus\_diag</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">refl\_cequiv</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Program Transformations {.section}
=======================

<div class="paragraph">

</div>

A *program transformation* is a function that takes a program as input
and produces some variant of the program as its output. Compiler
optimizations such as constant folding are a canonical example, but
there are many others.
<div class="paragraph">

</div>

A program transformation is *sound* if it preserves the behavior of the
original program.
<div class="paragraph">

</div>

We can define a notion of soundness for translations of <span
class="inlinecode"><span class="id" type="var">aexp</span></span>s,
<span class="inlinecode"><span class="id"
type="var">bexp</span></span>s, and <span class="inlinecode"><span
class="id" type="var">com</span></span>s.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">atrans\_sound</span> (<span class="id"
type="var">atrans</span> : <span class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>) : <span class="id" type="keyword">Prop</span>
:=\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">a</span> : <span class="id" type="var">aexp</span>),\
     <span class="id" type="var">aequiv</span> <span class="id"
type="var">a</span> (<span class="id" type="var">atrans</span> <span
class="id" type="var">a</span>).\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">btrans\_sound</span> (<span class="id"
type="var">btrans</span> : <span class="id" type="var">bexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bexp</span>) : <span class="id" type="keyword">Prop</span>
:=\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">b</span> : <span class="id" type="var">bexp</span>),\
     <span class="id" type="var">bequiv</span> <span class="id"
type="var">b</span> (<span class="id" type="var">btrans</span> <span
class="id" type="var">b</span>).\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">ctrans\_sound</span> (<span class="id"
type="var">ctrans</span> : <span class="id" type="var">com</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">com</span>) : <span class="id" type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">c</span> : <span class="id" type="var">com</span>),\
     <span class="id" type="var">cequiv</span> <span class="id"
type="var">c</span> (<span class="id" type="var">ctrans</span> <span
class="id" type="var">c</span>).\
\

</div>

<div class="doc">

The Constant-Folding Transformation {.section}
-----------------------------------

<div class="paragraph">

</div>

An expression is *constant* when it contains no variable references.
<div class="paragraph">

</div>

Constant folding is an optimization that finds constant expressions and
replaces them by their values.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">fold\_constants\_aexp</span> (<span class="id"
type="var">a</span> : <span class="id" type="var">aexp</span>) : <span
class="id" type="var">aexp</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">a</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">ANum</span> <span class="id"
type="var">n</span> ⇒ <span class="id" type="var">ANum</span> <span
class="id" type="var">n</span>\
   | <span class="id" type="var">AId</span> <span class="id"
type="var">i</span> ⇒ <span class="id" type="var">AId</span> <span
class="id" type="var">i</span>\
   | <span class="id" type="var">APlus</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒\
       <span class="id" type="keyword">match</span> (<span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a1</span>, <span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a2</span>) <span class="id" type="keyword">with</span>\
       | (<span class="id" type="var">ANum</span> <span class="id"
type="var">n1</span>, <span class="id" type="var">ANum</span> <span
class="id" type="var">n2</span>) ⇒ <span class="id"
type="var">ANum</span> (<span class="id" type="var">n1</span> + <span
class="id" type="var">n2</span>)\
       | (<span class="id" type="var">a1'</span>, <span class="id"
type="var">a2'</span>) ⇒ <span class="id" type="var">APlus</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2'</span>\
       <span class="id" type="keyword">end</span>\
   | <span class="id" type="var">AMinus</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒\
       <span class="id" type="keyword">match</span> (<span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a1</span>, <span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a2</span>) <span class="id" type="keyword">with</span>\
       | (<span class="id" type="var">ANum</span> <span class="id"
type="var">n1</span>, <span class="id" type="var">ANum</span> <span
class="id" type="var">n2</span>) ⇒ <span class="id"
type="var">ANum</span> (<span class="id" type="var">n1</span> - <span
class="id" type="var">n2</span>)\
       | (<span class="id" type="var">a1'</span>, <span class="id"
type="var">a2'</span>) ⇒ <span class="id" type="var">AMinus</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2'</span>\
       <span class="id" type="keyword">end</span>\
   | <span class="id" type="var">AMult</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒\
       <span class="id" type="keyword">match</span> (<span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a1</span>, <span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a2</span>) <span class="id" type="keyword">with</span>\
       | (<span class="id" type="var">ANum</span> <span class="id"
type="var">n1</span>, <span class="id" type="var">ANum</span> <span
class="id" type="var">n2</span>) ⇒ <span class="id"
type="var">ANum</span> (<span class="id" type="var">n1</span> × <span
class="id" type="var">n2</span>)\
       | (<span class="id" type="var">a1'</span>, <span class="id"
type="var">a2'</span>) ⇒ <span class="id" type="var">AMult</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2'</span>\
       <span class="id" type="keyword">end</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">fold\_aexp\_ex1</span> :\
     <span class="id" type="var">fold\_constants\_aexp</span>\
       (<span class="id" type="var">AMult</span> (<span class="id"
type="var">APlus</span> (<span class="id" type="var">ANum</span> 1)
(<span class="id" type="var">ANum</span> 2)) (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>))\
   = <span class="id" type="var">AMult</span> (<span class="id"
type="var">ANum</span> 3) (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Note that this version of constant folding doesn't eliminate trivial
additions, etc. — we are focusing attention on a single optimization for
the sake of simplicity. It is not hard to incorporate other ways of
simplifying expressions; the definitions and proofs just get longer.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">fold\_aexp\_ex2</span> :\
     <span class="id" type="var">fold\_constants\_aexp</span>\
       (<span class="id" type="var">AMinus</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">APlus</span> (<span class="id"
type="var">AMult</span> (<span class="id" type="var">ANum</span> 0)
(<span class="id" type="var">ANum</span> 6)) (<span class="id"
type="var">AId</span> <span class="id" type="var">Y</span>)))\
   = <span class="id" type="var">AMinus</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">APlus</span> (<span class="id"
type="var">ANum</span> 0) (<span class="id" type="var">AId</span> <span
class="id" type="var">Y</span>)).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

Not only can we lift <span class="inlinecode"><span class="id"
type="var">fold\_constants\_aexp</span></span> to <span
class="inlinecode"><span class="id" type="var">bexp</span></span>s (in
the <span class="inlinecode"><span class="id"
type="var">BEq</span></span> and <span class="inlinecode"><span
class="id" type="var">BLe</span></span> cases), we can also find
constant *boolean* expressions and reduce them in-place.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">fold\_constants\_bexp</span> (<span class="id"
type="var">b</span> : <span class="id" type="var">bexp</span>) : <span
class="id" type="var">bexp</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">b</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">BTrue</span> ⇒ <span class="id"
type="var">BTrue</span>\
   | <span class="id" type="var">BFalse</span> ⇒ <span class="id"
type="var">BFalse</span>\
   | <span class="id" type="var">BEq</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒\
       <span class="id" type="keyword">match</span> (<span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a1</span>, <span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a2</span>) <span class="id" type="keyword">with</span>\
       | (<span class="id" type="var">ANum</span> <span class="id"
type="var">n1</span>, <span class="id" type="var">ANum</span> <span
class="id" type="var">n2</span>) ⇒ <span class="id"
type="keyword">if</span> <span class="id" type="var">beq\_nat</span>
<span class="id" type="var">n1</span> <span class="id"
type="var">n2</span> <span class="id" type="keyword">then</span> <span
class="id" type="var">BTrue</span> <span class="id"
type="keyword">else</span> <span class="id" type="var">BFalse</span>\
       | (<span class="id" type="var">a1'</span>, <span class="id"
type="var">a2'</span>) ⇒ <span class="id" type="var">BEq</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2'</span>\
       <span class="id" type="keyword">end</span>\
   | <span class="id" type="var">BLe</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒\
       <span class="id" type="keyword">match</span> (<span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a1</span>, <span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a2</span>) <span class="id" type="keyword">with</span>\
       | (<span class="id" type="var">ANum</span> <span class="id"
type="var">n1</span>, <span class="id" type="var">ANum</span> <span
class="id" type="var">n2</span>) ⇒ <span class="id"
type="keyword">if</span> <span class="id" type="var">ble\_nat</span>
<span class="id" type="var">n1</span> <span class="id"
type="var">n2</span> <span class="id" type="keyword">then</span> <span
class="id" type="var">BTrue</span> <span class="id"
type="keyword">else</span> <span class="id" type="var">BFalse</span>\
       | (<span class="id" type="var">a1'</span>, <span class="id"
type="var">a2'</span>) ⇒ <span class="id" type="var">BLe</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2'</span>\
       <span class="id" type="keyword">end</span>\
   | <span class="id" type="var">BNot</span> <span class="id"
type="var">b1</span> ⇒\
       <span class="id" type="keyword">match</span> (<span class="id"
type="var">fold\_constants\_bexp</span> <span class="id"
type="var">b1</span>) <span class="id" type="keyword">with</span>\
       | <span class="id" type="var">BTrue</span> ⇒ <span class="id"
type="var">BFalse</span>\
       | <span class="id" type="var">BFalse</span> ⇒ <span class="id"
type="var">BTrue</span>\
       | <span class="id" type="var">b1'</span> ⇒ <span class="id"
type="var">BNot</span> <span class="id" type="var">b1'</span>\
       <span class="id" type="keyword">end</span>\
   | <span class="id" type="var">BAnd</span> <span class="id"
type="var">b1</span> <span class="id" type="var">b2</span> ⇒\
       <span class="id" type="keyword">match</span> (<span class="id"
type="var">fold\_constants\_bexp</span> <span class="id"
type="var">b1</span>, <span class="id"
type="var">fold\_constants\_bexp</span> <span class="id"
type="var">b2</span>) <span class="id" type="keyword">with</span>\
       | (<span class="id" type="var">BTrue</span>, <span class="id"
type="var">BTrue</span>) ⇒ <span class="id" type="var">BTrue</span>\
       | (<span class="id" type="var">BTrue</span>, <span class="id"
type="var">BFalse</span>) ⇒ <span class="id" type="var">BFalse</span>\
       | (<span class="id" type="var">BFalse</span>, <span class="id"
type="var">BTrue</span>) ⇒ <span class="id" type="var">BFalse</span>\
       | (<span class="id" type="var">BFalse</span>, <span class="id"
type="var">BFalse</span>) ⇒ <span class="id" type="var">BFalse</span>\
       | (<span class="id" type="var">b1'</span>, <span class="id"
type="var">b2'</span>) ⇒ <span class="id" type="var">BAnd</span> <span
class="id" type="var">b1'</span> <span class="id" type="var">b2'</span>\
       <span class="id" type="keyword">end</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">fold\_bexp\_ex1</span> :\
     <span class="id" type="var">fold\_constants\_bexp</span> (<span
class="id" type="var">BAnd</span> <span class="id"
type="var">BTrue</span> (<span class="id" type="var">BNot</span> (<span
class="id" type="var">BAnd</span> <span class="id"
type="var">BFalse</span> <span class="id" type="var">BTrue</span>)))\
   = <span class="id" type="var">BTrue</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">fold\_bexp\_ex2</span> :\
     <span class="id" type="var">fold\_constants\_bexp</span>\
       (<span class="id" type="var">BAnd</span> (<span class="id"
type="var">BEq</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">AId</span>
<span class="id" type="var">Y</span>))\
             (<span class="id" type="var">BEq</span> (<span class="id"
type="var">ANum</span> 0)\
                  (<span class="id" type="var">AMinus</span> (<span
class="id" type="var">ANum</span> 2) (<span class="id"
type="var">APlus</span> (<span class="id" type="var">ANum</span> 1)
(<span class="id" type="var">ANum</span> 1)))))\
   = <span class="id" type="var">BAnd</span> (<span class="id"
type="var">BEq</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">AId</span>
<span class="id" type="var">Y</span>)) <span class="id"
type="var">BTrue</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

To fold constants in a command, we apply the appropriate folding
functions on all embedded expressions.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">fold\_constants\_com</span> (<span class="id"
type="var">c</span> : <span class="id" type="var">com</span>) : <span
class="id" type="var">com</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">c</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">SKIP</span> ⇒\
       <span class="id" type="var">SKIP</span>\
   | <span class="id" type="var">i</span> ::= <span class="id"
type="var">a</span> ⇒\
       <span class="id" type="var">CAss</span> <span class="id"
type="var">i</span> (<span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a</span>)\
   | <span class="id" type="var">c1</span> ;; <span class="id"
type="var">c2</span> ⇒\
       (<span class="id" type="var">fold\_constants\_com</span> <span
class="id" type="var">c1</span>) ;; (<span class="id"
type="var">fold\_constants\_com</span> <span class="id"
type="var">c2</span>)\
   | <span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span> ⇒\
       <span class="id" type="keyword">match</span> <span class="id"
type="var">fold\_constants\_bexp</span> <span class="id"
type="var">b</span> <span class="id" type="keyword">with</span>\
       | <span class="id" type="var">BTrue</span> ⇒ <span class="id"
type="var">fold\_constants\_com</span> <span class="id"
type="var">c1</span>\
       | <span class="id" type="var">BFalse</span> ⇒ <span class="id"
type="var">fold\_constants\_com</span> <span class="id"
type="var">c2</span>\
       | <span class="id" type="var">b'</span> ⇒ <span class="id"
type="var">IFB</span> <span class="id" type="var">b'</span> <span
class="id" type="var">THEN</span> <span class="id"
type="var">fold\_constants\_com</span> <span class="id"
type="var">c1</span>\
                      <span class="id" type="var">ELSE</span> <span
class="id" type="var">fold\_constants\_com</span> <span class="id"
type="var">c2</span> <span class="id" type="var">FI</span>\
       <span class="id" type="keyword">end</span>\
   | <span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span> ⇒\
       <span class="id" type="keyword">match</span> <span class="id"
type="var">fold\_constants\_bexp</span> <span class="id"
type="var">b</span> <span class="id" type="keyword">with</span>\
       | <span class="id" type="var">BTrue</span> ⇒ <span class="id"
type="var">WHILE</span> <span class="id" type="var">BTrue</span> <span
class="id" type="var">DO</span> <span class="id" type="var">SKIP</span>
<span class="id" type="var">END</span>\
       | <span class="id" type="var">BFalse</span> ⇒ <span class="id"
type="var">SKIP</span>\
       | <span class="id" type="var">b'</span> ⇒ <span class="id"
type="var">WHILE</span> <span class="id" type="var">b'</span> <span
class="id" type="var">DO</span> (<span class="id"
type="var">fold\_constants\_com</span> <span class="id"
type="var">c</span>) <span class="id" type="var">END</span>\
       <span class="id" type="keyword">end</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

###  {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">fold\_com\_ex1</span> :\
   <span class="id" type="var">fold\_constants\_com</span>\
     <span class="comment">(\* Original program: \*)</span>\
     (<span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">ANum</span> 4)
(<span class="id" type="var">ANum</span> 5);;\
      <span class="id" type="var">Y</span> ::= <span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
3);;\
      <span class="id" type="var">IFB</span> <span class="id"
type="var">BEq</span> (<span class="id" type="var">AMinus</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">AId</span> <span class="id"
type="var">Y</span>)) (<span class="id" type="var">APlus</span> (<span
class="id" type="var">ANum</span> 2) (<span class="id"
type="var">ANum</span> 4)) <span class="id" type="var">THEN</span>\
        <span class="id" type="var">SKIP</span>\
      <span class="id" type="var">ELSE</span>\
        <span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 0\
      <span class="id" type="var">FI</span>;;\
      <span class="id" type="var">IFB</span> <span class="id"
type="var">BLe</span> (<span class="id" type="var">ANum</span> 0) (<span
class="id" type="var">AMinus</span> (<span class="id"
type="var">ANum</span> 4) (<span class="id" type="var">APlus</span>
(<span class="id" type="var">ANum</span> 2) (<span class="id"
type="var">ANum</span> 1))) <span class="id" type="var">THEN</span>\
        <span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 0\
      <span class="id" type="var">ELSE</span>\
        <span class="id" type="var">SKIP</span>\
      <span class="id" type="var">FI</span>;;\
      <span class="id" type="var">WHILE</span> <span class="id"
type="var">BEq</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">Y</span>) (<span class="id" type="var">ANum</span>
0) <span class="id" type="var">DO</span>\
        <span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1)\
      <span class="id" type="var">END</span>)\
   = <span class="comment">(\* After constant folding: \*)</span>\
     (<span class="id" type="var">X</span> ::= <span class="id"
type="var">ANum</span> 9;;\
      <span class="id" type="var">Y</span> ::= <span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
3);;\
      <span class="id" type="var">IFB</span> <span class="id"
type="var">BEq</span> (<span class="id" type="var">AMinus</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">AId</span> <span class="id"
type="var">Y</span>)) (<span class="id" type="var">ANum</span> 6) <span
class="id" type="var">THEN</span>\
        <span class="id" type="var">SKIP</span>\
      <span class="id" type="var">ELSE</span>\
        (<span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 0)\
      <span class="id" type="var">FI</span>;;\
      <span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 0;;\
      <span class="id" type="var">WHILE</span> <span class="id"
type="var">BEq</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">Y</span>) (<span class="id" type="var">ANum</span>
0) <span class="id" type="var">DO</span>\
        <span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1)\
      <span class="id" type="var">END</span>).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Soundness of Constant Folding {.section}
-----------------------------

<div class="paragraph">

</div>

Now we need to show that what we've done is correct.
<div class="paragraph">

</div>

Here's the proof for arithmetic expressions:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">fold\_constants\_aexp\_sound</span> :\
   <span class="id" type="var">atrans\_sound</span> <span class="id"
type="var">fold\_constants\_aexp</span>.\
<div id="proofcontrol17" class="togglescript"
onclick="toggleDisplay('proof17');toggleDisplay('proofcontrol17')">

<span class="show"></span>

</div>

<div id="proof17" class="proofscript"
onclick="toggleDisplay('proof17');toggleDisplay('proofcontrol17')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">atrans\_sound</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">a</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">aequiv</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">st</span>.\
   <span class="id" type="var">aexp\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">a</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">simpl</span>;\
     <span
class="comment">(\* ANum and AId follow immediately \*)</span>\
     <span class="id" type="tactic">try</span> <span class="id"
type="tactic">reflexivity</span>;\
     <span
class="comment">(\* APlus, AMinus, and AMult follow from the IH\
        and the observation that\
               aeval st (APlus a1 a2) \
             = ANum ((aeval st a1) + (aeval st a2)) \
             = aeval st (ANum ((aeval st a1) + (aeval st a2)))\
        (and similarly for AMinus/minus and AMult/mult) \*)</span>\
     <span class="id" type="tactic">try</span> (<span class="id"
type="tactic">destruct</span> (<span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a1</span>);\
          <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a2</span>);\
          <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHa1</span>; <span class="id" type="tactic">rewrite</span>
<span class="id" type="var">IHa2</span>; <span class="id"
type="tactic">reflexivity</span>). <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 3 stars, optional (fold\_bexp\_Eq\_informal) {.section}

Here is an informal proof of the <span class="inlinecode"><span
class="id" type="var">BEq</span></span> case of the soundness argument
for boolean expression constant folding. Read it carefully and compare
it to the formal proof that follows. Then fill in the <span
class="inlinecode"><span class="id" type="var">BLe</span></span> case of
the formal proof (without looking at the <span class="inlinecode"><span
class="id" type="var">BEq</span></span> case, if possible).
<div class="paragraph">

</div>

*Theorem*: The constant folding function for booleans, <span
class="inlinecode"><span class="id"
type="var">fold\_constants\_bexp</span></span>, is sound.
<div class="paragraph">

</div>

*Proof*: We must show that <span class="inlinecode"><span class="id"
type="var">b</span></span> is equivalent to <span
class="inlinecode"><span class="id"
type="var">fold\_constants\_bexp</span></span>, for all boolean
expressions <span class="inlinecode"><span class="id"
type="var">b</span></span>. Proceed by induction on <span
class="inlinecode"><span class="id" type="var">b</span></span>. We show
just the case where <span class="inlinecode"><span class="id"
type="var">b</span></span> has the form <span class="inlinecode"><span
class="id" type="var">BEq</span></span> <span class="inlinecode"><span
class="id" type="var">a1</span></span> <span class="inlinecode"><span
class="id" type="var">a2</span></span>.
<div class="paragraph">

</div>

In this case, we must show
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">BEq</span> <span
class="id" type="var">a1</span> <span class="id" type="var">a2</span>) \
      = <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> (<span class="id"
type="var">fold\_constants\_bexp</span> (<span class="id"
type="var">BEq</span> <span class="id" type="var">a1</span> <span
class="id" type="var">a2</span>)).
<div class="paragraph">

</div>

</div>

There are two cases to consider:
<div class="paragraph">

</div>

-   First, suppose <span class="inlinecode"><span class="id"
    type="var">fold\_constants\_aexp</span></span> <span
    class="inlinecode"><span class="id" type="var">a1</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">ANum</span></span> <span
    class="inlinecode"><span class="id" type="var">n1</span></span> and
    <span class="inlinecode"><span class="id"
    type="var">fold\_constants\_aexp</span></span> <span
    class="inlinecode"><span class="id" type="var">a2</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">ANum</span></span> <span
    class="inlinecode"><span class="id" type="var">n2</span></span> for
    some <span class="inlinecode"><span class="id"
    type="var">n1</span></span> and <span class="inlinecode"><span
    class="id" type="var">n2</span></span>.
    <div class="paragraph">

    </div>

    In this case, we have
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span class="id" type="var">fold\_constants\_bexp</span> (<span
    class="id" type="var">BEq</span> <span class="id"
    type="var">a1</span> <span class="id" type="var">a2</span>) \
       = <span class="id" type="keyword">if</span> <span class="id"
    type="var">beq\_nat</span> <span class="id"
    type="var">n1</span> <span class="id" type="var">n2</span> <span
    class="id" type="keyword">then</span> <span class="id"
    type="var">BTrue</span> <span class="id"
    type="keyword">else</span> <span class="id" type="var">BFalse</span>
    <div class="paragraph">

    </div>

    </div>

    and
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span class="id" type="var">beval</span> <span class="id"
    type="var">st</span> (<span class="id" type="var">BEq</span> <span
    class="id" type="var">a1</span> <span class="id"
    type="var">a2</span>) \
       = <span class="id" type="var">beq\_nat</span> (<span class="id"
    type="var">aeval</span> <span class="id" type="var">st</span> <span
    class="id" type="var">a1</span>) (<span class="id"
    type="var">aeval</span> <span class="id" type="var">st</span> <span
    class="id" type="var">a2</span>).
    <div class="paragraph">

    </div>

    </div>

    By the soundness of constant folding for arithmetic expressions
    (Lemma <span class="inlinecode"><span class="id"
    type="var">fold\_constants\_aexp\_sound</span></span>), we know
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span class="id" type="var">aeval</span> <span class="id"
    type="var">st</span> <span class="id" type="var">a1</span> \
       = <span class="id" type="var">aeval</span> <span class="id"
    type="var">st</span> (<span class="id"
    type="var">fold\_constants\_aexp</span> <span class="id"
    type="var">a1</span>) \
       = <span class="id" type="var">aeval</span> <span class="id"
    type="var">st</span> (<span class="id" type="var">ANum</span> <span
    class="id" type="var">n1</span>) \
       = <span class="id" type="var">n1</span>
    <div class="paragraph">

    </div>

    </div>

    and
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span class="id" type="var">aeval</span> <span class="id"
    type="var">st</span> <span class="id" type="var">a2</span> \
       = <span class="id" type="var">aeval</span> <span class="id"
    type="var">st</span> (<span class="id"
    type="var">fold\_constants\_aexp</span> <span class="id"
    type="var">a2</span>) \
       = <span class="id" type="var">aeval</span> <span class="id"
    type="var">st</span> (<span class="id" type="var">ANum</span> <span
    class="id" type="var">n2</span>) \
       = <span class="id" type="var">n2</span>,
    <div class="paragraph">

    </div>

    </div>

    so
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span class="id" type="var">beval</span> <span class="id"
    type="var">st</span> (<span class="id" type="var">BEq</span> <span
    class="id" type="var">a1</span> <span class="id"
    type="var">a2</span>) \
       = <span class="id" type="var">beq\_nat</span> (<span class="id"
    type="var">aeval</span> <span class="id"
    type="var">a1</span>) (<span class="id"
    type="var">aeval</span> <span class="id" type="var">a2</span>)\
       = <span class="id" type="var">beq\_nat</span> <span class="id"
    type="var">n1</span> <span class="id" type="var">n2</span>.
    <div class="paragraph">

    </div>

    </div>

    Also, it is easy to see (by considering the cases <span
    class="inlinecode"><span class="id" type="var">n1</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">n2</span></span> and <span
    class="inlinecode"><span class="id" type="var">n1</span></span>
    <span class="inlinecode">≠</span> <span class="inlinecode"><span
    class="id" type="var">n2</span></span> separately) that
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span class="id" type="var">beval</span> <span class="id"
    type="var">st</span> (<span class="id"
    type="keyword">if</span> <span class="id"
    type="var">beq\_nat</span> <span class="id"
    type="var">n1</span> <span class="id" type="var">n2</span> <span
    class="id" type="keyword">then</span> <span class="id"
    type="var">BTrue</span> <span class="id"
    type="keyword">else</span> <span class="id"
    type="var">BFalse</span>)\
       = <span class="id" type="keyword">if</span> <span class="id"
    type="var">beq\_nat</span> <span class="id"
    type="var">n1</span> <span class="id" type="var">n2</span> <span
    class="id" type="keyword">then</span> <span class="id"
    type="var">beval</span> <span class="id" type="var">st</span> <span
    class="id" type="var">BTrue</span> <span class="id"
    type="keyword">else</span> <span class="id"
    type="var">beval</span> <span class="id" type="var">st</span> <span
    class="id" type="var">BFalse</span>\
       = <span class="id" type="keyword">if</span> <span class="id"
    type="var">beq\_nat</span> <span class="id"
    type="var">n1</span> <span class="id" type="var">n2</span> <span
    class="id" type="keyword">then</span> <span class="id"
    type="var">true</span> <span class="id"
    type="keyword">else</span> <span class="id" type="var">false</span>\
       = <span class="id" type="var">beq\_nat</span> <span class="id"
    type="var">n1</span> <span class="id" type="var">n2</span>.
    <div class="paragraph">

    </div>

    </div>

    So
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span class="id" type="var">beval</span> <span class="id"
    type="var">st</span> (<span class="id" type="var">BEq</span> <span
    class="id" type="var">a1</span> <span class="id"
    type="var">a2</span>) \
       = <span class="id" type="var">beq\_nat</span> <span class="id"
    type="var">n1</span> <span class="id" type="var">n2</span>.\
       = <span class="id" type="var">beval</span> <span class="id"
    type="var">st</span> (<span class="id"
    type="keyword">if</span> <span class="id"
    type="var">beq\_nat</span> <span class="id"
    type="var">n1</span> <span class="id" type="var">n2</span> <span
    class="id" type="keyword">then</span> <span class="id"
    type="var">BTrue</span> <span class="id"
    type="keyword">else</span> <span class="id"
    type="var">BFalse</span>),
    <div class="paragraph">

    </div>

    </div>

    as required.
    <div class="paragraph">

    </div>

-   Otherwise, one of <span class="inlinecode"><span class="id"
    type="var">fold\_constants\_aexp</span></span> <span
    class="inlinecode"><span class="id" type="var">a1</span></span> and
    <span class="inlinecode"><span class="id"
    type="var">fold\_constants\_aexp</span></span> <span
    class="inlinecode"><span class="id" type="var">a2</span></span> is
    not a constant. In this case, we must show
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span class="id" type="var">beval</span> <span class="id"
    type="var">st</span> (<span class="id" type="var">BEq</span> <span
    class="id" type="var">a1</span> <span class="id"
    type="var">a2</span>) \
       = <span class="id" type="var">beval</span> <span class="id"
    type="var">st</span> (<span class="id" type="var">BEq</span> (<span
    class="id" type="var">fold\_constants\_aexp</span> <span class="id"
    type="var">a1</span>)\
                       (<span class="id"
    type="var">fold\_constants\_aexp</span> <span class="id"
    type="var">a2</span>)),
    <div class="paragraph">

    </div>

    </div>

    which, by the definition of <span class="inlinecode"><span
    class="id" type="var">beval</span></span>, is the same as showing
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span class="id" type="var">beq\_nat</span> (<span class="id"
    type="var">aeval</span> <span class="id" type="var">st</span> <span
    class="id" type="var">a1</span>) (<span class="id"
    type="var">aeval</span> <span class="id" type="var">st</span> <span
    class="id" type="var">a2</span>) \
       = <span class="id" type="var">beq\_nat</span> (<span class="id"
    type="var">aeval</span> <span class="id" type="var">st</span> (<span
    class="id" type="var">fold\_constants\_aexp</span> <span class="id"
    type="var">a1</span>))\
                 (<span class="id" type="var">aeval</span> <span
    class="id" type="var">st</span> (<span class="id"
    type="var">fold\_constants\_aexp</span> <span class="id"
    type="var">a2</span>)).
    <div class="paragraph">

    </div>

    </div>

    But the soundness of constant folding for arithmetic expressions
    (<span class="inlinecode"><span class="id"
    type="var">fold\_constants\_aexp\_sound</span></span>) gives us
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">aeval</span> <span class="id"
    type="var">st</span> <span class="id" type="var">a1</span> = <span
    class="id" type="var">aeval</span> <span class="id"
    type="var">st</span> (<span class="id"
    type="var">fold\_constants\_aexp</span> <span class="id"
    type="var">a1</span>)\
       <span class="id" type="var">aeval</span> <span class="id"
    type="var">st</span> <span class="id" type="var">a2</span> = <span
    class="id" type="var">aeval</span> <span class="id"
    type="var">st</span> (<span class="id"
    type="var">fold\_constants\_aexp</span> <span class="id"
    type="var">a2</span>),
    <div class="paragraph">

    </div>

    </div>

    completing the case. ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">fold\_constants\_bexp\_sound</span>:\
   <span class="id" type="var">btrans\_sound</span> <span class="id"
type="var">fold\_constants\_bexp</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">btrans\_sound</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">b</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">bequiv</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">st</span>.\
   <span class="id" type="var">bexp\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">b</span>)
<span class="id" type="var">Case</span>;\
     <span
class="comment">(\* BTrue and BFalse are immediate \*)</span>\
     <span class="id" type="tactic">try</span> <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "BEq".\
     <span
class="comment">(\* Doing induction when there are a lot of constructors makes\
        specifying variable names a chore, but Coq doesn't always\
        choose nice variable names.  We can rename entries in the\
        context with the <span class="inlinecode"><span class="id"
type="tactic">rename</span></span> tactic: <span
class="inlinecode"><span class="id" type="tactic">rename</span></span>
<span class="inlinecode"><span class="id" type="var">a</span></span>
<span class="inlinecode"><span class="id" type="var">into</span></span>
<span class="inlinecode"><span class="id"
type="var">a1</span></span> will\
        change <span class="inlinecode"><span class="id"
type="var">a</span></span> to <span class="inlinecode"><span class="id"
type="var">a1</span></span> in the current goal and context. \*)</span>\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">a</span> <span class="id" type="var">into</span> <span
class="id" type="var">a1</span>. <span class="id"
type="tactic">rename</span> <span class="id" type="var">a0</span> <span
class="id" type="var">into</span> <span class="id" type="var">a2</span>.
<span class="id" type="tactic">simpl</span>.\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a1</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">a1'</span> <span class="id"
type="var">eqn</span>:<span class="id" type="var">Heqa1'</span>.\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">fold\_constants\_aexp</span> <span class="id"
type="var">a2</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">a2'</span> <span class="id"
type="var">eqn</span>:<span class="id" type="var">Heqa2'</span>.\
     <span class="id" type="tactic">replace</span> (<span class="id"
type="var">aeval</span> <span class="id" type="var">st</span> <span
class="id" type="var">a1</span>) <span class="id"
type="keyword">with</span> (<span class="id" type="var">aeval</span>
<span class="id" type="var">st</span> <span class="id"
type="var">a1'</span>) <span class="id" type="tactic">by</span>\
        (<span class="id" type="tactic">subst</span> <span class="id"
type="var">a1'</span>; <span class="id" type="tactic">rewrite</span>
<span style="font-family: arial;">←</span> <span class="id"
type="var">fold\_constants\_aexp\_sound</span>; <span class="id"
type="tactic">reflexivity</span>).\
     <span class="id" type="tactic">replace</span> (<span class="id"
type="var">aeval</span> <span class="id" type="var">st</span> <span
class="id" type="var">a2</span>) <span class="id"
type="keyword">with</span> (<span class="id" type="var">aeval</span>
<span class="id" type="var">st</span> <span class="id"
type="var">a2'</span>) <span class="id" type="tactic">by</span>\
        (<span class="id" type="tactic">subst</span> <span class="id"
type="var">a2'</span>; <span class="id" type="tactic">rewrite</span>
<span style="font-family: arial;">←</span> <span class="id"
type="var">fold\_constants\_aexp\_sound</span>; <span class="id"
type="tactic">reflexivity</span>).\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">a1'</span>; <span class="id" type="tactic">destruct</span>
<span class="id" type="var">a2'</span>; <span class="id"
type="tactic">try</span> <span class="id"
type="tactic">reflexivity</span>.\
       <span
class="comment">(\* The only interesting case is when both a1 and a2 \
          become constants after folding \*)</span>\
       <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">destruct</span> (<span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n</span> <span
class="id" type="var">n0</span>); <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "BLe".\
     <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
   <span class="id" type="var">Case</span> "BNot".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="var">remember</span> (<span class="id"
type="var">fold\_constants\_bexp</span> <span class="id"
type="var">b</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">b'</span> <span class="id"
type="var">eqn</span>:<span class="id" type="var">Heqb'</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHb</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">b'</span>; <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "BAnd".\
     <span class="id" type="tactic">simpl</span>.\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">fold\_constants\_bexp</span> <span class="id"
type="var">b1</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">b1'</span> <span class="id"
type="var">eqn</span>:<span class="id" type="var">Heqb1'</span>.\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">fold\_constants\_bexp</span> <span class="id"
type="var">b2</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">b2'</span> <span class="id"
type="var">eqn</span>:<span class="id" type="var">Heqb2'</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHb1</span>. <span class="id" type="tactic">rewrite</span>
<span class="id" type="var">IHb2</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">b1'</span>; <span class="id" type="tactic">destruct</span>
<span class="id" type="var">b2'</span>; <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (fold\_constants\_com\_sound) {.section}

Complete the <span class="inlinecode"><span class="id"
type="var">WHILE</span></span> case of the following proof.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">fold\_constants\_com\_sound</span> :\
   <span class="id" type="var">ctrans\_sound</span> <span class="id"
type="var">fold\_constants\_com</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">ctrans\_sound</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">c</span>.\
   <span class="id" type="var">com\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">c</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">simpl</span>.\
   <span class="id" type="var">Case</span> "SKIP". <span class="id"
type="tactic">apply</span> <span class="id"
type="var">refl\_cequiv</span>.\
   <span class="id" type="var">Case</span> "::=". <span class="id"
type="tactic">apply</span> <span class="id"
type="var">CAss\_congruence</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">fold\_constants\_aexp\_sound</span>.\
   <span class="id" type="var">Case</span> ";;". <span class="id"
type="tactic">apply</span> <span class="id"
type="var">CSeq\_congruence</span>; <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "IFB".\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">bequiv</span> <span class="id" type="var">b</span> (<span
class="id" type="var">fold\_constants\_bexp</span> <span class="id"
type="var">b</span>)).\
       <span class="id" type="var">SCase</span> "Pf of assertion". <span
class="id" type="tactic">apply</span> <span class="id"
type="var">fold\_constants\_bexp\_sound</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">fold\_constants\_bexp</span> <span class="id"
type="var">b</span>) <span class="id" type="var">eqn</span>:<span
class="id" type="var">Heqb</span>;\
       <span
class="comment">(\* If the optimization doesn't eliminate the if, then the result\

         is easy to prove from the IH and fold\_constants\_bexp\_sound \*)</span>\
       <span class="id" type="tactic">try</span> (<span class="id"
type="tactic">apply</span> <span class="id"
type="var">CIf\_congruence</span>; <span class="id"
type="tactic">assumption</span>).\
     <span class="id" type="var">SCase</span> "b always true".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">trans\_cequiv</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">c1</span>; <span
class="id" type="tactic">try</span> <span class="id"
type="tactic">assumption</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IFB\_true</span>; <span class="id"
type="tactic">assumption</span>.\
     <span class="id" type="var">SCase</span> "b always false".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">trans\_cequiv</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">c2</span>; <span
class="id" type="tactic">try</span> <span class="id"
type="tactic">assumption</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IFB\_false</span>; <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "WHILE".\
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

### Soundness of (0 + n) Elimination, Redux {.section}

<div class="paragraph">

</div>

#### Exercise: 4 stars, advanced, optional (optimize\_0plus) {.section}

Recall the definition <span class="inlinecode"><span class="id"
type="var">optimize\_0plus</span></span> from Imp.v:
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">optimize\_0plus</span> (<span class="id"
type="var">e</span>:<span class="id" type="var">aexp</span>) : <span
class="id" type="var">aexp</span> := \
       <span class="id" type="keyword">match</span> <span class="id"
type="var">e</span> <span class="id" type="keyword">with</span>\
       | <span class="id" type="var">ANum</span> <span class="id"
type="var">n</span> ⇒ \
           <span class="id" type="var">ANum</span> <span class="id"
type="var">n</span>\
       | <span class="id" type="var">APlus</span> (<span class="id"
type="var">ANum</span> 0) <span class="id" type="var">e2</span> ⇒ \
           <span class="id" type="var">optimize\_0plus</span> <span
class="id" type="var">e2</span>\
       | <span class="id" type="var">APlus</span> <span class="id"
type="var">e1</span> <span class="id" type="var">e2</span> ⇒ \
           <span class="id" type="var">APlus</span> (<span class="id"
type="var">optimize\_0plus</span> <span class="id"
type="var">e1</span>) (<span class="id"
type="var">optimize\_0plus</span> <span class="id"
type="var">e2</span>)\
       | <span class="id" type="var">AMinus</span> <span class="id"
type="var">e1</span> <span class="id" type="var">e2</span> ⇒ \
           <span class="id" type="var">AMinus</span> (<span class="id"
type="var">optimize\_0plus</span> <span class="id"
type="var">e1</span>) (<span class="id"
type="var">optimize\_0plus</span> <span class="id"
type="var">e2</span>)\
       | <span class="id" type="var">AMult</span> <span class="id"
type="var">e1</span> <span class="id" type="var">e2</span> ⇒ \
           <span class="id" type="var">AMult</span> (<span class="id"
type="var">optimize\_0plus</span> <span class="id"
type="var">e1</span>) (<span class="id"
type="var">optimize\_0plus</span> <span class="id"
type="var">e2</span>)\
       <span class="id" type="keyword">end</span>.
<div class="paragraph">

</div>

</div>

Note that this function is defined over the old <span
class="inlinecode"><span class="id" type="var">aexp</span></span>s,
without states.
<div class="paragraph">

</div>

Write a new version of this function that accounts for variables, and
analogous ones for <span class="inlinecode"><span class="id"
type="var">bexp</span></span>s and commands:
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">optimize\_0plus\_aexp</span>\
      <span class="id" type="var">optimize\_0plus\_bexp</span>\
      <span class="id" type="var">optimize\_0plus\_com</span>
<div class="paragraph">

</div>

</div>

Prove that these three functions are sound, as we did for <span
class="inlinecode"><span class="id"
type="var">fold\_constants\_</span>×</span>. (Make sure you use the
congruence lemmas in the proof of <span class="inlinecode"><span
class="id" type="var">optimize\_0plus\_com</span></span> — otherwise it
will be *long*!)
<div class="paragraph">

</div>

Then define an optimizer on commands that first folds constants (using
<span class="inlinecode"><span class="id"
type="var">fold\_constants\_com</span></span>) and then eliminates <span
class="inlinecode">0</span> <span class="inlinecode">+</span> <span
class="inlinecode"><span class="id" type="var">n</span></span> terms
(using <span class="inlinecode"><span class="id"
type="var">optimize\_0plus\_com</span></span>).
<div class="paragraph">

</div>

-   Give a meaningful example of this optimizer's output.
    <div class="paragraph">

    </div>

-   Prove that the optimizer is sound. (This part should be *very*
    easy.)

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

Proving That Programs Are *Not* Equivalent {.section}
==========================================

<div class="paragraph">

</div>

Suppose that <span class="inlinecode"><span class="id"
type="var">c1</span></span> is a command of the form <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">::=</span> <span class="inlinecode"><span class="id"
type="var">a1</span>;;</span> <span class="inlinecode"><span class="id"
type="var">Y</span></span> <span class="inlinecode">::=</span> <span
class="inlinecode"><span class="id" type="var">a2</span></span> and
<span class="inlinecode"><span class="id" type="var">c2</span></span> is
the command <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode">::=</span> <span
class="inlinecode"><span class="id" type="var">a1</span>;;</span> <span
class="inlinecode"><span class="id" type="var">Y</span></span> <span
class="inlinecode">::=</span> <span class="inlinecode"><span class="id"
type="var">a2'</span></span>, where <span class="inlinecode"><span
class="id" type="var">a2'</span></span> is formed by substituting <span
class="inlinecode"><span class="id" type="var">a1</span></span> for all
occurrences of <span class="inlinecode"><span class="id"
type="var">X</span></span> in <span class="inlinecode"><span class="id"
type="var">a2</span></span>. For example, <span class="inlinecode"><span
class="id" type="var">c1</span></span> and <span
class="inlinecode"><span class="id" type="var">c2</span></span> might
be:
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="var">c1</span>  =  (<span class="id"
type="var">X</span> ::= 42 + 53;; \
                <span class="id" type="var">Y</span> ::= <span
class="id" type="var">Y</span> + <span class="id" type="var">X</span>)\
        <span class="id" type="var">c2</span>  =  (<span class="id"
type="var">X</span> ::= 42 + 53;; \
                <span class="id" type="var">Y</span> ::= <span
class="id" type="var">Y</span> + (42 + 53))
<div class="paragraph">

</div>

</div>

Clearly, this *particular* <span class="inlinecode"><span class="id"
type="var">c1</span></span> and <span class="inlinecode"><span
class="id" type="var">c2</span></span> are equivalent. Is this true in
general?
<div class="paragraph">

</div>

We will see in a moment that it is not, but it is worthwhile to pause,
now, and see if you can find a counter-example on your own.
<div class="paragraph">

</div>

Here, formally, is the function that substitutes an arithmetic
expression for each occurrence of a given variable in another
expression:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">subst\_aexp</span> (<span class="id" type="var">i</span> :
<span class="id" type="var">id</span>) (<span class="id"
type="var">u</span> : <span class="id" type="var">aexp</span>) (<span
class="id" type="var">a</span> : <span class="id"
type="var">aexp</span>) : <span class="id" type="var">aexp</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">a</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">ANum</span> <span class="id"
type="var">n</span> ⇒ <span class="id" type="var">ANum</span> <span
class="id" type="var">n</span>\
   | <span class="id" type="var">AId</span> <span class="id"
type="var">i'</span> ⇒ <span class="id" type="keyword">if</span> <span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">i</span> <span class="id" type="var">i'</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">u</span> <span class="id" type="keyword">else</span> <span
class="id" type="var">AId</span> <span class="id" type="var">i'</span>\
   | <span class="id" type="var">APlus</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ <span
class="id" type="var">APlus</span> (<span class="id"
type="var">subst\_aexp</span> <span class="id" type="var">i</span> <span
class="id" type="var">u</span> <span class="id" type="var">a1</span>)
(<span class="id" type="var">subst\_aexp</span> <span class="id"
type="var">i</span> <span class="id" type="var">u</span> <span
class="id" type="var">a2</span>)\
   | <span class="id" type="var">AMinus</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ <span
class="id" type="var">AMinus</span> (<span class="id"
type="var">subst\_aexp</span> <span class="id" type="var">i</span> <span
class="id" type="var">u</span> <span class="id" type="var">a1</span>)
(<span class="id" type="var">subst\_aexp</span> <span class="id"
type="var">i</span> <span class="id" type="var">u</span> <span
class="id" type="var">a2</span>)\
   | <span class="id" type="var">AMult</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ <span
class="id" type="var">AMult</span> (<span class="id"
type="var">subst\_aexp</span> <span class="id" type="var">i</span> <span
class="id" type="var">u</span> <span class="id" type="var">a1</span>)
(<span class="id" type="var">subst\_aexp</span> <span class="id"
type="var">i</span> <span class="id" type="var">u</span> <span
class="id" type="var">a2</span>)\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">subst\_aexp\_ex</span> :\
   <span class="id" type="var">subst\_aexp</span> <span class="id"
type="var">X</span> (<span class="id" type="var">APlus</span> (<span
class="id" type="var">ANum</span> 42) (<span class="id"
type="var">ANum</span> 53)) (<span class="id" type="var">APlus</span>
(<span class="id" type="var">AId</span> <span class="id"
type="var">Y</span>) (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>)) =\
   (<span class="id" type="var">APlus</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">Y</span>) (<span
class="id" type="var">APlus</span> (<span class="id"
type="var">ANum</span> 42) (<span class="id" type="var">ANum</span>
53))).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

And here is the property we are interested in, expressing the claim that
commands <span class="inlinecode"><span class="id"
type="var">c1</span></span> and <span class="inlinecode"><span
class="id" type="var">c2</span></span> as described above are always
equivalent.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">subst\_equiv\_property</span> := <span
style="font-family: arial;">∀</span><span class="id"
type="var">i1</span> <span class="id" type="var">i2</span> <span
class="id" type="var">a1</span> <span class="id" type="var">a2</span>,\
   <span class="id" type="var">cequiv</span> (<span class="id"
type="var">i1</span> ::= <span class="id" type="var">a1</span>;; <span
class="id" type="var">i2</span> ::= <span class="id"
type="var">a2</span>)\
          (<span class="id" type="var">i1</span> ::= <span class="id"
type="var">a1</span>;; <span class="id" type="var">i2</span> ::= <span
class="id" type="var">subst\_aexp</span> <span class="id"
type="var">i1</span> <span class="id" type="var">a1</span> <span
class="id" type="var">a2</span>).\
\

</div>

<div class="doc">

###  {.section}

Sadly, the property does *not* always hold.
<div class="paragraph">

</div>

*Theorem*: It is not the case that, for all <span
class="inlinecode"><span class="id" type="var">i1</span></span>, <span
class="inlinecode"><span class="id" type="var">i2</span></span>, <span
class="inlinecode"><span class="id" type="var">a1</span></span>, and
<span class="inlinecode"><span class="id" type="var">a2</span></span>,
<div class="paragraph">

</div>

<div class="code code-tight">

         <span class="id" type="var">cequiv</span> (<span class="id"
type="var">i1</span> ::= <span class="id" type="var">a1</span>;; <span
class="id" type="var">i2</span> ::= <span class="id"
type="var">a2</span>)\
                 (<span class="id" type="var">i1</span> ::= <span
class="id" type="var">a1</span>;; <span class="id"
type="var">i2</span> ::= <span class="id"
type="var">subst\_aexp</span> <span class="id"
type="var">i1</span> <span class="id" type="var">a1</span> <span
class="id" type="var">a2</span>).
<div class="paragraph">

</div>

</div>

*Proof*: Suppose, for a contradiction, that for all <span
class="inlinecode"><span class="id" type="var">i1</span></span>, <span
class="inlinecode"><span class="id" type="var">i2</span></span>, <span
class="inlinecode"><span class="id" type="var">a1</span></span>, and
<span class="inlinecode"><span class="id" type="var">a2</span></span>,
we have
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">cequiv</span> (<span class="id"
type="var">i1</span> ::= <span class="id" type="var">a1</span>;; <span
class="id" type="var">i2</span> ::= <span class="id"
type="var">a2</span>) \
              (<span class="id" type="var">i1</span> ::= <span
class="id" type="var">a1</span>;; <span class="id"
type="var">i2</span> ::= <span class="id"
type="var">subst\_aexp</span> <span class="id"
type="var">i1</span> <span class="id" type="var">a1</span> <span
class="id" type="var">a2</span>).
<div class="paragraph">

</div>

</div>

Consider the following program:
<div class="paragraph">

</div>

<div class="code code-tight">

         <span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id"
type="var">ANum</span> 1);; <span class="id"
type="var">Y</span> ::= <span class="id" type="var">AId</span> <span
class="id" type="var">X</span>
<div class="paragraph">

</div>

</div>

Note that
<div class="paragraph">

</div>

<div class="code code-tight">

         (<span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id"
type="var">ANum</span> 1);; <span class="id"
type="var">Y</span> ::= <span class="id" type="var">AId</span> <span
class="id" type="var">X</span>)\
          / <span class="id" type="var">empty\_state</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st1</span>,
<div class="paragraph">

</div>

</div>

where <span class="inlinecode"><span class="id"
type="var">st1</span></span> <span class="inlinecode">=</span> <span
class="inlinecode">{</span> <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode"><span
style="font-family: arial;">↦</span></span> <span
class="inlinecode">1,</span> <span class="inlinecode"><span class="id"
type="var">Y</span></span> <span class="inlinecode"><span
style="font-family: arial;">↦</span></span> <span
class="inlinecode">1</span> <span class="inlinecode">}</span>.
<div class="paragraph">

</div>

By our assumption, we know that
<div class="paragraph">

</div>

<div class="code code-tight">

        <span class="id" type="var">cequiv</span> (<span class="id"
type="var">X</span> ::= <span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">ANum</span> 1);; <span
class="id" type="var">Y</span> ::= <span class="id"
type="var">AId</span> <span class="id" type="var">X</span>)\
                (<span class="id" type="var">X</span> ::= <span
class="id" type="var">APlus</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">ANum</span> 1);; <span class="id"
type="var">Y</span> ::= <span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">ANum</span> 1))
<div class="paragraph">

</div>

</div>

so, by the definition of <span class="inlinecode"><span class="id"
type="var">cequiv</span></span>, we have
<div class="paragraph">

</div>

<div class="code code-tight">

        (<span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id"
type="var">ANum</span> 1);; <span class="id"
type="var">Y</span> ::= <span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">ANum</span> 1))\
         / <span class="id" type="var">empty\_state</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st1</span>.
<div class="paragraph">

</div>

</div>

But we can also derive
<div class="paragraph">

</div>

<div class="code code-tight">

        (<span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id"
type="var">ANum</span> 1);; <span class="id"
type="var">Y</span> ::= <span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">ANum</span> 1))\
         / <span class="id" type="var">empty\_state</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st2</span>,
<div class="paragraph">

</div>

</div>

where <span class="inlinecode"><span class="id"
type="var">st2</span></span> <span class="inlinecode">=</span> <span
class="inlinecode">{</span> <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode"><span
style="font-family: arial;">↦</span></span> <span
class="inlinecode">1,</span> <span class="inlinecode"><span class="id"
type="var">Y</span></span> <span class="inlinecode"><span
style="font-family: arial;">↦</span></span> <span
class="inlinecode">2</span> <span class="inlinecode">}</span>. Note that
<span class="inlinecode"><span class="id" type="var">st1</span></span>
<span class="inlinecode">≠</span> <span class="inlinecode"><span
class="id" type="var">st2</span></span>; this is a contradiction, since
<span class="inlinecode"><span class="id" type="var">ceval</span></span>
is deterministic! ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">subst\_inequiv</span> :\
   ¬ <span class="id" type="var">subst\_equiv\_property</span>.\
<div id="proofcontrol18" class="togglescript"
onclick="toggleDisplay('proof18');toggleDisplay('proofcontrol18')">

<span class="show"></span>

</div>

<div id="proof18" class="proofscript"
onclick="toggleDisplay('proof18');toggleDisplay('proofcontrol18')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">subst\_equiv\_property</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">Contra</span>.\
\
   <span
class="comment">(\* Here is the counterexample: assuming that <span
class="inlinecode"><span class="id"
type="var">subst\_equiv\_property</span></span>\
      holds allows us to prove that these two programs are\
      equivalent... \*)</span>\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">X</span> ::= <span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 1);;\
             <span class="id" type="var">Y</span> ::= <span class="id"
type="var">AId</span> <span class="id" type="var">X</span>)\
       <span class="id" type="keyword">as</span> <span class="id"
type="var">c1</span>.\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">X</span> ::= <span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 1);;\
             <span class="id" type="var">Y</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1))\
       <span class="id" type="keyword">as</span> <span class="id"
type="var">c2</span>.\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">cequiv</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c2</span>) <span class="id"
type="tactic">by</span> (<span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">apply</span> <span class="id"
type="var">Contra</span>).\
\
   <span
class="comment">(\* ... allows us to show that the command <span
class="inlinecode"><span class="id"
type="var">c2</span></span> can terminate \
      in two different final states: \
         st1 = {X |-\> 1, Y |-\> 1} \
         st2 = {X |-\> 1, Y |-\> 2}. \*)</span>\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">update</span> (<span class="id" type="var">update</span>
<span class="id" type="var">empty\_state</span> <span class="id"
type="var">X</span> 1) <span class="id" type="var">Y</span> 1) <span
class="id" type="keyword">as</span> <span class="id"
type="var">st1</span>.\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">update</span> (<span class="id" type="var">update</span>
<span class="id" type="var">empty\_state</span> <span class="id"
type="var">X</span> 1) <span class="id" type="var">Y</span> 2) <span
class="id" type="keyword">as</span> <span class="id"
type="var">st2</span>.\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">H1</span>: <span class="id" type="var">c1</span> / <span
class="id" type="var">empty\_state</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st1</span>);\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">H2</span>: <span class="id" type="var">c2</span> / <span
class="id" type="var">empty\_state</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st2</span>);\
   <span class="id" type="tactic">try</span> (<span class="id"
type="tactic">subst</span>;\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Seq</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">st'</span> := (<span class="id"
type="var">update</span> <span class="id" type="var">empty\_state</span>
<span class="id" type="var">X</span> 1));\
        <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Ass</span>; <span class="id"
type="tactic">reflexivity</span>).\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H1</span>.\
\
   <span
class="comment">(\* Finally, we use the fact that evaluation is deterministic\
      to obtain a contradiction. \*)</span>\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">Hcontra</span>: <span class="id" type="var">st1</span> =
<span class="id" type="var">st2</span>)\
     <span class="id" type="tactic">by</span> (<span class="id"
type="tactic">apply</span> (<span class="id"
type="var">ceval\_deterministic</span> <span class="id"
type="var">c2</span> <span class="id" type="var">empty\_state</span>);
<span class="id" type="tactic">assumption</span>).\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">Hcontra'</span>: <span class="id" type="var">st1</span> <span
class="id" type="var">Y</span> = <span class="id" type="var">st2</span>
<span class="id" type="var">Y</span>)\
     <span class="id" type="tactic">by</span> (<span class="id"
type="tactic">rewrite</span> <span class="id" type="var">Hcontra</span>;
<span class="id" type="tactic">reflexivity</span>).\
   <span class="id" type="tactic">subst</span>. <span class="id"
type="tactic">inversion</span> <span class="id"
type="var">Hcontra'</span>. <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 4 stars, optional (better\_subst\_equiv) {.section}

The equivalence we had in mind above was not complete nonsense — it was
actually almost right. To make it correct, we just need to exclude the
case where the variable <span class="inlinecode"><span class="id"
type="var">X</span></span> occurs in the right-hand-side of the first
assignment statement.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">var\_not\_used\_in\_aexp</span> (<span class="id"
type="var">X</span>:<span class="id" type="var">id</span>) : <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">VNUNum</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id"
type="var">var\_not\_used\_in\_aexp</span> <span class="id"
type="var">X</span> (<span class="id" type="var">ANum</span> <span
class="id" type="var">n</span>)\
   | <span class="id" type="var">VNUId</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">Y</span>, <span class="id" type="var">X</span> ≠ <span
class="id" type="var">Y</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">var\_not\_used\_in\_aexp</span> <span class="id"
type="var">X</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">Y</span>)\
   | <span class="id" type="var">VNUPlus</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>,\
       <span class="id" type="var">var\_not\_used\_in\_aexp</span> <span
class="id" type="var">X</span> <span class="id" type="var">a1</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">var\_not\_used\_in\_aexp</span> <span
class="id" type="var">X</span> <span class="id" type="var">a2</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">var\_not\_used\_in\_aexp</span> <span
class="id" type="var">X</span> (<span class="id" type="var">APlus</span>
<span class="id" type="var">a1</span> <span class="id"
type="var">a2</span>)\
   | <span class="id" type="var">VNUMinus</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>,\
       <span class="id" type="var">var\_not\_used\_in\_aexp</span> <span
class="id" type="var">X</span> <span class="id" type="var">a1</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">var\_not\_used\_in\_aexp</span> <span
class="id" type="var">X</span> <span class="id" type="var">a2</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">var\_not\_used\_in\_aexp</span> <span
class="id" type="var">X</span> (<span class="id"
type="var">AMinus</span> <span class="id" type="var">a1</span> <span
class="id" type="var">a2</span>)\
   | <span class="id" type="var">VNUMult</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>,\
       <span class="id" type="var">var\_not\_used\_in\_aexp</span> <span
class="id" type="var">X</span> <span class="id" type="var">a1</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">var\_not\_used\_in\_aexp</span> <span
class="id" type="var">X</span> <span class="id" type="var">a2</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">var\_not\_used\_in\_aexp</span> <span
class="id" type="var">X</span> (<span class="id" type="var">AMult</span>
<span class="id" type="var">a1</span> <span class="id"
type="var">a2</span>).\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">aeval\_weakening</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">i</span>
<span class="id" type="var">st</span> <span class="id"
type="var">a</span> <span class="id" type="var">ni</span>,\
   <span class="id" type="var">var\_not\_used\_in\_aexp</span> <span
class="id" type="var">i</span> <span class="id" type="var">a</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">aeval</span> (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">i</span> <span class="id" type="var">ni</span>)
<span class="id" type="var">a</span> = <span class="id"
type="var">aeval</span> <span class="id" type="var">st</span> <span
class="id" type="var">a</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Using <span class="inlinecode"><span class="id"
type="var">var\_not\_used\_in\_aexp</span></span>, formalize and prove a
correct verson of <span class="inlinecode"><span class="id"
type="var">subst\_equiv\_property</span></span>.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (inequiv\_exercise) {.section}

Prove that an infinite loop is not equivalent to <span
class="inlinecode"><span class="id" type="var">SKIP</span></span>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">inequiv\_exercise</span>:\
   ¬ <span class="id" type="var">cequiv</span> (<span class="id"
type="var">WHILE</span> <span class="id" type="var">BTrue</span> <span
class="id" type="var">DO</span> <span class="id" type="var">SKIP</span>
<span class="id" type="var">END</span>) <span class="id"
type="var">SKIP</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Extended exercise: Non-deterministic Imp {.section}
========================================

<div class="paragraph">

</div>

As we have seen (in theorem <span class="inlinecode"><span class="id"
type="var">ceval\_deterministic</span></span> in the Imp chapter), Imp's
evaluation relation is deterministic. However, *non*-determinism is an
important part of the definition of many real programming languages. For
example, in many imperative languages (such as C and its relatives), the
order in which function arguments are evaluated is unspecified. The
program fragment
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">x</span> = 0;;\
       <span class="id" type="var">f</span>(++<span class="id"
type="var">x</span>, <span class="id" type="var">x</span>)
<div class="paragraph">

</div>

</div>

might call <span class="inlinecode"><span class="id"
type="var">f</span></span> with arguments <span
class="inlinecode">(1,</span> <span class="inlinecode">0)</span> or
<span class="inlinecode">(1,</span> <span class="inlinecode">1)</span>,
depending how the compiler chooses to order things. This can be a little
confusing for programmers, but it gives the compiler writer useful
freedom.
<div class="paragraph">

</div>

In this exercise, we will extend Imp with a simple non-deterministic
command and study how this change affects program equivalence. The new
command has the syntax <span class="inlinecode"><span class="id"
type="var">HAVOC</span></span> <span class="inlinecode"><span class="id"
type="var">X</span></span>, where <span class="inlinecode"><span
class="id" type="var">X</span></span> is an identifier. The effect of
executing <span class="inlinecode"><span class="id"
type="var">HAVOC</span></span> <span class="inlinecode"><span class="id"
type="var">X</span></span> is to assign an *arbitrary* number to the
variable <span class="inlinecode"><span class="id"
type="var">X</span></span>, non-deterministically. For example, after
executing the program:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">HAVOC</span> <span class="id"
type="var">Y</span>;;\
       <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Y</span> × 2
<div class="paragraph">

</div>

</div>

the value of <span class="inlinecode"><span class="id"
type="var">Y</span></span> can be any number, while the value of <span
class="inlinecode"><span class="id" type="var">Z</span></span> is twice
that of <span class="inlinecode"><span class="id"
type="var">Y</span></span> (so <span class="inlinecode"><span class="id"
type="var">Z</span></span> is always even). Note that we are not saying
anything about the *probabilities* of the outcomes — just that there are
(infinitely) many different outcomes that can possibly happen after
executing this non-deterministic code.
<div class="paragraph">

</div>

In a sense a variable on which we do <span class="inlinecode"><span
class="id" type="var">HAVOC</span></span> roughly corresponds to an
unitialized variable in the C programming language. After the <span
class="inlinecode"><span class="id" type="var">HAVOC</span></span> the
variable holds a fixed but arbitrary number. Most sources of
nondeterminism in language definitions are there precisely because
programmers don't care which choice is made (and so it is good to leave
it open to the compiler to choose whichever will run faster).
<div class="paragraph">

</div>

We call this new language *Himp* (\`\`Imp extended with <span
class="inlinecode"><span class="id" type="var">HAVOC</span></span>'').

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Himp</span>.\
\

</div>

<div class="doc">

To formalize the language, we first add a clause to the definition of
commands.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">com</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">CSkip</span> : <span class="id"
type="var">com</span>\
   | <span class="id" type="var">CAss</span> : <span class="id"
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
   | <span class="id" type="var">CHavoc</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">com</span>. <span
class="comment">(\* \<---- new \*)</span>\
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
type="var">c</span> ";;"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "IFB" | <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">c</span> "WHILE" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "HAVOC"
].\
\
 <span class="id" type="keyword">Notation</span> "'SKIP'" :=\
   <span class="id" type="var">CSkip</span>.\
 <span class="id" type="keyword">Notation</span> "X '::=' a" :=\
   (<span class="id" type="var">CAss</span> <span class="id"
type="var">X</span> <span class="id" type="var">a</span>) (<span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 60).\
 <span class="id" type="keyword">Notation</span> "c1 ;; c2" :=\
   (<span class="id" type="var">CSeq</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c2</span>) (<span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 80, <span class="id" type="var">right</span>
<span class="id" type="var">associativity</span>).\
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
 <span class="id" type="keyword">Notation</span> "'HAVOC' l" := (<span
class="id" type="var">CHavoc</span> <span class="id"
type="var">l</span>) (<span class="id" type="tactic">at</span> <span
class="id" type="var">level</span> 60).\
\

</div>

<div class="doc">

#### Exercise: 2 stars (himp\_ceval) {.section}

Now, we must extend the operational semantics. We have provided a
template for the <span class="inlinecode"><span class="id"
type="var">ceval</span></span> relation below, specifying the big-step
semantics. What rule(s) must be added to the definition of <span
class="inlinecode"><span class="id" type="var">ceval</span></span> to
formalize the behavior of the <span class="inlinecode"><span class="id"
type="var">HAVOC</span></span> command?

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> "c1 '/' st
'<span style="font-family: arial;">⇓</span>' st'" (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40,
<span class="id" type="var">st</span> <span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 39).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ceval</span> : <span class="id" type="var">com</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">state</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">state</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">E\_Skip</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> : <span class="id" type="var">state</span>, <span
class="id" type="var">SKIP</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st</span>\
   | <span class="id" type="var">E\_Ass</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st</span> : <span class="id" type="var">state</span>) (<span
class="id" type="var">a1</span> : <span class="id"
type="var">aexp</span>) (<span class="id" type="var">n</span> : <span
class="id" type="var">nat</span>) (<span class="id" type="var">X</span>
: <span class="id" type="var">id</span>),\
             <span class="id" type="var">aeval</span> <span class="id"
type="var">st</span> <span class="id" type="var">a1</span> = <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> (<span class="id"
type="var">X</span> ::= <span class="id" type="var">a1</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">X</span> <span class="id" type="var">n</span>\
   | <span class="id" type="var">E\_Seq</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">c1</span> <span class="id" type="var">c2</span> : <span
class="id" type="var">com</span>) (<span class="id" type="var">st</span>
<span class="id" type="var">st'</span> <span class="id"
type="var">st''</span> : <span class="id" type="var">state</span>),\
             <span class="id" type="var">c1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">c2</span> / <span class="id" type="var">st'</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st''</span> <span style="font-family: arial;">→</span> (<span
class="id" type="var">c1</span> ;; <span class="id"
type="var">c2</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st''</span>\
   | <span class="id" type="var">E\_IfTrue</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st</span> <span class="id" type="var">st'</span> : <span
class="id" type="var">state</span>) (<span class="id"
type="var">b1</span> : <span class="id" type="var">bexp</span>) (<span
class="id" type="var">c1</span> <span class="id" type="var">c2</span> :
<span class="id" type="var">com</span>),\
                <span class="id" type="var">beval</span> <span
class="id" type="var">st</span> <span class="id" type="var">b1</span> =
<span class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
                <span class="id" type="var">c1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span> (<span class="id"
type="var">IFB</span> <span class="id" type="var">b1</span> <span
class="id" type="var">THEN</span> <span class="id" type="var">c1</span>
<span class="id" type="var">ELSE</span> <span class="id"
type="var">c2</span> <span class="id" type="var">FI</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span>\
   | <span class="id" type="var">E\_IfFalse</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st</span> <span class="id" type="var">st'</span> : <span
class="id" type="var">state</span>) (<span class="id"
type="var">b1</span> : <span class="id" type="var">bexp</span>) (<span
class="id" type="var">c1</span> <span class="id" type="var">c2</span> :
<span class="id" type="var">com</span>),\
                 <span class="id" type="var">beval</span> <span
class="id" type="var">st</span> <span class="id" type="var">b1</span> =
<span class="id" type="var">false</span> <span
style="font-family: arial;">→</span>\
                 <span class="id" type="var">c2</span> / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span> (<span
class="id" type="var">IFB</span> <span class="id" type="var">b1</span>
<span class="id" type="var">THEN</span> <span class="id"
type="var">c1</span> <span class="id" type="var">ELSE</span> <span
class="id" type="var">c2</span> <span class="id" type="var">FI</span>) /
<span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span>\
   | <span class="id" type="var">E\_WhileEnd</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">b1</span> : <span class="id" type="var">bexp</span>) (<span
class="id" type="var">st</span> : <span class="id"
type="var">state</span>) (<span class="id" type="var">c1</span> : <span
class="id" type="var">com</span>),\
                  <span class="id" type="var">beval</span> <span
class="id" type="var">st</span> <span class="id" type="var">b1</span> =
<span class="id" type="var">false</span> <span
style="font-family: arial;">→</span> (<span class="id"
type="var">WHILE</span> <span class="id" type="var">b1</span> <span
class="id" type="var">DO</span> <span class="id" type="var">c1</span>
<span class="id" type="var">END</span>) / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st</span>\
   | <span class="id" type="var">E\_WhileLoop</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">st''</span> : <span class="id"
type="var">state</span>) (<span class="id" type="var">b1</span> : <span
class="id" type="var">bexp</span>) (<span class="id"
type="var">c1</span> : <span class="id" type="var">com</span>),\
                   <span class="id" type="var">beval</span> <span
class="id" type="var">st</span> <span class="id" type="var">b1</span> =
<span class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
                   <span class="id" type="var">c1</span> / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
                   (<span class="id" type="var">WHILE</span> <span
class="id" type="var">b1</span> <span class="id" type="var">DO</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">END</span>) / <span class="id" type="var">st'</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st''</span> <span style="font-family: arial;">→</span>\
                   (<span class="id" type="var">WHILE</span> <span
class="id" type="var">b1</span> <span class="id" type="var">DO</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">END</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st''</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\
   <span class="id" type="keyword">where</span> "c1 '/' st '<span
style="font-family: arial;">⇓</span>' st'" := (<span class="id"
type="var">ceval</span> <span class="id" type="var">c1</span> <span
class="id" type="var">st</span> <span class="id"
type="var">st'</span>).\
\
 <span class="id" type="keyword">Tactic Notation</span> "ceval\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_Skip" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"E\_Ass" | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_Seq"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_IfTrue" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"E\_IfFalse"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_WhileEnd" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"E\_WhileLoop"\
 <span class="comment">(\* FILL IN HERE \*)</span>\
 ].\
\

</div>

<div class="doc">

As a sanity check, the following claims should be provable for your
definition:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">havoc\_example1</span> : (<span class="id"
type="var">HAVOC</span> <span class="id" type="var">X</span>) / <span
class="id" type="var">empty\_state</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">update</span> <span class="id" type="var">empty\_state</span>
<span class="id" type="var">X</span> 0.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">havoc\_example2</span> :\
   (<span class="id" type="var">SKIP</span>;; <span class="id"
type="var">HAVOC</span> <span class="id" type="var">Z</span>) / <span
class="id" type="var">empty\_state</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">update</span> <span class="id" type="var">empty\_state</span>
<span class="id" type="var">Z</span> 42.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Finally, we repeat the definition of command equivalence from above:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">cequiv</span> (<span class="id" type="var">c1</span> <span
class="id" type="var">c2</span> : <span class="id"
type="var">com</span>) : <span class="id" type="keyword">Prop</span> :=
<span style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span> : <span
class="id" type="var">state</span>,\
   <span class="id" type="var">c1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">c2</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span>.\
\

</div>

<div class="doc">

This definition still makes perfect sense in the case of always
terminating programs, so let's apply it to prove some non-deterministic
programs equivalent or non-equivalent.
<div class="paragraph">

</div>

#### Exercise: 3 stars (havoc\_swap) {.section}

Are the following two programs equivalent?

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">pXY</span> :=\
   <span class="id" type="var">HAVOC</span> <span class="id"
type="var">X</span>;; <span class="id" type="var">HAVOC</span> <span
class="id" type="var">Y</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">pYX</span> :=\
   <span class="id" type="var">HAVOC</span> <span class="id"
type="var">Y</span>;; <span class="id" type="var">HAVOC</span> <span
class="id" type="var">X</span>.\
\

</div>

<div class="doc">

If you think they are equivalent, prove it. If you think they are not,
prove that.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">pXY\_cequiv\_pYX</span> :\
   <span class="id" type="var">cequiv</span> <span class="id"
type="var">pXY</span> <span class="id" type="var">pYX</span> <span
style="font-family: arial;">∨</span> ¬<span class="id"
type="var">cequiv</span> <span class="id" type="var">pXY</span> <span
class="id" type="var">pYX</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, optional (havoc\_copy) {.section}

Are the following two programs equivalent?

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">ptwice</span> :=\
   <span class="id" type="var">HAVOC</span> <span class="id"
type="var">X</span>;; <span class="id" type="var">HAVOC</span> <span
class="id" type="var">Y</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">pcopy</span> :=\
   <span class="id" type="var">HAVOC</span> <span class="id"
type="var">X</span>;; <span class="id" type="var">Y</span> ::= <span
class="id" type="var">AId</span> <span class="id" type="var">X</span>.\
\

</div>

<div class="doc">

If you think they are equivalent, then prove it. If you think they are
not, then prove that. (Hint: You may find the <span
class="inlinecode"><span class="id" type="tactic">assert</span></span>
tactic useful.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ptwice\_cequiv\_pcopy</span> :\
   <span class="id" type="var">cequiv</span> <span class="id"
type="var">ptwice</span> <span class="id" type="var">pcopy</span> <span
style="font-family: arial;">∨</span> ¬<span class="id"
type="var">cequiv</span> <span class="id" type="var">ptwice</span> <span
class="id" type="var">pcopy</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

The definition of program equivalence we are using here has some subtle
consequences on programs that may loop forever. What <span
class="inlinecode"><span class="id" type="var">cequiv</span></span> says
is that the set of possible *terminating* outcomes of two equivalent
programs is the same. However, in a language with non-determinism, like
Himp, some programs always terminate, some programs always diverge, and
some programs can non-deterministically terminate in some runs and
diverge in others. The final part of the following exercise illustrates
this phenomenon.
<div class="paragraph">

</div>

#### Exercise: 5 stars, advanced (p1\_p2\_equiv) {.section}

Prove that p1 and p2 are equivalent. In this and the following
exercises, try to understand why the <span class="inlinecode"><span
class="id" type="var">cequiv</span></span> definition has the behavior
it has on these examples.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">p1</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">WHILE</span> (<span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 0))) <span class="id"
type="var">DO</span>\
     <span class="id" type="var">HAVOC</span> <span class="id"
type="var">Y</span>;;\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1)\
   <span class="id" type="var">END</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">p2</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">WHILE</span> (<span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 0))) <span class="id"
type="var">DO</span>\
     <span class="id" type="var">SKIP</span>\
   <span class="id" type="var">END</span>.\
\

</div>

<div class="doc">

Intuitively, the programs have the same termination behavior: either
they loop forever, or they terminate in the same state they started in.
We can capture the termination behavior of p1 and p2 individually with
these lemmas:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">p1\_may\_diverge</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span>, <span
class="id" type="var">st</span> <span class="id" type="var">X</span> ≠ 0
<span style="font-family: arial;">→</span>\
   ¬ <span class="id" type="var">p1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">p2\_may\_diverge</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span>, <span
class="id" type="var">st</span> <span class="id" type="var">X</span> ≠ 0
<span style="font-family: arial;">→</span>\
   ¬ <span class="id" type="var">p2</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span>.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

You should use these lemmas to prove that p1 and p2 are actually
equivalent.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">p1\_p2\_equiv</span> : <span class="id"
type="var">cequiv</span> <span class="id" type="var">p1</span> <span
class="id" type="var">p2</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, advanced (p3\_p4\_inquiv) {.section}

<div class="paragraph">

</div>

Prove that the following programs are *not* equivalent.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">p3</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">Z</span> ::= <span class="id"
type="var">ANum</span> 1;;\
   <span class="id" type="var">WHILE</span> (<span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 0))) <span class="id"
type="var">DO</span>\
     <span class="id" type="var">HAVOC</span> <span class="id"
type="var">X</span>;;\
     <span class="id" type="var">HAVOC</span> <span class="id"
type="var">Z</span>\
   <span class="id" type="var">END</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">p4</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">X</span> ::= (<span class="id"
type="var">ANum</span> 0);;\
   <span class="id" type="var">Z</span> ::= (<span class="id"
type="var">ANum</span> 1).\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">p3\_p4\_inequiv</span> : ¬ <span class="id"
type="var">cequiv</span> <span class="id" type="var">p3</span> <span
class="id" type="var">p4</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 5 stars, advanced, optional (p5\_p6\_equiv) {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">p5</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">WHILE</span> (<span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 1))) <span class="id"
type="var">DO</span>\
     <span class="id" type="var">HAVOC</span> <span class="id"
type="var">X</span>\
   <span class="id" type="var">END</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">p6</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">X</span> ::= <span class="id"
type="var">ANum</span> 1.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">p5\_p6\_equiv</span> : <span class="id"
type="var">cequiv</span> <span class="id" type="var">p5</span> <span
class="id" type="var">p6</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Himp</span>.\
\

</div>

<div class="doc">

Doing Without Extensionality (Advanced) {.section}
=======================================

<div class="paragraph">

</div>

Purists might object to using the <span class="inlinecode"><span
class="id" type="var">functional\_extensionality</span></span> axiom. In
general, it can be quite dangerous to add axioms, particularly several
at once (as they may be mutually inconsistent). In fact, <span
class="inlinecode"><span class="id"
type="var">functional\_extensionality</span></span> and <span
class="inlinecode"><span class="id"
type="var">excluded\_middle</span></span> can both be assumed without
any problems, but some Coq users prefer to avoid such "heavyweight"
general techniques, and instead craft solutions for specific problems
that stay within Coq's standard logic.
<div class="paragraph">

</div>

For our particular problem here, rather than extending the definition of
equality to do what we want on functions representing states, we could
instead give an explicit notion of *equivalence* on states. For example:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">stequiv</span> (<span class="id" type="var">st1</span> <span
class="id" type="var">st2</span> : <span class="id"
type="var">state</span>) : <span class="id" type="keyword">Prop</span>
:=\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="var">id</span>), <span
class="id" type="var">st1</span> <span class="id" type="var">X</span> =
<span class="id" type="var">st2</span> <span class="id"
type="var">X</span>.\
\
 <span class="id" type="keyword">Notation</span> "st1 '¬' st2" := (<span
class="id" type="var">stequiv</span> <span class="id"
type="var">st1</span> <span class="id" type="var">st2</span>) (<span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 30).\
\

</div>

<div class="doc">

It is easy to prove that <span class="inlinecode"><span class="id"
type="var">stequiv</span></span> is an *equivalence* (i.e., it is
reflexive, symmetric, and transitive), so it partitions the set of all
states into equivalence classes.
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (stequiv\_refl) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">stequiv\_refl</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st</span> : <span class="id" type="var">state</span>),\
   <span class="id" type="var">st</span> ¬ <span class="id"
type="var">st</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (stequiv\_sym) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">stequiv\_sym</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st1</span> <span class="id" type="var">st2</span> : <span
class="id" type="var">state</span>),\
   <span class="id" type="var">st1</span> ¬ <span class="id"
type="var">st2</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">st2</span> ¬ <span class="id"
type="var">st1</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (stequiv\_trans) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">stequiv\_trans</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st1</span> <span class="id" type="var">st2</span> <span
class="id" type="var">st3</span> : <span class="id"
type="var">state</span>),\
   <span class="id" type="var">st1</span> ¬ <span class="id"
type="var">st2</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">st2</span> ¬ <span class="id"
type="var">st3</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">st1</span> ¬ <span class="id"
type="var">st3</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Another useful fact...
#### Exercise: 1 star, optional (stequiv\_update) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">stequiv\_update</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st1</span> <span class="id" type="var">st2</span> : <span
class="id" type="var">state</span>),\
   <span class="id" type="var">st1</span> ¬ <span class="id"
type="var">st2</span> <span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="var">id</span>) (<span
class="id" type="var">n</span>:<span class="id" type="var">nat</span>),\
   <span class="id" type="var">update</span> <span class="id"
type="var">st1</span> <span class="id" type="var">X</span> <span
class="id" type="var">n</span> ¬ <span class="id"
type="var">update</span> <span class="id" type="var">st2</span> <span
class="id" type="var">X</span> <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

It is then straightforward to show that <span class="inlinecode"><span
class="id" type="var">aeval</span></span> and <span
class="inlinecode"><span class="id" type="var">beval</span></span>
behave uniformly on all members of an equivalence class:
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (stequiv\_aeval) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">stequiv\_aeval</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st1</span> <span class="id" type="var">st2</span> : <span
class="id" type="var">state</span>),\
   <span class="id" type="var">st1</span> ¬ <span class="id"
type="var">st2</span> <span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">a</span>:<span class="id" type="var">aexp</span>), <span
class="id" type="var">aeval</span> <span class="id"
type="var">st1</span> <span class="id" type="var">a</span> = <span
class="id" type="var">aeval</span> <span class="id"
type="var">st2</span> <span class="id" type="var">a</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (stequiv\_beval) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">stequiv\_beval</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st1</span> <span class="id" type="var">st2</span> : <span
class="id" type="var">state</span>),\
   <span class="id" type="var">st1</span> ¬ <span class="id"
type="var">st2</span> <span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">b</span>:<span class="id" type="var">bexp</span>), <span
class="id" type="var">beval</span> <span class="id"
type="var">st1</span> <span class="id" type="var">b</span> = <span
class="id" type="var">beval</span> <span class="id"
type="var">st2</span> <span class="id" type="var">b</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

We can also characterize the behavior of <span class="inlinecode"><span
class="id" type="var">ceval</span></span> on equivalent states (this
result is a bit more complicated to write down because <span
class="inlinecode"><span class="id" type="var">ceval</span></span> is a
relation).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">stequiv\_ceval</span>: <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st1</span> <span class="id" type="var">st2</span> : <span
class="id" type="var">state</span>),\
   <span class="id" type="var">st1</span> ¬ <span class="id"
type="var">st2</span> <span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">c</span>: <span class="id" type="var">com</span>) (<span
class="id" type="var">st1'</span>: <span class="id"
type="var">state</span>),\
     (<span class="id" type="var">c</span> / <span class="id"
type="var">st1</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st1'</span>) <span
style="font-family: arial;">→</span>\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">st2'</span> : <span class="id" type="var">state</span>,\
     ((<span class="id" type="var">c</span> / <span class="id"
type="var">st2</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st2'</span>) <span
style="font-family: arial;">∧</span> <span class="id"
type="var">st1'</span> ¬ <span class="id" type="var">st2'</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">st1</span> <span class="id" type="var">st2</span> <span
class="id" type="var">STEQV</span> <span class="id" type="var">c</span>
<span class="id" type="var">st1'</span> <span class="id"
type="var">CEV1</span>. <span class="id" type="tactic">generalize</span>
<span class="id" type="tactic">dependent</span> <span class="id"
type="var">st2</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">CEV1</span>; <span class="id" type="tactic">intros</span>
<span class="id" type="var">st2</span> <span class="id"
type="var">STEQV</span>.\
   <span class="id" type="var">Case</span> "SKIP".\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">st2</span>. <span class="id" type="tactic">split</span>.\
       <span class="id" type="var">constructor</span>.\
       <span class="id" type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> ":=".\
     <span style="font-family: arial;">∃</span>(<span class="id"
type="var">update</span> <span class="id" type="var">st2</span> <span
class="id" type="var">x</span> <span class="id" type="var">n</span>).
<span class="id" type="tactic">split</span>.\
        <span class="id" type="var">constructor</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">H</span>. <span class="id"
type="tactic">symmetry</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">stequiv\_aeval</span>.\
        <span class="id" type="tactic">assumption</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">stequiv\_update</span>. <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> ";".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHCEV1\_1</span> <span class="id" type="var">st2</span> <span
class="id" type="var">STEQV</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">st2'</span> [<span
class="id" type="var">P1</span> <span class="id"
type="var">EQV1</span>]].\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHCEV1\_2</span> <span class="id" type="var">st2'</span>
<span class="id" type="var">EQV1</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">st2''</span>
[<span class="id" type="var">P2</span> <span class="id"
type="var">EQV2</span>]].\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">st2''</span>. <span class="id" type="tactic">split</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Seq</span> <span class="id" type="keyword">with</span>
<span class="id" type="var">st2'</span>; <span class="id"
type="tactic">assumption</span>.\
       <span class="id" type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "IfTrue".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHCEV1</span> <span class="id" type="var">st2</span> <span
class="id" type="var">STEQV</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">st2'</span> [<span
class="id" type="var">P</span> <span class="id"
type="var">EQV</span>]].\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">st2'</span>. <span class="id" type="tactic">split</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_IfTrue</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">H</span>. <span class="id"
type="tactic">symmetry</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">stequiv\_beval</span>.\
       <span class="id" type="tactic">assumption</span>. <span
class="id" type="tactic">assumption</span>. <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "IfFalse".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHCEV1</span> <span class="id" type="var">st2</span> <span
class="id" type="var">STEQV</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">st2'</span> [<span
class="id" type="var">P</span> <span class="id"
type="var">EQV</span>]].\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">st2'</span>. <span class="id" type="tactic">split</span>.\
      <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_IfFalse</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">H</span>. <span class="id"
type="tactic">symmetry</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">stequiv\_beval</span>.\
      <span class="id" type="tactic">assumption</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "WhileEnd".\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">st2</span>. <span class="id" type="tactic">split</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_WhileEnd</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">H</span>. <span class="id"
type="tactic">symmetry</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">stequiv\_beval</span>.\
       <span class="id" type="tactic">assumption</span>. <span
class="id" type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "WhileLoop".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHCEV1\_1</span> <span class="id" type="var">st2</span> <span
class="id" type="var">STEQV</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">st2'</span> [<span
class="id" type="var">P1</span> <span class="id"
type="var">EQV1</span>]].\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHCEV1\_2</span> <span class="id" type="var">st2'</span>
<span class="id" type="var">EQV1</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">st2''</span>
[<span class="id" type="var">P2</span> <span class="id"
type="var">EQV2</span>]].\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">st2''</span>. <span class="id" type="tactic">split</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_WhileLoop</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">st2'</span>.
<span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">symmetry</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">stequiv\_beval</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="tactic">assumption</span>.\
       <span class="id" type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Now we need to redefine <span class="inlinecode"><span class="id"
type="var">cequiv</span></span> to use <span class="inlinecode">¬</span>
instead of <span class="inlinecode">=</span>. It is not completely
trivial to do this in a way that keeps the definition simple and
symmetric, but here is one approach (thanks to Andrew McCreight). We
first define a looser variant of <span class="inlinecode"><span
style="font-family: arial;">⇓</span></span> that "folds in" the notion
of equivalence.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> "c1 '/' st
'<span style="font-family: arial;">⇓</span>'' st'" (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40,
<span class="id" type="var">st</span> <span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 39).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ceval'</span> : <span class="id" type="var">com</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">state</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">state</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">E\_equiv</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span> <span class="id" type="var">st''</span>,\
     <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">st'</span> ¬ <span class="id"
type="var">st''</span> <span style="font-family: arial;">→</span>\
     <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span>' <span
class="id" type="var">st''</span>\
   <span class="id" type="keyword">where</span> "c1 '/' st '<span
style="font-family: arial;">⇓</span>'' st'" := (<span class="id"
type="var">ceval'</span> <span class="id" type="var">c1</span> <span
class="id" type="var">st</span> <span class="id"
type="var">st'</span>).\
\

</div>

<div class="doc">

Now the revised definition of <span class="inlinecode"><span class="id"
type="var">cequiv'</span></span> looks familiar:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">cequiv'</span> (<span class="id" type="var">c1</span> <span
class="id" type="var">c2</span> : <span class="id"
type="var">com</span>) : <span class="id" type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">st</span> <span class="id" type="var">st'</span> : <span
class="id" type="var">state</span>),\
     (<span class="id" type="var">c1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span>' <span
class="id" type="var">st'</span>) <span
style="font-family: arial;">↔</span> (<span class="id"
type="var">c2</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span>' <span class="id"
type="var">st'</span>).\
\

</div>

<div class="doc">

A sanity check shows that the original notion of command equivalence is
at least as strong as this new one. (The converse is not true,
naturally.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">cequiv\_\_cequiv'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">c1</span> <span class="id" type="var">c2</span>: <span
class="id" type="var">com</span>),\
   <span class="id" type="var">cequiv</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c2</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">cequiv'</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">cequiv</span>, <span class="id" type="var">cequiv'</span>;
<span class="id" type="tactic">split</span>; <span class="id"
type="tactic">intros</span>.\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span> ; <span class="id" type="tactic">subst</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_equiv</span> <span class="id" type="keyword">with</span>
<span class="id" type="var">st'0</span>.\
     <span class="id" type="tactic">apply</span> (<span class="id"
type="var">H</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'0</span>); <span class="id"
type="tactic">assumption</span>. <span class="id"
type="tactic">assumption</span>.\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span> ; <span class="id" type="tactic">subst</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_equiv</span> <span class="id" type="keyword">with</span>
<span class="id" type="var">st'0</span>.\
     <span class="id" type="tactic">apply</span> (<span class="id"
type="var">H</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'0</span>). <span class="id"
type="tactic">assumption</span>. <span class="id"
type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (identity\_assignment') {.section}

Finally, here is our example once more... (You can complete the proof.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">identity\_assignment'</span> :\
   <span class="id" type="var">cequiv'</span> <span class="id"
type="var">SKIP</span> (<span class="id" type="var">X</span> ::= <span
class="id" type="var">AId</span> <span class="id" type="var">X</span>).\
 <span class="id" type="keyword">Proof</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">cequiv'</span>. <span class="id" type="tactic">intros</span>.
<span class="id" type="tactic">split</span>; <span class="id"
type="tactic">intros</span>.\
     <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">inversion</span>
<span class="id" type="var">H0</span>; <span class="id"
type="tactic">subst</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_equiv</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">update</span> <span class="id"
type="var">st'0</span> <span class="id" type="var">X</span> (<span
class="id" type="var">st'0</span> <span class="id"
type="var">X</span>)).\
       <span class="id" type="var">constructor</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">stequiv\_trans</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">st'0</span>.\
       <span class="id" type="tactic">unfold</span> <span class="id"
type="var">stequiv</span>. <span class="id" type="tactic">intros</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">update\_same</span>.\
       <span class="id" type="tactic">reflexivity</span>. <span
class="id" type="tactic">assumption</span>.\
     <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
       <span class="comment">(\* FILL IN HERE \*)</span> <span
class="id" type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

On the whole, this explicit equivalence approach is considerably harder
to work with than relying on functional extensionality. (Coq does have
an advanced mechanism called "setoids" that makes working with
equivalences somewhat easier, by allowing them to be registered with the
system so that standard rewriting tactics work for them almost as well
as for equalities.) But it is worth knowing about, because it applies
even in situations where the equivalence in question is *not* over
functions. For example, if we chose to represent state mappings as
binary search trees, we would need to use an explicit equivalence of
this kind.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Additional Exercises {.section}
====================

<div class="paragraph">

</div>

#### Exercise: 4 stars, optional (for\_while\_equiv) {.section}

This exercise extends the optional <span class="inlinecode"><span
class="id" type="var">add\_for\_loop</span></span> exercise from Imp.v,
where you were asked to extend the language of commands with C-style
<span class="inlinecode"><span class="id"
type="keyword">for</span></span> loops. Prove that the command:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="keyword">for</span> (<span class="id"
type="var">c1</span> ; <span class="id" type="var">b</span> ; <span
class="id" type="var">c2</span>) {\
           <span class="id" type="var">c3</span>\
       }
<div class="paragraph">

</div>

</div>

is equivalent to:
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="var">c1</span> ; \
        <span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span>\
          <span class="id" type="var">c3</span> ;\
          <span class="id" type="var">c2</span>\
        <span class="id" type="var">END</span>
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

<span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (swap\_noninterfering\_assignments) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">swap\_noninterfering\_assignments</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">l1</span> <span class="id" type="var">l2</span> <span
class="id" type="var">a1</span> <span class="id" type="var">a2</span>,\
   <span class="id" type="var">l1</span> ≠ <span class="id"
type="var">l2</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">var\_not\_used\_in\_aexp</span> <span
class="id" type="var">l1</span> <span class="id" type="var">a2</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">var\_not\_used\_in\_aexp</span> <span
class="id" type="var">l2</span> <span class="id" type="var">a1</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">cequiv</span>\
     (<span class="id" type="var">l1</span> ::= <span class="id"
type="var">a1</span>;; <span class="id" type="var">l2</span> ::= <span
class="id" type="var">a2</span>)\
     (<span class="id" type="var">l2</span> ::= <span class="id"
type="var">a2</span>;; <span class="id" type="var">l1</span> ::= <span
class="id" type="var">a1</span>).\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* Hint: You'll need <span
class="inlinecode"><span class="id"
type="var">functional\_extensionality</span></span> \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

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
