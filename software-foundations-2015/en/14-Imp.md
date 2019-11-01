<div id="page">

<div id="header">

</div>

<div id="main">

Imp<span class="subtitle">Simple Imperative Programs</span> {.libtitle}
===========================================================

<div class="code code-tight">

</div>

<div class="doc">

<div class="paragraph">

</div>

In this chapter, we begin a new direction that will continue for the
rest of the course. Up to now most of our attention has been focused on
various aspects of Coq itself, while from now on we'll mostly be using
Coq to formalize other things. (We'll continue to pause from time to
time to introduce a few additional aspects of Coq.)
<div class="paragraph">

</div>

Our first case study is a *simple imperative programming language*
called Imp, embodying a tiny core fragment of conventional mainstream
languages such as C and Java. Here is a familiar mathematical function
written in Imp.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">Z</span> ::= <span class="id"
type="var">X</span>;;\
      <span class="id" type="var">Y</span> ::= 1;;\
      <span class="id" type="var">WHILE</span> <span class="id"
type="var">not</span> (<span class="id" type="var">Z</span> = 0) <span
class="id" type="var">DO</span>\
        <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> × <span class="id" type="var">Z</span>;;\
        <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span> - 1\
      <span class="id" type="var">END</span>
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

This chapter looks at how to define the *syntax* and *semantics* of Imp;
the chapters that follow develop a theory of *program equivalence* and
introduce *Hoare Logic*, a widely used logic for reasoning about
imperative programs.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Sflib {.section}

<div class="paragraph">

</div>

A minor technical point: Instead of asking Coq to import our earlier
definitions from chapter <span class="inlinecode"><span class="id"
type="var">Logic</span></span>, we import a small library called <span
class="inlinecode"><span class="id" type="var">Sflib.v</span></span>,
containing just a few definitions and theorems from earlier chapters
that we'll actually use in the rest of the course. This change should be
nearly invisible, since most of what's missing from Sflib has identical
definitions in the Coq standard library. The main reason for doing it is
to tidy the global Coq environment so that, for example, it is easier to
search for relevant theorems.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">SfLib</span>.\
\

</div>

<div class="doc">

Arithmetic and Boolean Expressions {.section}
==================================

<div class="paragraph">

</div>

We'll present Imp in three parts: first a core language of *arithmetic
and boolean expressions*, then an extension of these expressions with
*variables*, and finally a language of *commands* including assignment,
conditions, sequencing, and loops.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Syntax {.section}
------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">AExp</span>.\
\

</div>

<div class="doc">

These two definitions specify the *abstract syntax* of arithmetic and
boolean expressions.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">aexp</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">ANum</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span>\
   | <span class="id" type="var">APlus</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>\
   | <span class="id" type="var">AMinus</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>\
   | <span class="id" type="var">AMult</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">bexp</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">BTrue</span> : <span class="id"
type="var">bexp</span>\
   | <span class="id" type="var">BFalse</span> : <span class="id"
type="var">bexp</span>\
   | <span class="id" type="var">BEq</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bexp</span>\
   | <span class="id" type="var">BLe</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bexp</span>\
   | <span class="id" type="var">BNot</span> : <span class="id"
type="var">bexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">bexp</span>\
   | <span class="id" type="var">BAnd</span> : <span class="id"
type="var">bexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">bexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bexp</span>.\
\

</div>

<div class="doc">

In this chapter, we'll elide the translation from the concrete syntax
that a programmer would actually write to these abstract syntax trees —
the process that, for example, would translate the string <span
class="inlinecode">"1+2×3"</span> to the AST <span
class="inlinecode"><span class="id" type="var">APlus</span></span> <span
class="inlinecode">(<span class="id" type="var">ANum</span></span> <span
class="inlinecode">1)</span> <span class="inlinecode">(<span class="id"
type="var">AMult</span></span> <span class="inlinecode">(<span
class="id" type="var">ANum</span></span> <span
class="inlinecode">2)</span> <span class="inlinecode">(<span class="id"
type="var">ANum</span></span> <span class="inlinecode">3))</span>. The
optional chapter <span class="inlinecode"><span class="id"
type="var">ImpParser</span></span> develops a simple implementation of a
lexical analyzer and parser that can perform this translation. You do
*not* need to understand that file to understand this one, but if you
haven't taken a course where these techniques are covered (e.g., a
compilers course) you may want to skim it.
<div class="paragraph">

</div>

###  {.section}

For comparison, here's a conventional BNF (Backus-Naur Form) grammar
defining the same abstract syntax:
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="var">a</span> ::= <span class="id"
type="var">nat</span>\
         | <span class="id" type="var">a</span> + <span class="id"
type="var">a</span>\
         | <span class="id" type="var">a</span> - <span class="id"
type="var">a</span>\
         | <span class="id" type="var">a</span> × <span class="id"
type="var">a</span>\
\
     <span class="id" type="var">b</span> ::= <span class="id"
type="var">true</span>\
         | <span class="id" type="var">false</span>\
         | <span class="id" type="var">a</span> = <span class="id"
type="var">a</span>\
         | <span class="id" type="var">a</span> ≤ <span class="id"
type="var">a</span>\
         | <span class="id" type="var">not</span> <span class="id"
type="var">b</span>\
         | <span class="id" type="var">b</span> <span class="id"
type="var">and</span> <span class="id" type="var">b</span>
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Compared to the Coq version above...
<div class="paragraph">

</div>

-   The BNF is more informal — for example, it gives some suggestions
    about the surface syntax of expressions (like the fact that the
    addition operation is written <span class="inlinecode">+</span> and
    is an infix symbol) while leaving other aspects of lexical analysis
    and parsing (like the relative precedence of <span
    class="inlinecode">+</span>, <span class="inlinecode">-</span>, and
    <span class="inlinecode">×</span>) unspecified. Some additional
    information — and human intelligence — would be required to turn
    this description into a formal definition (when implementing a
    compiler, for example).
    <div class="paragraph">

    </div>

    The Coq version consistently omits all this information and
    concentrates on the abstract syntax only.
    <div class="paragraph">

    </div>

-   On the other hand, the BNF version is lighter and easier to read.
    Its informality makes it flexible, which is a huge advantage in
    situations like discussions at the blackboard, where conveying
    general ideas is more important than getting every detail nailed
    down precisely.
    <div class="paragraph">

    </div>

    Indeed, there are dozens of BNF-like notations and people switch
    freely among them, usually without bothering to say which form of
    BNF they're using because there is no need to: a rough-and-ready
    informal understanding is all that's needed.

<div class="paragraph">

</div>

It's good to be comfortable with both sorts of notations: informal ones
for communicating between humans and formal ones for carrying out
implementations and proofs.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Evaluation {.section}
----------

<div class="paragraph">

</div>

*Evaluating* an arithmetic expression produces a number.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">aeval</span> (<span class="id" type="var">a</span> : <span
class="id" type="var">aexp</span>) : <span class="id"
type="var">nat</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">a</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">ANum</span> <span class="id"
type="var">n</span> ⇒ <span class="id" type="var">n</span>\
   | <span class="id" type="var">APlus</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ (<span
class="id" type="var">aeval</span> <span class="id"
type="var">a1</span>) + (<span class="id" type="var">aeval</span> <span
class="id" type="var">a2</span>)\
   | <span class="id" type="var">AMinus</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ (<span
class="id" type="var">aeval</span> <span class="id"
type="var">a1</span>) - (<span class="id" type="var">aeval</span> <span
class="id" type="var">a2</span>)\
   | <span class="id" type="var">AMult</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ (<span
class="id" type="var">aeval</span> <span class="id"
type="var">a1</span>) × (<span class="id" type="var">aeval</span> <span
class="id" type="var">a2</span>)\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_aeval1</span>:\
   <span class="id" type="var">aeval</span> (<span class="id"
type="var">APlus</span> (<span class="id" type="var">ANum</span> 2)
(<span class="id" type="var">ANum</span> 2)) = 4.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

Similarly, evaluating a boolean expression yields a boolean.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">beval</span> (<span class="id" type="var">b</span> : <span
class="id" type="var">bexp</span>) : <span class="id"
type="var">bool</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">b</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">BTrue</span> ⇒ <span class="id"
type="var">true</span>\
   | <span class="id" type="var">BFalse</span> ⇒ <span class="id"
type="var">false</span>\
   | <span class="id" type="var">BEq</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ <span
class="id" type="var">beq\_nat</span> (<span class="id"
type="var">aeval</span> <span class="id" type="var">a1</span>) (<span
class="id" type="var">aeval</span> <span class="id"
type="var">a2</span>)\
   | <span class="id" type="var">BLe</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ <span
class="id" type="var">ble\_nat</span> (<span class="id"
type="var">aeval</span> <span class="id" type="var">a1</span>) (<span
class="id" type="var">aeval</span> <span class="id"
type="var">a2</span>)\
   | <span class="id" type="var">BNot</span> <span class="id"
type="var">b1</span> ⇒ <span class="id" type="var">negb</span> (<span
class="id" type="var">beval</span> <span class="id"
type="var">b1</span>)\
   | <span class="id" type="var">BAnd</span> <span class="id"
type="var">b1</span> <span class="id" type="var">b2</span> ⇒ <span
class="id" type="var">andb</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">b1</span>) (<span
class="id" type="var">beval</span> <span class="id"
type="var">b2</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Optimization {.section}
------------

<div class="paragraph">

</div>

We haven't defined very much yet, but we can already get some mileage
out of the definitions. Suppose we define a function that takes an
arithmetic expression and slightly simplifies it, changing every
occurrence of <span class="inlinecode">0+<span class="id"
type="var">e</span></span> (i.e., <span class="inlinecode">(<span
class="id" type="var">APlus</span></span> <span
class="inlinecode">(<span class="id" type="var">ANum</span></span> <span
class="inlinecode">0)</span> <span class="inlinecode"><span class="id"
type="var">e</span></span>) into just <span class="inlinecode"><span
class="id" type="var">e</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">optimize\_0plus</span> (<span class="id"
type="var">a</span>:<span class="id" type="var">aexp</span>) : <span
class="id" type="var">aexp</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">a</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">ANum</span> <span class="id"
type="var">n</span> ⇒\
       <span class="id" type="var">ANum</span> <span class="id"
type="var">n</span>\
   | <span class="id" type="var">APlus</span> (<span class="id"
type="var">ANum</span> 0) <span class="id" type="var">e2</span> ⇒\
       <span class="id" type="var">optimize\_0plus</span> <span
class="id" type="var">e2</span>\
   | <span class="id" type="var">APlus</span> <span class="id"
type="var">e1</span> <span class="id" type="var">e2</span> ⇒\
       <span class="id" type="var">APlus</span> (<span class="id"
type="var">optimize\_0plus</span> <span class="id" type="var">e1</span>)
(<span class="id" type="var">optimize\_0plus</span> <span class="id"
type="var">e2</span>)\
   | <span class="id" type="var">AMinus</span> <span class="id"
type="var">e1</span> <span class="id" type="var">e2</span> ⇒\
       <span class="id" type="var">AMinus</span> (<span class="id"
type="var">optimize\_0plus</span> <span class="id" type="var">e1</span>)
(<span class="id" type="var">optimize\_0plus</span> <span class="id"
type="var">e2</span>)\
   | <span class="id" type="var">AMult</span> <span class="id"
type="var">e1</span> <span class="id" type="var">e2</span> ⇒\
       <span class="id" type="var">AMult</span> (<span class="id"
type="var">optimize\_0plus</span> <span class="id" type="var">e1</span>)
(<span class="id" type="var">optimize\_0plus</span> <span class="id"
type="var">e2</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

To make sure our optimization is doing the right thing we can test it on
some examples and see if the output looks OK.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_optimize\_0plus</span>:\
   <span class="id" type="var">optimize\_0plus</span> (<span class="id"
type="var">APlus</span> (<span class="id" type="var">ANum</span> 2)\
                         (<span class="id" type="var">APlus</span>
(<span class="id" type="var">ANum</span> 0)\
                                (<span class="id"
type="var">APlus</span> (<span class="id" type="var">ANum</span> 0)
(<span class="id" type="var">ANum</span> 1))))\
   = <span class="id" type="var">APlus</span> (<span class="id"
type="var">ANum</span> 2) (<span class="id" type="var">ANum</span> 1).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

But if we want to be sure the optimization is correct — i.e., that
evaluating an optimized expression gives the same result as the original
— we should prove it.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">optimize\_0plus\_sound</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">a</span>,\
   <span class="id" type="var">aeval</span> (<span class="id"
type="var">optimize\_0plus</span> <span class="id" type="var">a</span>)
= <span class="id" type="var">aeval</span> <span class="id"
type="var">a</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">a</span>. <span class="id" type="tactic">induction</span>
<span class="id" type="var">a</span>.\
   <span class="id" type="var">Case</span> "ANum". <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "APlus". <span class="id"
type="tactic">destruct</span> <span class="id" type="var">a1</span>.\
     <span class="id" type="var">SCase</span> "a1 = ANum n". <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">n</span>.\
       <span class="id" type="var">SSCase</span> "n = 0". <span
class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHa2</span>.\
       <span class="id" type="var">SSCase</span> "n ≠ 0". <span
class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa2</span>.
<span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> "a1 = APlus a1\_1 a1\_2".\
       <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">IHa1</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa1</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHa2</span>. <span class="id"
type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> "a1 = AMinus a1\_1
a1\_2".\
       <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">IHa1</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa1</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHa2</span>. <span class="id"
type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> "a1 = AMult a1\_1 a1\_2".\
       <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">IHa1</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa1</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHa2</span>. <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "AMinus".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa1</span>.
<span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHa2</span>. <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "AMult".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa1</span>.
<span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHa2</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Coq Automation {.section}
==============

<div class="paragraph">

</div>

The repetition in this last proof is starting to be a little annoying.
If either the language of arithmetic expressions or the optimization
being proved sound were significantly more complex, it would begin to be
a real problem.
<div class="paragraph">

</div>

So far, we've been doing all our proofs using just a small handful of
Coq's tactics and completely ignoring its powerful facilities for
constructing parts of proofs automatically. This section introduces some
of these facilities, and we will see more over the next several
chapters. Getting used to them will take some energy — Coq's automation
is a power tool — but it will allow us to scale up our efforts to more
complex definitions and more interesting properties without becoming
overwhelmed by boring, repetitive, low-level details.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Tacticals {.section}
---------

<div class="paragraph">

</div>

*Tacticals* is Coq's term for tactics that take other tactics as
arguments — "higher-order tactics," if you will.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### The <span class="inlinecode"><span class="id" type="tactic">repeat</span></span> Tactical {.section}

<div class="paragraph">

</div>

The <span class="inlinecode"><span class="id"
type="tactic">repeat</span></span> tactical takes another tactic and
keeps applying this tactic until the tactic fails. Here is an example
showing that <span class="inlinecode">100</span> is even using repeat.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ev100</span> : <span class="id" type="var">ev</span> 100.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">repeat</span> (<span class="id"
type="tactic">apply</span> <span class="id" type="var">ev\_SS</span>).
<span class="comment">(\* applies ev\_SS 50 times,\
                            until <span class="inlinecode"><span
class="id" type="tactic">apply</span></span> <span
class="inlinecode"><span class="id"
type="var">ev\_SS</span></span> fails \*)</span>\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ev\_0</span>.\
 <span class="id" type="keyword">Qed</span>.\
 <span class="comment">(\* Print ev100. \*)</span>\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="tactic">repeat</span></span> <span class="inlinecode"><span
class="id" type="var">T</span></span> tactic never fails; if the tactic
<span class="inlinecode"><span class="id" type="var">T</span></span>
doesn't apply to the original goal, then repeat still succeeds without
changing the original goal (it repeats zero times).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ev100'</span> : <span class="id" type="var">ev</span> 100.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">repeat</span> (<span class="id"
type="tactic">apply</span> <span class="id" type="var">ev\_0</span>).
<span
class="comment">(\* doesn't fail, applies ev\_0 zero times \*)</span>\
   <span class="id" type="tactic">repeat</span> (<span class="id"
type="tactic">apply</span> <span class="id" type="var">ev\_SS</span>).
<span class="id" type="tactic">apply</span> <span class="id"
type="var">ev\_0</span>. <span
class="comment">(\* we can continue the proof \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="tactic">repeat</span></span> <span class="inlinecode"><span
class="id" type="var">T</span></span> tactic does not have any bound on
the number of times it applies <span class="inlinecode"><span class="id"
type="var">T</span></span>. If <span class="inlinecode"><span class="id"
type="var">T</span></span> is a tactic that always succeeds then repeat
<span class="inlinecode"><span class="id" type="var">T</span></span>
will loop forever (e.g. <span class="inlinecode"><span class="id"
type="tactic">repeat</span></span> <span class="inlinecode"><span
class="id" type="tactic">simpl</span></span> loops forever since <span
class="inlinecode"><span class="id" type="tactic">simpl</span></span>
always succeeds). While Coq's term language is guaranteed to terminate,
Coq's tactic language is not!

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### The <span class="inlinecode"><span class="id" type="tactic">try</span></span> Tactical {.section}

<div class="paragraph">

</div>

If <span class="inlinecode"><span class="id" type="var">T</span></span>
is a tactic, then <span class="inlinecode"><span class="id"
type="tactic">try</span></span> <span class="inlinecode"><span
class="id" type="var">T</span></span> is a tactic that is just like
<span class="inlinecode"><span class="id" type="var">T</span></span>
except that, if <span class="inlinecode"><span class="id"
type="var">T</span></span> fails, <span class="inlinecode"><span
class="id" type="tactic">try</span></span> <span
class="inlinecode"><span class="id" type="var">T</span></span>
*successfully* does nothing at all (instead of failing).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">silly1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ae</span>, <span class="id" type="var">aeval</span> <span
class="id" type="var">ae</span> = <span class="id"
type="var">aeval</span> <span class="id" type="var">ae</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">try</span> <span class="id"
type="tactic">reflexivity</span>. <span
class="comment">(\* this just does <span class="inlinecode"><span
class="id" type="tactic">reflexivity</span></span> \*)</span> <span
class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">silly2</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="keyword">Prop</span>),
<span class="id" type="var">P</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">HP</span>.\
   <span class="id" type="tactic">try</span> <span class="id"
type="tactic">reflexivity</span>. <span class="comment">(\* just <span
class="inlinecode"><span class="id"
type="tactic">reflexivity</span></span> would have failed \*)</span>\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">HP</span>. <span
class="comment">(\* we can still finish the proof in some other way \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Using <span class="inlinecode"><span class="id"
type="tactic">try</span></span> in a completely manual proof is a bit
silly, but we'll see below that <span class="inlinecode"><span
class="id" type="tactic">try</span></span> is very useful for doing
automated proofs in conjunction with the <span
class="inlinecode">;</span> tactical.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### The <span class="inlinecode">;</span> Tactical (Simple Form) {.section}

<div class="paragraph">

</div>

In its most commonly used form, the <span class="inlinecode">;</span>
tactical takes two tactics as argument: <span class="inlinecode"><span
class="id" type="var">T</span>;<span class="id"
type="var">T'</span></span> first performs the tactic <span
class="inlinecode"><span class="id" type="var">T</span></span> and then
performs the tactic <span class="inlinecode"><span class="id"
type="var">T'</span></span> on *each subgoal* generated by <span
class="inlinecode"><span class="id" type="var">T</span></span>.
<div class="paragraph">

</div>

For example, consider the following trivial lemma:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">foo</span> : <span style="font-family: arial;">∀</span><span
class="id" type="var">n</span>, <span class="id"
type="var">ble\_nat</span> 0 <span class="id" type="var">n</span> =
<span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">n</span>.\
     <span
class="comment">(\* Leaves two subgoals, which are discharged identically...  \*)</span>\
     <span class="id" type="var">Case</span> "n=0". <span class="id"
type="tactic">simpl</span>. <span class="id"
type="tactic">reflexivity</span>.\
     <span class="id" type="var">Case</span> "n=Sn'". <span class="id"
type="tactic">simpl</span>. <span class="id"
type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

We can simplify this proof using the <span class="inlinecode">;</span>
tactical:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">foo'</span> : <span style="font-family: arial;">∀</span><span
class="id" type="var">n</span>, <span class="id"
type="var">ble\_nat</span> 0 <span class="id" type="var">n</span> =
<span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">n</span>; <span class="comment">(\* <span
class="inlinecode"><span class="id"
type="tactic">destruct</span></span> the current goal \*)</span>\
   <span class="id" type="tactic">simpl</span>; <span
class="comment">(\* then <span class="inlinecode"><span class="id"
type="tactic">simpl</span></span> each resulting subgoal \*)</span>\
   <span class="id" type="tactic">reflexivity</span>. <span
class="comment">(\* and do <span class="inlinecode"><span class="id"
type="tactic">reflexivity</span></span> on each resulting subgoal \*)</span>\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Using <span class="inlinecode"><span class="id"
type="tactic">try</span></span> and <span class="inlinecode">;</span>
together, we can get rid of the repetition in the proof that was
bothering us a little while ago.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">optimize\_0plus\_sound'</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">a</span>,\
   <span class="id" type="var">aeval</span> (<span class="id"
type="var">optimize\_0plus</span> <span class="id" type="var">a</span>)
= <span class="id" type="var">aeval</span> <span class="id"
type="var">a</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">a</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">a</span>;\
     <span
class="comment">(\* Most cases follow directly by the IH \*)</span>\
     <span class="id" type="tactic">try</span> (<span class="id"
type="tactic">simpl</span>; <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa1</span>;
<span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHa2</span>; <span class="id"
type="tactic">reflexivity</span>).\
   <span
class="comment">(\* The remaining cases -- ANum and APlus -- are different \*)</span>\
   <span class="id" type="var">Case</span> "ANum". <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "APlus".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">a1</span>;\
       <span
class="comment">(\* Again, most cases follow directly by the IH \*)</span>\
       <span class="id" type="tactic">try</span> (<span class="id"
type="tactic">simpl</span>; <span class="id" type="tactic">simpl</span>
<span class="id" type="keyword">in</span> <span class="id"
type="var">IHa1</span>; <span class="id" type="tactic">rewrite</span>
<span class="id" type="var">IHa1</span>;\
            <span class="id" type="tactic">rewrite</span> <span
class="id" type="var">IHa2</span>; <span class="id"
type="tactic">reflexivity</span>).\
     <span class="comment">(\* The interesting case, on which the <span
class="inlinecode"><span class="id"
type="tactic">try</span>...</span> does nothing,\
        is when <span class="inlinecode"><span class="id"
type="var">e1</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">ANum</span></span> <span
class="inlinecode"><span class="id"
type="var">n</span></span>. In this case, we have to destruct\
        <span class="inlinecode"><span class="id"
type="var">n</span></span> (to see whether the optimization applies) and rewrite\
        with the induction hypothesis. \*)</span>\
     <span class="id" type="var">SCase</span> "a1 = ANum n". <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">n</span>;\
       <span class="id" type="tactic">simpl</span>; <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa2</span>;
<span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Coq experts often use this "<span class="inlinecode">...;</span> <span
class="inlinecode"><span class="id" type="tactic">try</span>...</span>
<span class="inlinecode"></span>" idiom after a tactic like <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> to take care of many similar cases
all at once. Naturally, this practice has an analog in informal proofs.
<div class="paragraph">

</div>

Here is an informal proof of this theorem that matches the structure of
the formal one:
<div class="paragraph">

</div>

*Theorem*: For all arithmetic expressions <span class="inlinecode"><span
class="id" type="var">a</span></span>,
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="var">aeval</span> (<span class="id"
type="var">optimize\_0plus</span> <span class="id"
type="var">a</span>) = <span class="id" type="var">aeval</span> <span
class="id" type="var">a</span>.
<div class="paragraph">

</div>

</div>

*Proof*: By induction on <span class="inlinecode"><span class="id"
type="var">a</span></span>. The <span class="inlinecode"><span
class="id" type="var">AMinus</span></span> and <span
class="inlinecode"><span class="id" type="var">AMult</span></span> cases
follow directly from the IH. The remaining cases are as follows:
<div class="paragraph">

</div>

-   Suppose <span class="inlinecode"><span class="id"
    type="var">a</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">ANum</span></span>
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    for some <span class="inlinecode"><span class="id"
    type="var">n</span></span>. We must show
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">aeval</span> (<span class="id"
    type="var">optimize\_0plus</span> (<span class="id"
    type="var">ANum</span> <span class="id"
    type="var">n</span>)) = <span class="id"
    type="var">aeval</span> (<span class="id"
    type="var">ANum</span> <span class="id" type="var">n</span>).
    <div class="paragraph">

    </div>

    </div>

    This is immediate from the definition of <span
    class="inlinecode"><span class="id"
    type="var">optimize\_0plus</span></span>.
    <div class="paragraph">

    </div>

-   Suppose <span class="inlinecode"><span class="id"
    type="var">a</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">APlus</span></span>
    <span class="inlinecode"><span class="id"
    type="var">a1</span></span> <span class="inlinecode"><span
    class="id" type="var">a2</span></span> for some <span
    class="inlinecode"><span class="id" type="var">a1</span></span> and
    <span class="inlinecode"><span class="id"
    type="var">a2</span></span>. We must show
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">aeval</span> (<span class="id"
    type="var">optimize\_0plus</span> (<span class="id"
    type="var">APlus</span> <span class="id" type="var">a1</span> <span
    class="id" type="var">a2</span>))\
     = <span class="id" type="var">aeval</span> (<span class="id"
    type="var">APlus</span> <span class="id" type="var">a1</span> <span
    class="id" type="var">a2</span>).
    <div class="paragraph">

    </div>

    </div>

    Consider the possible forms of <span class="inlinecode"><span
    class="id" type="var">a1</span></span>. For most of them, <span
    class="inlinecode"><span class="id"
    type="var">optimize\_0plus</span></span> simply calls itself
    recursively for the subexpressions and rebuilds a new expression of
    the same form as <span class="inlinecode"><span class="id"
    type="var">a1</span></span>; in these cases, the result follows
    directly from the IH.
    <div class="paragraph">

    </div>

    The interesting case is when <span class="inlinecode"><span
    class="id" type="var">a1</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">ANum</span></span> <span
    class="inlinecode"><span class="id" type="var">n</span></span> for
    some <span class="inlinecode"><span class="id"
    type="var">n</span></span>. If <span class="inlinecode"><span
    class="id" type="var">n</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">ANum</span></span> <span
    class="inlinecode">0</span>, then
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">optimize\_0plus</span> (<span
    class="id" type="var">APlus</span> <span class="id"
    type="var">a1</span> <span class="id" type="var">a2</span>) = <span
    class="id" type="var">optimize\_0plus</span> <span class="id"
    type="var">a2</span>
    <div class="paragraph">

    </div>

    </div>

    and the IH for <span class="inlinecode"><span class="id"
    type="var">a2</span></span> is exactly what we need. On the other
    hand, if <span class="inlinecode"><span class="id"
    type="var">n</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">S</span></span> <span
    class="inlinecode"><span class="id" type="var">n'</span></span> for
    some <span class="inlinecode"><span class="id"
    type="var">n'</span></span>, then again <span
    class="inlinecode"><span class="id"
    type="var">optimize\_0plus</span></span> simply calls itself
    recursively, and the result follows from the IH. ☐

<div class="paragraph">

</div>

This proof can still be improved: the first case (for <span
class="inlinecode"><span class="id" type="var">a</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">ANum</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span>) is very trivial — even more trivial than the
cases that we said simply followed from the IH — yet we have chosen to
write it out in full. It would be better and clearer to drop it and just
say, at the top, "Most cases are either immediate or direct from the IH.
The only interesting case is the one for <span class="inlinecode"><span
class="id" type="var">APlus</span></span>..." We can make the same
improvement in our formal proof too. Here's how it looks:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">optimize\_0plus\_sound''</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">a</span>,\
   <span class="id" type="var">aeval</span> (<span class="id"
type="var">optimize\_0plus</span> <span class="id" type="var">a</span>)
= <span class="id" type="var">aeval</span> <span class="id"
type="var">a</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">a</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">a</span>;\
     <span
class="comment">(\* Most cases follow directly by the IH \*)</span>\
     <span class="id" type="tactic">try</span> (<span class="id"
type="tactic">simpl</span>; <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa1</span>;
<span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHa2</span>; <span class="id"
type="tactic">reflexivity</span>);\
     <span
class="comment">(\* ... or are immediate by definition \*)</span>\
     <span class="id" type="tactic">try</span> <span class="id"
type="tactic">reflexivity</span>.\
   <span
class="comment">(\* The interesting case is when a = APlus a1 a2. \*)</span>\
   <span class="id" type="var">Case</span> "APlus".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">a1</span>; <span class="id" type="tactic">try</span> (<span
class="id" type="tactic">simpl</span>; <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">IHa1</span>; <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa1</span>;\
                       <span class="id" type="tactic">rewrite</span>
<span class="id" type="var">IHa2</span>; <span class="id"
type="tactic">reflexivity</span>).\
     <span class="id" type="var">SCase</span> "a1 = ANum n". <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">n</span>;\
       <span class="id" type="tactic">simpl</span>; <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa2</span>;
<span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### The <span class="inlinecode">;</span> Tactical (General Form) {.section}

<div class="paragraph">

</div>

The <span class="inlinecode">;</span> tactical has a more general than
the simple <span class="inlinecode"><span class="id"
type="var">T</span>;<span class="id" type="var">T'</span></span> we've
seen above, which is sometimes also useful. If <span
class="inlinecode"><span class="id" type="var">T</span></span>, <span
class="inlinecode"><span class="id" type="var">T~1~</span></span>, ...,
<span class="inlinecode"><span class="id" type="var">Tn</span></span>
are tactics, then
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">T</span>; [<span class="id"
type="var">T~1~</span> | <span class="id" type="var">T~2~</span> | ...
| <span class="id" type="var">Tn</span>]
<div class="paragraph">

</div>

</div>

is a tactic that first performs <span class="inlinecode"><span
class="id" type="var">T</span></span> and then performs <span
class="inlinecode"><span class="id" type="var">T~1~</span></span> on the
first subgoal generated by <span class="inlinecode"><span class="id"
type="var">T</span></span>, performs <span class="inlinecode"><span
class="id" type="var">T~2~</span></span> on the second subgoal, etc.
<div class="paragraph">

</div>

So <span class="inlinecode"><span class="id" type="var">T</span>;<span
class="id" type="var">T'</span></span> is just special notation for the
case when all of the <span class="inlinecode"><span class="id"
type="var">Ti</span></span>'s are the same tactic; i.e. <span
class="inlinecode"><span class="id" type="var">T</span>;<span class="id"
type="var">T'</span></span> is just a shorthand for:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">T</span>; [<span class="id"
type="var">T'</span> | <span class="id" type="var">T'</span> | ...
| <span class="id" type="var">T'</span>]
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Defining New Tactic Notations {.section}
-----------------------------

<div class="paragraph">

</div>

Coq also provides several ways of "programming" tactic scripts.
<div class="paragraph">

</div>

-   The <span class="inlinecode"><span class="id"
    type="keyword">Tactic</span></span> <span class="inlinecode"><span
    class="id" type="keyword">Notation</span></span> idiom illustrated
    below gives a handy way to define "shorthand tactics" that bundle
    several tactics into a single command.
    <div class="paragraph">

    </div>

-   For more sophisticated programming, Coq offers a small built-in
    programming language called <span class="inlinecode"><span
    class="id" type="keyword">Ltac</span></span> with primitives that
    can examine and modify the proof state. The details are a bit too
    complicated to get into here (and it is generally agreed that <span
    class="inlinecode"><span class="id"
    type="keyword">Ltac</span></span> is not the most beautiful part of
    Coq's design!), but they can be found in the reference manual, and
    there are many examples of <span class="inlinecode"><span class="id"
    type="keyword">Ltac</span></span> definitions in the Coq standard
    library that you can use as examples.
    <div class="paragraph">

    </div>

-   There is also an OCaml API, which can be used to build tactics that
    access Coq's internal structures at a lower level, but this is
    seldom worth the trouble for ordinary Coq users.

<div class="paragraph">

</div>

The <span class="inlinecode"><span class="id"
type="keyword">Tactic</span></span> <span class="inlinecode"><span
class="id" type="keyword">Notation</span></span> mechanism is the
easiest to come to grips with, and it offers plenty of power for many
purposes. Here's an example.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Tactic Notation</span>
"simpl\_and\_try" <span class="id" type="var">tactic</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="tactic">simpl</span>;\
   <span class="id" type="tactic">try</span> <span class="id"
type="var">c</span>.\
\

</div>

<div class="doc">

This defines a new tactical called <span class="inlinecode"><span
class="id" type="var">simpl\_and\_try</span></span> which takes one
tactic <span class="inlinecode"><span class="id"
type="var">c</span></span> as an argument, and is defined to be
equivalent to the tactic <span class="inlinecode"><span class="id"
type="tactic">simpl</span>;</span> <span class="inlinecode"><span
class="id" type="tactic">try</span></span> <span
class="inlinecode"><span class="id" type="var">c</span></span>. For
example, writing "<span class="inlinecode"><span class="id"
type="var">simpl\_and\_try</span></span> <span class="inlinecode"><span
class="id" type="tactic">reflexivity</span>.</span>" in a proof would be
the same as writing "<span class="inlinecode"><span class="id"
type="tactic">simpl</span>;</span> <span class="inlinecode"><span
class="id" type="tactic">try</span></span> <span
class="inlinecode"><span class="id"
type="tactic">reflexivity</span>.</span>"
<div class="paragraph">

</div>

The next subsection gives a more sophisticated use of this feature...

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Bulletproofing Case Analyses {.section}

<div class="paragraph">

</div>

Being able to deal with most of the cases of an <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> or <span class="inlinecode"><span
class="id" type="tactic">destruct</span></span> all at the same time is
very convenient, but it can also be a little confusing. One problem that
often comes up is that *maintaining* proofs written in this style can be
difficult. For example, suppose that, later, we extended the definition
of <span class="inlinecode"><span class="id"
type="var">aexp</span></span> with another constructor that also
required a special argument. The above proof might break because Coq
generated the subgoals for this constructor before the one for <span
class="inlinecode"><span class="id" type="var">APlus</span></span>, so
that, at the point when we start working on the <span
class="inlinecode"><span class="id" type="var">APlus</span></span> case,
Coq is actually expecting the argument for a completely different
constructor. What we'd like is to get a sensible error message saying "I
was expecting the <span class="inlinecode"><span class="id"
type="var">AFoo</span></span> case at this point, but the proof script
is talking about <span class="inlinecode"><span class="id"
type="var">APlus</span></span>." Here's a nice trick (due to Aaron
Bohannon) that smoothly achieves this.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Tactic Notation</span> "aexp\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ANum" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"APlus"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "AMinus" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "AMult"
].\
\

</div>

<div class="doc">

(<span class="inlinecode"><span class="id"
type="var">Case\_aux</span></span> implements the common functionality
of <span class="inlinecode"><span class="id"
type="var">Case</span></span>, <span class="inlinecode"><span class="id"
type="var">SCase</span></span>, <span class="inlinecode"><span
class="id" type="var">SSCase</span></span>, etc. For example, <span
class="inlinecode"><span class="id" type="var">Case</span></span> <span
class="inlinecode">"<span class="id" type="var">foo</span>"</span> is
defined as <span class="inlinecode"><span class="id"
type="var">Case\_aux</span></span> <span class="inlinecode"><span
class="id" type="var">Case</span></span> <span class="inlinecode">"<span
class="id" type="var">foo</span>".)</span> <span
class="inlinecode"></span>
<div class="paragraph">

</div>

For example, if <span class="inlinecode"><span class="id"
type="var">a</span></span> is a variable of type <span
class="inlinecode"><span class="id" type="var">aexp</span></span>, then
doing
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">aexp\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id"
type="var">a</span>) <span class="id" type="var">Case</span>
<div class="paragraph">

</div>

</div>

will perform an induction on <span class="inlinecode"><span class="id"
type="var">a</span></span> (the same as if we had just typed <span
class="inlinecode"><span class="id"
type="tactic">induction</span></span> <span class="inlinecode"><span
class="id" type="var">a</span></span>) and *also* add a <span
class="inlinecode"><span class="id" type="var">Case</span></span> tag to
each subgoal generated by the <span class="inlinecode"><span class="id"
type="tactic">induction</span></span>, labeling which constructor it
comes from. For example, here is yet another proof of <span
class="inlinecode"><span class="id"
type="var">optimize\_0plus\_sound</span></span>, using <span
class="inlinecode"><span class="id"
type="var">aexp\_cases</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">optimize\_0plus\_sound'''</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">a</span>,\
   <span class="id" type="var">aeval</span> (<span class="id"
type="var">optimize\_0plus</span> <span class="id" type="var">a</span>)
= <span class="id" type="var">aeval</span> <span class="id"
type="var">a</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">a</span>.\
   <span class="id" type="var">aexp\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">a</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">try</span> (<span class="id"
type="tactic">simpl</span>; <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa1</span>;
<span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHa2</span>; <span class="id"
type="tactic">reflexivity</span>);\
     <span class="id" type="tactic">try</span> <span class="id"
type="tactic">reflexivity</span>.\
   <span class="comment">(\* At this point, there is already an <span
class="inlinecode">"<span class="id"
type="var">APlus</span>"</span> case name\
      in the context.  The <span class="inlinecode"><span class="id"
type="var">Case</span></span> <span class="inlinecode">"<span class="id"
type="var">APlus</span>"</span> here in the proof\
      text has the effect of a sanity check: if the "Case"\
      string in the context is anything \_other\_ than <span
class="inlinecode">"<span class="id" type="var">APlus</span>"</span>\
      (for example, because we added a clause to the definition\
      of <span class="inlinecode"><span class="id"
type="var">aexp</span></span> and forgot to change the proof) we'll get a\
      helpful error at this point telling us that this is now\
      the wrong case. \*)</span>\
   <span class="id" type="var">Case</span> "APlus".\
     <span class="id" type="var">aexp\_cases</span> (<span class="id"
type="tactic">destruct</span> <span class="id" type="var">a1</span>)
<span class="id" type="var">SCase</span>;\
       <span class="id" type="tactic">try</span> (<span class="id"
type="tactic">simpl</span>; <span class="id" type="tactic">simpl</span>
<span class="id" type="keyword">in</span> <span class="id"
type="var">IHa1</span>;\
            <span class="id" type="tactic">rewrite</span> <span
class="id" type="var">IHa1</span>; <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa2</span>;
<span class="id" type="tactic">reflexivity</span>).\
     <span class="id" type="var">SCase</span> "ANum". <span class="id"
type="tactic">destruct</span> <span class="id" type="var">n</span>;\
       <span class="id" type="tactic">simpl</span>; <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHa2</span>;
<span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars (optimize\_0plus\_b) {.section}

Since the <span class="inlinecode"><span class="id"
type="var">optimize\_0plus</span></span> tranformation doesn't change
the value of <span class="inlinecode"><span class="id"
type="var">aexp</span></span>s, we should be able to apply it to all the
<span class="inlinecode"><span class="id" type="var">aexp</span></span>s
that appear in a <span class="inlinecode"><span class="id"
type="var">bexp</span></span> without changing the <span
class="inlinecode"><span class="id" type="var">bexp</span></span>'s
value. Write a function which performs that transformation on <span
class="inlinecode"><span class="id" type="var">bexp</span></span>s, and
prove it is sound. Use the tacticals we've just seen to make the proof
as elegant as possible.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">optimize\_0plus\_b</span> (<span class="id"
type="var">b</span> : <span class="id" type="var">bexp</span>) : <span
class="id" type="var">bexp</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">optimize\_0plus\_b\_sound</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">b</span>,\
   <span class="id" type="var">beval</span> (<span class="id"
type="var">optimize\_0plus\_b</span> <span class="id"
type="var">b</span>) = <span class="id" type="var">beval</span> <span
class="id" type="var">b</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, optional (optimizer) {.section}

*Design exercise*: The optimization implemented by our <span
class="inlinecode"><span class="id"
type="var">optimize\_0plus</span></span> function is only one of many
imaginable optimizations on arithmetic and boolean expressions. Write a
more sophisticated optimizer and prove it correct.
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id" type="tactic">omega</span></span> Tactic {.section}
--------------------------------------------------------------------------------------

<div class="paragraph">

</div>

The <span class="inlinecode"><span class="id"
type="tactic">omega</span></span> tactic implements a decision procedure
for a subset of first-order logic called *Presburger arithmetic*. It is
based on the Omega algorithm invented in 1992 by William Pugh.
<div class="paragraph">

</div>

If the goal is a universally quantified formula made out of
<div class="paragraph">

</div>

-   numeric constants, addition (<span class="inlinecode">+</span> and
    <span class="inlinecode"><span class="id"
    type="var">S</span></span>), subtraction (<span
    class="inlinecode">-</span> and <span class="inlinecode"><span
    class="id" type="var">pred</span></span>), and multiplication by
    constants (this is what makes it Presburger arithmetic),
    <div class="paragraph">

    </div>

-   equality (<span class="inlinecode">=</span> and <span
    class="inlinecode">≠</span>) and inequality (<span
    class="inlinecode">≤</span>), and
    <div class="paragraph">

    </div>

-   the logical connectives <span class="inlinecode"><span
    style="font-family: arial;">∧</span></span>, <span
    class="inlinecode"><span
    style="font-family: arial;">∨</span></span>, <span
    class="inlinecode">¬</span>, and <span class="inlinecode"><span
    style="font-family: arial;">→</span></span>,

<div class="paragraph">

</div>

then invoking <span class="inlinecode"><span class="id"
type="tactic">omega</span></span> will either solve the goal or tell you
that it is actually false.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">silly\_presburger\_example</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">m</span>
<span class="id" type="var">n</span> <span class="id"
type="var">o</span> <span class="id" type="var">p</span>,\
   <span class="id" type="var">m</span> + <span class="id"
type="var">n</span> ≤ <span class="id" type="var">n</span> + <span
class="id" type="var">o</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">o</span> + 3 = <span class="id" type="var">p</span> + 3 <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">m</span> ≤ <span class="id"
type="var">p</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">omega</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Leibniz wrote, "It is unworthy of excellent men to lose hours like
slaves in the labor of calculation which could be relegated to anyone
else if machines were used." We recommend using the omega tactic
whenever possible.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

A Few More Handy Tactics {.section}
------------------------

<div class="paragraph">

</div>

Finally, here are some miscellaneous tactics that you may find
convenient.
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="tactic">clear</span></span> <span class="inlinecode"><span
    class="id" type="var">H</span></span>: Delete hypothesis <span
    class="inlinecode"><span class="id" type="var">H</span></span> from
    the context.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">subst</span></span> <span class="inlinecode"><span
    class="id" type="var">x</span></span>: Find an assumption <span
    class="inlinecode"><span class="id" type="var">x</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">e</span></span> or <span
    class="inlinecode"><span class="id" type="var">e</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">x</span></span> in the context, replace <span
    class="inlinecode"><span class="id" type="var">x</span></span> with
    <span class="inlinecode"><span class="id" type="var">e</span></span>
    throughout the context and current goal, and clear the assumption.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">subst</span></span>: Substitute away *all* assumptions
    of the form <span class="inlinecode"><span class="id"
    type="var">x</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">e</span></span> or
    <span class="inlinecode"><span class="id" type="var">e</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">x</span></span>.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">rename</span>...</span> <span class="inlinecode"><span
    class="id" type="var">into</span>...</span>: Change the name of a
    hypothesis in the proof context. For example, if the context
    includes a variable named <span class="inlinecode"><span class="id"
    type="var">x</span></span>, then <span class="inlinecode"><span
    class="id" type="tactic">rename</span></span> <span
    class="inlinecode"><span class="id" type="var">x</span></span> <span
    class="inlinecode"><span class="id" type="var">into</span></span>
    <span class="inlinecode"><span class="id" type="var">y</span></span>
    will change all occurrences of <span class="inlinecode"><span
    class="id" type="var">x</span></span> to <span
    class="inlinecode"><span class="id" type="var">y</span></span>.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="tactic">assumption</span></span>: Try to find a hypothesis
    <span class="inlinecode"><span class="id" type="var">H</span></span>
    in the context that exactly matches the goal; if one is found,
    behave just like <span class="inlinecode"><span class="id"
    type="tactic">apply</span></span> <span class="inlinecode"><span
    class="id" type="var">H</span></span>.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">contradiction</span></span>: Try to find a hypothesis
    <span class="inlinecode"><span class="id" type="var">H</span></span>
    in the current context that is logically equivalent to <span
    class="inlinecode"><span class="id" type="var">False</span></span>.
    If one is found, solve the goal.
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">constructor</span></span>: Try to find a constructor
    <span class="inlinecode"><span class="id" type="var">c</span></span>
    (from some <span class="inlinecode"><span class="id"
    type="keyword">Inductive</span></span> definition in the current
    environment) that can be applied to solve the current goal. If one
    is found, behave like <span class="inlinecode"><span class="id"
    type="tactic">apply</span></span> <span class="inlinecode"><span
    class="id" type="var">c</span></span>.

<div class="paragraph">

</div>

We'll see many examples of these in the proofs below.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Evaluation as a Relation {.section}
========================

<div class="paragraph">

</div>

We have presented <span class="inlinecode"><span class="id"
type="var">aeval</span></span> and <span class="inlinecode"><span
class="id" type="var">beval</span></span> as functions defined by <span
class="inlinecode"><span class="id" type="var">Fixpoints</span></span>.
Another way to think about evaluation — one that we will see is often
more flexible — is as a *relation* between expressions and their values.
This leads naturally to <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> definitions like the following
one for arithmetic expressions...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">aevalR\_first\_try</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">aevalR</span> : <span class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">E\_ANum</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span>: <span class="id" type="var">nat</span>),\
       <span class="id" type="var">aevalR</span> (<span class="id"
type="var">ANum</span> <span class="id" type="var">n</span>) <span
class="id" type="var">n</span>\
   | <span class="id" type="var">E\_APlus</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">e1</span> <span class="id" type="var">e2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span>: <span
class="id" type="var">nat</span>),\
       <span class="id" type="var">aevalR</span> <span class="id"
type="var">e1</span> <span class="id" type="var">n1</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">aevalR</span> <span class="id"
type="var">e2</span> <span class="id" type="var">n2</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">aevalR</span> (<span class="id"
type="var">APlus</span> <span class="id" type="var">e1</span> <span
class="id" type="var">e2</span>) (<span class="id"
type="var">n1</span> + <span class="id" type="var">n2</span>)\
   | <span class="id" type="var">E\_AMinus</span>: <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">e1</span> <span class="id" type="var">e2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span>: <span
class="id" type="var">nat</span>),\
       <span class="id" type="var">aevalR</span> <span class="id"
type="var">e1</span> <span class="id" type="var">n1</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">aevalR</span> <span class="id"
type="var">e2</span> <span class="id" type="var">n2</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">aevalR</span> (<span class="id"
type="var">AMinus</span> <span class="id" type="var">e1</span> <span
class="id" type="var">e2</span>) (<span class="id"
type="var">n1</span> - <span class="id" type="var">n2</span>)\
   | <span class="id" type="var">E\_AMult</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">e1</span> <span class="id" type="var">e2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span>: <span
class="id" type="var">nat</span>),\
       <span class="id" type="var">aevalR</span> <span class="id"
type="var">e1</span> <span class="id" type="var">n1</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">aevalR</span> <span class="id"
type="var">e2</span> <span class="id" type="var">n2</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">aevalR</span> (<span class="id"
type="var">AMult</span> <span class="id" type="var">e1</span> <span
class="id" type="var">e2</span>) (<span class="id" type="var">n1</span>
× <span class="id" type="var">n2</span>).\
\

</div>

<div class="doc">

As is often the case with relations, we'll find it convenient to define
infix notation for <span class="inlinecode"><span class="id"
type="var">aevalR</span></span>. We'll write <span
class="inlinecode"><span class="id" type="var">e</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇓</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span> to
mean that arithmetic expression <span class="inlinecode"><span
class="id" type="var">e</span></span> evaluates to value <span
class="inlinecode"><span class="id" type="var">n</span></span>. (This
notation is one place where the limitation to ASCII symbols becomes a
little bothersome. The standard notation for the evaluation relation is
a double down-arrow. We'll typeset it like this in the HTML version of
the notes and use a double vertical bar as the closest approximation in
<span class="inlinecode">.<span class="id" type="var">v</span></span>
files.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "e '<span
style="font-family: arial;">⇓</span>' n" := (<span class="id"
type="var">aevalR</span> <span class="id" type="var">e</span> <span
class="id" type="var">n</span>) : <span class="id"
type="var">type\_scope</span>.\
\

</div>

<div class="doc">

In fact, Coq provides a way to use this notation in the definition of
<span class="inlinecode"><span class="id"
type="var">aevalR</span></span> itself. This avoids situations where
we're working on a proof involving statements in the form <span
class="inlinecode"><span class="id" type="var">e</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇓</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span> but
we have to refer back to a definition written using the form <span
class="inlinecode"><span class="id" type="var">aevalR</span></span>
<span class="inlinecode"><span class="id" type="var">e</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span>.
<div class="paragraph">

</div>

We do this by first "reserving" the notation, then giving the definition
together with a declaration of what the notation means.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> "e '<span
style="font-family: arial;">⇓</span>' n" (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 50,
<span class="id" type="var">left</span> <span class="id"
type="var">associativity</span>).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">aevalR</span> : <span class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">E\_ANum</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>),\
       (<span class="id" type="var">ANum</span> <span class="id"
type="var">n</span>) <span style="font-family: arial;">⇓</span> <span
class="id" type="var">n</span>\
   | <span class="id" type="var">E\_APlus</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">e1</span> <span class="id" type="var">e2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> : <span
class="id" type="var">nat</span>),\
       (<span class="id" type="var">e1</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n1</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">e2</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n2</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">APlus</span> <span class="id" type="var">e1</span>
<span class="id" type="var">e2</span>) <span
style="font-family: arial;">⇓</span> (<span class="id"
type="var">n1</span> + <span class="id" type="var">n2</span>)\
   | <span class="id" type="var">E\_AMinus</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">e1</span> <span class="id" type="var">e2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> : <span
class="id" type="var">nat</span>),\
       (<span class="id" type="var">e1</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n1</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">e2</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n2</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">AMinus</span> <span class="id"
type="var">e1</span> <span class="id" type="var">e2</span>) <span
style="font-family: arial;">⇓</span> (<span class="id"
type="var">n1</span> - <span class="id" type="var">n2</span>)\
   | <span class="id" type="var">E\_AMult</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">e1</span> <span class="id" type="var">e2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> : <span
class="id" type="var">nat</span>),\
       (<span class="id" type="var">e1</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n1</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">e2</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n2</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">AMult</span> <span class="id" type="var">e1</span>
<span class="id" type="var">e2</span>) <span
style="font-family: arial;">⇓</span> (<span class="id"
type="var">n1</span> × <span class="id" type="var">n2</span>)\
\
   <span class="id" type="keyword">where</span> "e '<span
style="font-family: arial;">⇓</span>' n" := (<span class="id"
type="var">aevalR</span> <span class="id" type="var">e</span> <span
class="id" type="var">n</span>) : <span class="id"
type="var">type\_scope</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span> "aevalR\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_ANum" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"E\_APlus"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_AMinus" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"E\_AMult" ].\
\

</div>

<div class="doc">

Inference Rule Notation {.section}
-----------------------

<div class="paragraph">

</div>

In informal discussions, it is convenient to write the rules for <span
class="inlinecode"><span class="id" type="var">aevalR</span></span> and
similar relations in the more readable graphical form of *inference
rules*, where the premises above the line justify the conclusion below
the line (we have already seen them in the Prop chapter).
<div class="paragraph">

</div>

For example, the constructor <span class="inlinecode"><span class="id"
type="var">E\_APlus</span></span>...
<div class="paragraph">

</div>

<div class="code code-tight">

      | <span class="id" type="var">E\_APlus</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">e1</span> <span class="id" type="var">e2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span>: <span
class="id" type="var">nat</span>),\
           <span class="id" type="var">aevalR</span> <span class="id"
type="var">e1</span> <span class="id" type="var">n1</span> <span
style="font-family: arial;">→</span>\
           <span class="id" type="var">aevalR</span> <span class="id"
type="var">e2</span> <span class="id" type="var">n2</span> <span
style="font-family: arial;">→</span>\
           <span class="id" type="var">aevalR</span> (<span class="id"
type="var">APlus</span> <span class="id" type="var">e1</span> <span
class="id" type="var">e2</span>) (<span class="id"
type="var">n1</span> + <span class="id" type="var">n2</span>)
<div class="paragraph">

</div>

</div>

...would be written like this as an inference rule:
e1 <span style="font-family: arial;">⇓</span> n1
e2 <span style="font-family: arial;">⇓</span> n2
(E\_APlus)  

------------------------------------------------------------------------

APlus e1 e2 <span style="font-family: arial;">⇓</span> n1+n2
<div class="paragraph">

</div>

Formally, there is nothing very deep about inference rules: they are
just implications. You can read the rule name on the right as the name
of the constructor and read each of the linebreaks between the premises
above the line and the line itself as <span class="inlinecode"><span
style="font-family: arial;">→</span></span>. All the variables mentioned
in the rule (<span class="inlinecode"><span class="id"
type="var">e1</span></span>, <span class="inlinecode"><span class="id"
type="var">n1</span></span>, etc.) are implicitly bound by universal
quantifiers at the beginning. (Such variables are often called
*metavariables* to distinguish them from the variables of the language
we are defining. At the moment, our arithmetic expressions don't include
variables, but we'll soon be adding them.) The whole collection of rules
is understood as being wrapped in an <span class="inlinecode"><span
class="id" type="keyword">Inductive</span></span> declaration
(informally, this is either elided or else indicated by saying something
like "Let <span class="inlinecode"><span class="id"
type="var">aevalR</span></span> be the smallest relation closed under
the following rules...").
<div class="paragraph">

</div>

For example, <span class="inlinecode"><span
style="font-family: arial;">⇓</span></span> is the smallest relation
closed under these rules:
  
(E\_ANum)  

------------------------------------------------------------------------

ANum n <span style="font-family: arial;">⇓</span> n
e1 <span style="font-family: arial;">⇓</span> n1
e2 <span style="font-family: arial;">⇓</span> n2
(E\_APlus)  

------------------------------------------------------------------------

APlus e1 e2 <span style="font-family: arial;">⇓</span> n1+n2
e1 <span style="font-family: arial;">⇓</span> n1
e2 <span style="font-family: arial;">⇓</span> n2
(E\_AMinus)  

------------------------------------------------------------------------

AMinus e1 e2 <span style="font-family: arial;">⇓</span> n1-n2
e1 <span style="font-family: arial;">⇓</span> n1
e2 <span style="font-family: arial;">⇓</span> n2
(E\_AMult)  

------------------------------------------------------------------------

AMult e1 e2 <span style="font-family: arial;">⇓</span> n1\*n2

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Equivalence of the Definitions {.section}
------------------------------

<div class="paragraph">

</div>

It is straightforward to prove that the relational and functional
definitions of evaluation agree on all possible arithmetic
expressions...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">aeval\_iff\_aevalR</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">a</span>
<span class="id" type="var">n</span>,\
   (<span class="id" type="var">a</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n</span>) <span style="font-family: arial;">↔</span> <span
class="id" type="var">aeval</span> <span class="id" type="var">a</span>
= <span class="id" type="var">n</span>.\
<div id="proofcontrol1" class="togglescript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')">

<span class="show"></span>

</div>

<div id="proof1" class="proofscript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
  <span class="id" type="tactic">split</span>.\
  <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
    <span class="id" type="tactic">intros</span> <span class="id"
type="var">H</span>.\
    <span class="id" type="var">aevalR\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>)
<span class="id" type="var">SCase</span>; <span class="id"
type="tactic">simpl</span>.\
    <span class="id" type="var">SCase</span> "E\_ANum".\
      <span class="id" type="tactic">reflexivity</span>.\
    <span class="id" type="var">SCase</span> "E\_APlus".\
      <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHaevalR1</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">IHaevalR2</span>. <span class="id"
type="tactic">reflexivity</span>.\
    <span class="id" type="var">SCase</span> "E\_AMinus".\
      <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHaevalR1</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">IHaevalR2</span>. <span class="id"
type="tactic">reflexivity</span>.\
    <span class="id" type="var">SCase</span> "E\_AMult".\
      <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHaevalR1</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">IHaevalR2</span>. <span class="id"
type="tactic">reflexivity</span>.\
  <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
    <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">n</span>.\
    <span class="id" type="var">aexp\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">a</span>)
<span class="id" type="var">SCase</span>;\
       <span class="id" type="tactic">simpl</span>; <span class="id"
type="tactic">intros</span>; <span class="id"
type="tactic">subst</span>.\
    <span class="id" type="var">SCase</span> "ANum".\
      <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_ANum</span>.\
    <span class="id" type="var">SCase</span> "APlus".\
      <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_APlus</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHa1</span>. <span class="id"
type="tactic">reflexivity</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHa2</span>. <span class="id"
type="tactic">reflexivity</span>.\
    <span class="id" type="var">SCase</span> "AMinus".\
      <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_AMinus</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHa1</span>. <span class="id"
type="tactic">reflexivity</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHa2</span>. <span class="id"
type="tactic">reflexivity</span>.\
    <span class="id" type="var">SCase</span> "AMult".\
      <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_AMult</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHa1</span>. <span class="id"
type="tactic">reflexivity</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHa2</span>. <span class="id"
type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Note: if you're reading the HTML file, you'll see an empty square box
instead of a proof for this theorem. You can click on this box to
"unfold" the text to see the proof. Click on the unfolded to text to
"fold" it back up to a box. We'll be using this style frequently from
now on to help keep the HTML easier to read. The full proofs always
appear in the .v files.
<div class="paragraph">

</div>

We can make the proof quite a bit shorter by making more use of
tacticals...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">aeval\_iff\_aevalR'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">a</span>
<span class="id" type="var">n</span>,\
   (<span class="id" type="var">a</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n</span>) <span style="font-family: arial;">↔</span> <span
class="id" type="var">aeval</span> <span class="id" type="var">a</span>
= <span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">split</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">→</span>".\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">induction</span>
<span class="id" type="var">H</span>; <span class="id"
type="tactic">subst</span>; <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "<span
style="font-family: arial;">←</span>".\
     <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">n</span>.\
     <span class="id" type="tactic">induction</span> <span class="id"
type="var">a</span>; <span class="id" type="tactic">simpl</span>; <span
class="id" type="tactic">intros</span>; <span class="id"
type="tactic">subst</span>; <span class="id"
type="var">constructor</span>;\
        <span class="id" type="tactic">try</span> <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHa1</span>;
<span class="id" type="tactic">try</span> <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHa2</span>;
<span class="id" type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars (bevalR) {.section}

Write a relation <span class="inlinecode"><span class="id"
type="var">bevalR</span></span> in the same style as <span
class="inlinecode"><span class="id" type="var">aevalR</span></span>, and
prove that it is equivalent to <span class="inlinecode"><span class="id"
type="var">beval</span></span>.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* \
 Inductive bevalR:\
 <span class="comment">(\* FILL IN HERE \*)</span>\
 \*)</span>\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Computational vs. Relational Definitions {.section}
----------------------------------------

<div class="paragraph">

</div>

For the definitions of evaluation for arithmetic and boolean
expressions, the choice of whether to use functional or relational
definitions is mainly a matter of taste. In general, Coq has somewhat
better support for working with relations. On the other hand, in some
sense function definitions carry more information, because functions are
necessarily deterministic and defined on all arguments; for a relation
we have to show these properties explicitly if we need them. Functions
also take advantage of Coq's computations mechanism.
<div class="paragraph">

</div>

However, there are circumstances where relational definitions of
evaluation are preferable to functional ones.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">aevalR\_division</span>.\
\

</div>

<div class="doc">

For example, suppose that we wanted to extend the arithmetic operations
by considering also a division operation:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">aexp</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">ANum</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span>\
   | <span class="id" type="var">APlus</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>\
   | <span class="id" type="var">AMinus</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>\
   | <span class="id" type="var">AMult</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>\
   | <span class="id" type="var">ADiv</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>. <span class="comment">(\* \<--- new \*)</span>\
\

</div>

<div class="doc">

Extending the definition of <span class="inlinecode"><span class="id"
type="var">aeval</span></span> to handle this new operation would not be
straightforward (what should we return as the result of <span
class="inlinecode"><span class="id" type="var">ADiv</span></span> <span
class="inlinecode">(<span class="id" type="var">ANum</span></span> <span
class="inlinecode">5)</span> <span class="inlinecode">(<span class="id"
type="var">ANum</span></span> <span class="inlinecode">0)</span>?). But
extending <span class="inlinecode"><span class="id"
type="var">aevalR</span></span> is straightforward.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">aevalR</span> : <span class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">E\_ANum</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>),\
       (<span class="id" type="var">ANum</span> <span class="id"
type="var">n</span>) <span style="font-family: arial;">⇓</span> <span
class="id" type="var">n</span>\
   | <span class="id" type="var">E\_APlus</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> : <span
class="id" type="var">nat</span>),\
       (<span class="id" type="var">a1</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n1</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">a2</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n2</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">APlus</span> <span class="id" type="var">a1</span>
<span class="id" type="var">a2</span>) <span
style="font-family: arial;">⇓</span> (<span class="id"
type="var">n1</span> + <span class="id" type="var">n2</span>)\
   | <span class="id" type="var">E\_AMinus</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> : <span
class="id" type="var">nat</span>),\
       (<span class="id" type="var">a1</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n1</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">a2</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n2</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">AMinus</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>) <span
style="font-family: arial;">⇓</span> (<span class="id"
type="var">n1</span> - <span class="id" type="var">n2</span>)\
   | <span class="id" type="var">E\_AMult</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> : <span
class="id" type="var">nat</span>),\
       (<span class="id" type="var">a1</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n1</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">a2</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n2</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">AMult</span> <span class="id" type="var">a1</span>
<span class="id" type="var">a2</span>) <span
style="font-family: arial;">⇓</span> (<span class="id"
type="var">n1</span> × <span class="id" type="var">n2</span>)\
   | <span class="id" type="var">E\_ADiv</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> <span
class="id" type="var">n3</span>: <span class="id"
type="var">nat</span>),\
       (<span class="id" type="var">a1</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n1</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">a2</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n2</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">mult</span> <span class="id" type="var">n2</span>
<span class="id" type="var">n3</span> = <span class="id"
type="var">n1</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">ADiv</span> <span class="id" type="var">a1</span>
<span class="id" type="var">a2</span>) <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n3</span>\
\
 <span class="id" type="keyword">where</span> "a '<span
style="font-family: arial;">⇓</span>' n" := (<span class="id"
type="var">aevalR</span> <span class="id" type="var">a</span> <span
class="id" type="var">n</span>) : <span class="id"
type="var">type\_scope</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">aevalR\_division</span>.\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">aevalR\_extended</span>.\
\

</div>

<div class="doc">

Suppose, instead, that we want to extend the arithmetic operations by a
nondeterministic number generator <span class="inlinecode"><span
class="id" type="var">any</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">aexp</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">AAny</span> : <span class="id"
type="var">aexp</span> <span class="comment">(\* \<--- NEW \*)</span>\
   | <span class="id" type="var">ANum</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span>\
   | <span class="id" type="var">APlus</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>\
   | <span class="id" type="var">AMinus</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>\
   | <span class="id" type="var">AMult</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>.\
\

</div>

<div class="doc">

Again, extending <span class="inlinecode"><span class="id"
type="var">aeval</span></span> would be tricky (because evaluation is
*not* a deterministic function from expressions to numbers), but
extending <span class="inlinecode"><span class="id"
type="var">aevalR</span></span> is no problem:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">aevalR</span> : <span class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">E\_Any</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>),\
       <span class="id" type="var">AAny</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n</span> <span class="comment">(\* \<--- new \*)</span>\
   | <span class="id" type="var">E\_ANum</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>),\
       (<span class="id" type="var">ANum</span> <span class="id"
type="var">n</span>) <span style="font-family: arial;">⇓</span> <span
class="id" type="var">n</span>\
   | <span class="id" type="var">E\_APlus</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> : <span
class="id" type="var">nat</span>),\
       (<span class="id" type="var">a1</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n1</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">a2</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n2</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">APlus</span> <span class="id" type="var">a1</span>
<span class="id" type="var">a2</span>) <span
style="font-family: arial;">⇓</span> (<span class="id"
type="var">n1</span> + <span class="id" type="var">n2</span>)\
   | <span class="id" type="var">E\_AMinus</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> : <span
class="id" type="var">nat</span>),\
       (<span class="id" type="var">a1</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n1</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">a2</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n2</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">AMinus</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>) <span
style="font-family: arial;">⇓</span> (<span class="id"
type="var">n1</span> - <span class="id" type="var">n2</span>)\
   | <span class="id" type="var">E\_AMult</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>: <span
class="id" type="var">aexp</span>) (<span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> : <span
class="id" type="var">nat</span>),\
       (<span class="id" type="var">a1</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n1</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">a2</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n2</span>) <span style="font-family: arial;">→</span> (<span
class="id" type="var">AMult</span> <span class="id" type="var">a1</span>
<span class="id" type="var">a2</span>) <span
style="font-family: arial;">⇓</span> (<span class="id"
type="var">n1</span> × <span class="id" type="var">n2</span>)\
\
 <span class="id" type="keyword">where</span> "a '<span
style="font-family: arial;">⇓</span>' n" := (<span class="id"
type="var">aevalR</span> <span class="id" type="var">a</span> <span
class="id" type="var">n</span>) : <span class="id"
type="var">type\_scope</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">aevalR\_extended</span>.\
\

</div>

<div class="doc">

Expressions With Variables {.section}
==========================

<div class="paragraph">

</div>

Let's turn our attention back to defining Imp. The next thing we need to
do is to enrich our arithmetic and boolean expressions with variables.
To keep things simple, we'll assume that all variables are global and
that they only hold numbers.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Identifiers {.section}
-----------

<div class="paragraph">

</div>

To begin, we'll need to formalize *identifiers* such as program
variables. We could use strings for this — or, in a real compiler,
fancier structures like pointers into a symbol table. But for simplicity
let's just use natural numbers as identifiers.
<div class="paragraph">

</div>

(We hide this section in a module because these definitions are actually
in <span class="inlinecode"><span class="id"
type="var">SfLib</span></span>, but we want to repeat them here so that
we can explain them.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Id</span>.\
\

</div>

<div class="doc">

We define a new inductive datatype <span class="inlinecode"><span
class="id" type="var">Id</span></span> so that we won't confuse
identifiers and numbers. We use <span class="inlinecode"><span
class="id" type="var">sumbool</span></span> to define a computable
equality operator on <span class="inlinecode"><span class="id"
type="var">Id</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">id</span> : <span class="id" type="keyword">Type</span> :=\
   <span class="id" type="var">Id</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">id</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">eq\_id\_dec</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">id1</span> <span class="id" type="var">id2</span> : <span
class="id" type="var">id</span>, {<span class="id" type="var">id1</span>
= <span class="id" type="var">id2</span>} + {<span class="id"
type="var">id1</span> ≠ <span class="id" type="var">id2</span>}.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">intros</span> <span class="id"
type="var">id1</span> <span class="id" type="var">id2</span>.\
    <span class="id" type="tactic">destruct</span> <span class="id"
type="var">id1</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">n1</span>]. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">id2</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">n2</span>].\
    <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_nat\_dec</span> <span class="id" type="var">n1</span>
<span class="id" type="var">n2</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">Heq</span> | <span
class="id" type="var">Hneq</span>].\
    <span class="id" type="var">Case</span> "n1 = n2".\
      <span class="id" type="var">left</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">Heq</span>.
<span class="id" type="tactic">reflexivity</span>.\
    <span class="id" type="var">Case</span> "n1 ≠ n2".\
      <span class="id" type="var">right</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">contra</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">contra</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">Hneq</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H0</span>.\
 <span class="id" type="keyword">Defined</span>.\
\

</div>

<div class="doc">

The following lemmas will be useful for rewriting terms involving <span
class="inlinecode"><span class="id"
type="var">eq\_id\_dec</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">eq\_id</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">T</span>:<span class="id" type="keyword">Type</span>) <span
class="id" type="var">x</span> (<span class="id" type="var">p</span>
<span class="id" type="var">q</span>:<span class="id"
type="var">T</span>),\
               (<span class="id" type="keyword">if</span> <span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">x</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">p</span> <span class="id" type="keyword">else</span> <span
class="id" type="var">q</span>) = <span class="id" type="var">p</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x</span>).\
   <span class="id" type="var">Case</span> "x = x".\
     <span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "x ≠ x (impossible)".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ex\_falso\_quodlibet</span>; <span class="id"
type="tactic">apply</span> <span class="id" type="var">n</span>; <span
class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star, optional (neq\_id) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">neq\_id</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">T</span>:<span class="id" type="keyword">Type</span>) <span
class="id" type="var">x</span> <span class="id" type="var">y</span>
(<span class="id" type="var">p</span> <span class="id"
type="var">q</span>:<span class="id" type="var">T</span>), <span
class="id" type="var">x</span> ≠ <span class="id" type="var">y</span>
<span style="font-family: arial;">→</span>\
                (<span class="id" type="keyword">if</span> <span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">p</span> <span class="id" type="keyword">else</span> <span
class="id" type="var">q</span>) = <span class="id" type="var">q</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Id</span>.\
\

</div>

<div class="doc">

States {.section}
------

<div class="paragraph">

</div>

A *state* represents the current values of *all* the variables at some
point in the execution of a program. For simplicity (to avoid dealing
with partial functions), we let the state be defined for *all*
variables, even though any given program is only going to mention a
finite number of them. The state captures all of the information stored
in memory. For Imp programs, because each variable stores only a natural
number, we can represent the state as a mapping from identifiers to
<span class="inlinecode"><span class="id" type="var">nat</span></span>.
For more complex programming languages, the state might have more
structure.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">state</span> := <span class="id" type="var">id</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">empty\_state</span> : <span class="id"
type="var">state</span> :=\
   <span class="id" type="keyword">fun</span> <span class="id"
type="var">\_</span> ⇒ 0.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">update</span> (<span class="id" type="var">st</span> : <span
class="id" type="var">state</span>) (<span class="id"
type="var">x</span> : <span class="id" type="var">id</span>) (<span
class="id" type="var">n</span> : <span class="id" type="var">nat</span>)
: <span class="id" type="var">state</span> :=\
   <span class="id" type="keyword">fun</span> <span class="id"
type="var">x'</span> ⇒ <span class="id" type="keyword">if</span> <span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">x'</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">n</span> <span class="id" type="keyword">else</span> <span
class="id" type="var">st</span> <span class="id" type="var">x'</span>.\
\

</div>

<div class="doc">

For proofs involving states, we'll need several simple properties of
<span class="inlinecode"><span class="id"
type="var">update</span></span>.
<div class="paragraph">

</div>

#### Exercise: 1 star (update\_eq) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">update\_eq</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">x</span> <span class="id"
type="var">st</span>,\
   (<span class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">x</span> <span
class="id" type="var">n</span>) <span class="id" type="var">x</span> =
<span class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star (update\_neq) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">update\_neq</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x2</span> <span class="id" type="var">x1</span> <span
class="id" type="var">n</span> <span class="id" type="var">st</span>,\
   <span class="id" type="var">x2</span> ≠ <span class="id"
type="var">x1</span> <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">x2</span> <span
class="id" type="var">n</span>) <span class="id" type="var">x1</span> =
(<span class="id" type="var">st</span> <span class="id"
type="var">x1</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star (update\_example) {.section}

Before starting to play with tactics, make sure you understand exactly
what the theorem is saying!

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">update\_example</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>),\
   (<span class="id" type="var">update</span> <span class="id"
type="var">empty\_state</span> (<span class="id" type="var">Id</span> 2)
<span class="id" type="var">n</span>) (<span class="id"
type="var">Id</span> 3) = 0.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star (update\_shadow) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">update\_shadow</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> <span
class="id" type="var">x1</span> <span class="id" type="var">x2</span>
(<span class="id" type="var">st</span> : <span class="id"
type="var">state</span>),\
    (<span class="id" type="var">update</span> (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">x2</span> <span class="id" type="var">n1</span>)
<span class="id" type="var">x2</span> <span class="id"
type="var">n2</span>) <span class="id" type="var">x1</span> = (<span
class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">x2</span> <span
class="id" type="var">n2</span>) <span class="id" type="var">x1</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (update\_same) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">update\_same</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">x1</span> <span
class="id" type="var">x2</span> (<span class="id" type="var">st</span> :
<span class="id" type="var">state</span>),\
   <span class="id" type="var">st</span> <span class="id"
type="var">x1</span> = <span class="id" type="var">n1</span> <span
style="font-family: arial;">→</span>\
   (<span class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">x1</span> <span
class="id" type="var">n1</span>) <span class="id" type="var">x2</span> =
<span class="id" type="var">st</span> <span class="id"
type="var">x2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (update\_permute) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">update\_permute</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> <span
class="id" type="var">x1</span> <span class="id" type="var">x2</span>
<span class="id" type="var">x3</span> <span class="id"
type="var">st</span>,\
   <span class="id" type="var">x2</span> ≠ <span class="id"
type="var">x1</span> <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">update</span> (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">x2</span> <span class="id" type="var">n1</span>)
<span class="id" type="var">x1</span> <span class="id"
type="var">n2</span>) <span class="id" type="var">x3</span> = (<span
class="id" type="var">update</span> (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">x1</span> <span class="id" type="var">n2</span>)
<span class="id" type="var">x2</span> <span class="id"
type="var">n1</span>) <span class="id" type="var">x3</span>.\
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

Syntax {.section}
------

<div class="paragraph">

</div>

We can add variables to the arithmetic expressions we had before by
simply adding one more constructor:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">aexp</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">ANum</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span>\
   | <span class="id" type="var">AId</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
class="comment">(\* \<----- NEW \*)</span>\
   | <span class="id" type="var">APlus</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>\
   | <span class="id" type="var">AMinus</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>\
   | <span class="id" type="var">AMult</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span> "aexp\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ANum" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "AId" |
<span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "APlus"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "AMinus" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "AMult"
].\
\

</div>

<div class="doc">

Defining a few variable names as notational shorthands will make
examples easier to read:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">X</span> : <span class="id" type="var">id</span> := <span
class="id" type="var">Id</span> 0.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">Y</span> : <span class="id" type="var">id</span> := <span
class="id" type="var">Id</span> 1.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">Z</span> : <span class="id" type="var">id</span> := <span
class="id" type="var">Id</span> 2.\
\

</div>

<div class="doc">

(This convention for naming program variables (<span
class="inlinecode"><span class="id" type="var">X</span></span>, <span
class="inlinecode"><span class="id" type="var">Y</span></span>, <span
class="inlinecode"><span class="id" type="var">Z</span></span>) clashes
a bit with our earlier use of uppercase letters for types. Since we're
not using polymorphism heavily in this part of the course, this
overloading should not cause confusion.)
<div class="paragraph">

</div>

The definition of <span class="inlinecode"><span class="id"
type="var">bexp</span></span>s is the same as before (using the new
<span class="inlinecode"><span class="id"
type="var">aexp</span></span>s):

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">bexp</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">BTrue</span> : <span class="id"
type="var">bexp</span>\
   | <span class="id" type="var">BFalse</span> : <span class="id"
type="var">bexp</span>\
   | <span class="id" type="var">BEq</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bexp</span>\
   | <span class="id" type="var">BLe</span> : <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bexp</span>\
   | <span class="id" type="var">BNot</span> : <span class="id"
type="var">bexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">bexp</span>\
   | <span class="id" type="var">BAnd</span> : <span class="id"
type="var">bexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">bexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bexp</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span> "bexp\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "BTrue" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"BFalse" | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "BEq"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "BLe" | <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">c</span> "BNot" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "BAnd"
].\
\

</div>

<div class="doc">

Evaluation {.section}
----------

<div class="paragraph">

</div>

The arith and boolean evaluators can be extended to handle variables in
the obvious way:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">aeval</span> (<span class="id" type="var">st</span> : <span
class="id" type="var">state</span>) (<span class="id"
type="var">a</span> : <span class="id" type="var">aexp</span>) : <span
class="id" type="var">nat</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">a</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">ANum</span> <span class="id"
type="var">n</span> ⇒ <span class="id" type="var">n</span>\
   | <span class="id" type="var">AId</span> <span class="id"
type="var">x</span> ⇒ <span class="id" type="var">st</span> <span
class="id" type="var">x</span> <span
class="comment">(\* \<----- NEW \*)</span>\
   | <span class="id" type="var">APlus</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ (<span
class="id" type="var">aeval</span> <span class="id" type="var">st</span>
<span class="id" type="var">a1</span>) + (<span class="id"
type="var">aeval</span> <span class="id" type="var">st</span> <span
class="id" type="var">a2</span>)\
   | <span class="id" type="var">AMinus</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ (<span
class="id" type="var">aeval</span> <span class="id" type="var">st</span>
<span class="id" type="var">a1</span>) - (<span class="id"
type="var">aeval</span> <span class="id" type="var">st</span> <span
class="id" type="var">a2</span>)\
   | <span class="id" type="var">AMult</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ (<span
class="id" type="var">aeval</span> <span class="id" type="var">st</span>
<span class="id" type="var">a1</span>) × (<span class="id"
type="var">aeval</span> <span class="id" type="var">st</span> <span
class="id" type="var">a2</span>)\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">beval</span> (<span class="id" type="var">st</span> : <span
class="id" type="var">state</span>) (<span class="id"
type="var">b</span> : <span class="id" type="var">bexp</span>) : <span
class="id" type="var">bool</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">b</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">BTrue</span> ⇒ <span class="id"
type="var">true</span>\
   | <span class="id" type="var">BFalse</span> ⇒ <span class="id"
type="var">false</span>\
   | <span class="id" type="var">BEq</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ <span
class="id" type="var">beq\_nat</span> (<span class="id"
type="var">aeval</span> <span class="id" type="var">st</span> <span
class="id" type="var">a1</span>) (<span class="id"
type="var">aeval</span> <span class="id" type="var">st</span> <span
class="id" type="var">a2</span>)\
   | <span class="id" type="var">BLe</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ <span
class="id" type="var">ble\_nat</span> (<span class="id"
type="var">aeval</span> <span class="id" type="var">st</span> <span
class="id" type="var">a1</span>) (<span class="id"
type="var">aeval</span> <span class="id" type="var">st</span> <span
class="id" type="var">a2</span>)\
   | <span class="id" type="var">BNot</span> <span class="id"
type="var">b1</span> ⇒ <span class="id" type="var">negb</span> (<span
class="id" type="var">beval</span> <span class="id" type="var">st</span>
<span class="id" type="var">b1</span>)\
   | <span class="id" type="var">BAnd</span> <span class="id"
type="var">b1</span> <span class="id" type="var">b2</span> ⇒ <span
class="id" type="var">andb</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b1</span>) (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b2</span>)\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">aexp1</span> :\
   <span class="id" type="var">aeval</span> (<span class="id"
type="var">update</span> <span class="id" type="var">empty\_state</span>
<span class="id" type="var">X</span> 5)\
         (<span class="id" type="var">APlus</span> (<span class="id"
type="var">ANum</span> 3) (<span class="id" type="var">AMult</span>
(<span class="id" type="var">AId</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">ANum</span> 2)))\
   = 13.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">bexp1</span> :\
   <span class="id" type="var">beval</span> (<span class="id"
type="var">update</span> <span class="id" type="var">empty\_state</span>
<span class="id" type="var">X</span> 5)\
         (<span class="id" type="var">BAnd</span> <span class="id"
type="var">BTrue</span> (<span class="id" type="var">BNot</span> (<span
class="id" type="var">BLe</span> (<span class="id" type="var">AId</span>
<span class="id" type="var">X</span>) (<span class="id"
type="var">ANum</span> 4))))\
   = <span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Commands {.section}
========

<div class="paragraph">

</div>

Now we are ready define the syntax and behavior of Imp *commands* (often
called *statements*).

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Syntax {.section}
------

<div class="paragraph">

</div>

Informally, commands <span class="inlinecode"><span class="id"
type="var">c</span></span> are described by the following BNF grammar:
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">c</span> ::= <span class="id"
type="var">SKIP</span>\
          | <span class="id" type="var">x</span> ::= <span class="id"
type="var">a</span>\
          | <span class="id" type="var">c</span> ;; <span class="id"
type="var">c</span>\
          | <span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span>\
          | <span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c</span> <span class="id"
type="var">ELSE</span> <span class="id" type="var">c</span> <span
class="id" type="var">FI</span>
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

For example, here's the factorial function in Imp.
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">Z</span> ::= <span class="id"
type="var">X</span>;;\
      <span class="id" type="var">Y</span> ::= 1;;\
      <span class="id" type="var">WHILE</span> <span class="id"
type="var">not</span> (<span class="id" type="var">Z</span> = 0) <span
class="id" type="var">DO</span>\
        <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> × <span class="id" type="var">Z</span>;;\
        <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span> - 1\
      <span class="id" type="var">END</span>
<div class="paragraph">

</div>

</div>

When this command terminates, the variable <span
class="inlinecode"><span class="id" type="var">Y</span></span> will
contain the factorial of the initial value of <span
class="inlinecode"><span class="id" type="var">X</span></span>.
<div class="paragraph">

</div>

Here is the formal definition of the syntax of commands:

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
type="var">com</span>.\
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
<span class="id" type="var">c</span> "WHILE" ].\
\

</div>

<div class="doc">

As usual, we can use a few <span class="inlinecode"><span class="id"
type="keyword">Notation</span></span> declarations to make things more
readable. We need to be a bit careful to avoid conflicts with Coq's
built-in notations, so we'll keep this light — in particular, we won't
introduce any notations for <span class="inlinecode"><span class="id"
type="var">aexps</span></span> and <span class="inlinecode"><span
class="id" type="var">bexps</span></span> to avoid confusion with the
numerical and boolean operators we've already defined. We use the
keyword <span class="inlinecode"><span class="id"
type="var">IFB</span></span> for conditionals instead of <span
class="inlinecode"><span class="id" type="var">IF</span></span>, for
similar reasons.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "'SKIP'" :=\
   <span class="id" type="var">CSkip</span>.\
 <span class="id" type="keyword">Notation</span> "x '::=' a" :=\
   (<span class="id" type="var">CAss</span> <span class="id"
type="var">x</span> <span class="id" type="var">a</span>) (<span
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
 <span class="id" type="keyword">Notation</span> "'IFB' c1 'THEN' c2
'ELSE' c3 'FI'" :=\
   (<span class="id" type="var">CIf</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c2</span> <span
class="id" type="var">c3</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 80,
<span class="id" type="var">right</span> <span class="id"
type="var">associativity</span>).\
\

</div>

<div class="doc">

For example, here is the factorial function again, written as a formal
definition to Coq:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">fact\_in\_coq</span> : <span class="id" type="var">com</span>
:=\
   <span class="id" type="var">Z</span> ::= <span class="id"
type="var">AId</span> <span class="id" type="var">X</span>;;\
   <span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 1;;\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">Z</span>)
(<span class="id" type="var">ANum</span> 0)) <span class="id"
type="var">DO</span>\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">AMult</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">Y</span>) (<span class="id" type="var">AId</span>
<span class="id" type="var">Z</span>);;\
     <span class="id" type="var">Z</span> ::= <span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">Z</span>) (<span class="id" type="var">ANum</span>
1)\
   <span class="id" type="var">END</span>.\
\

</div>

<div class="doc">

Examples {.section}
--------

<div class="paragraph">

</div>

Assignment:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">plus2</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">X</span> ::= (<span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
2)).\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">XtimesYinZ</span> : <span class="id" type="var">com</span>
:=\
   <span class="id" type="var">Z</span> ::= (<span class="id"
type="var">AMult</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">AId</span>
<span class="id" type="var">Y</span>)).\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">subtract\_slowly\_body</span> : <span class="id"
type="var">com</span> :=\
   <span class="id" type="var">Z</span> ::= <span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">Z</span>) (<span class="id" type="var">ANum</span>
1) ;;\
   <span class="id" type="var">X</span> ::= <span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1).\
\

</div>

<div class="doc">

### Loops {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">subtract\_slowly</span> : <span class="id"
type="var">com</span> :=\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 0)) <span class="id"
type="var">DO</span>\
     <span class="id" type="var">subtract\_slowly\_body</span>\
   <span class="id" type="var">END</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">subtract\_3\_from\_5\_slowly</span> : <span class="id"
type="var">com</span> :=\
   <span class="id" type="var">X</span> ::= <span class="id"
type="var">ANum</span> 3 ;;\
   <span class="id" type="var">Z</span> ::= <span class="id"
type="var">ANum</span> 5 ;;\
   <span class="id" type="var">subtract\_slowly</span>.\
\

</div>

<div class="doc">

### An infinite loop: {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">loop</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">BTrue</span> <span class="id" type="var">DO</span>\
     <span class="id" type="var">SKIP</span>\
   <span class="id" type="var">END</span>.\
\

</div>

<div class="doc">

Evaluation {.section}
==========

<div class="paragraph">

</div>

Next we need to define what it means to evaluate an Imp command. The
fact that <span class="inlinecode"><span class="id"
type="var">WHILE</span></span> loops don't necessarily terminate makes
defining an evaluation function tricky...

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Evaluation as a Function (Failed Attempt) {.section}
-----------------------------------------

<div class="paragraph">

</div>

Here's an attempt at defining an evaluation function for commands,
omitting the <span class="inlinecode"><span class="id"
type="var">WHILE</span></span> case.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">ceval\_fun\_no\_while</span> (<span class="id"
type="var">st</span> : <span class="id" type="var">state</span>) (<span
class="id" type="var">c</span> : <span class="id" type="var">com</span>)
: <span class="id" type="var">state</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">c</span> <span class="id" type="keyword">with</span>\
     | <span class="id" type="var">SKIP</span> ⇒\
         <span class="id" type="var">st</span>\
     | <span class="id" type="var">x</span> ::= <span class="id"
type="var">a1</span> ⇒\
         <span class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">x</span> (<span
class="id" type="var">aeval</span> <span class="id" type="var">st</span>
<span class="id" type="var">a1</span>)\
     | <span class="id" type="var">c1</span> ;; <span class="id"
type="var">c2</span> ⇒\
         <span class="id" type="keyword">let</span> <span class="id"
type="var">st'</span> := <span class="id"
type="var">ceval\_fun\_no\_while</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="keyword">in</span>\
         <span class="id" type="var">ceval\_fun\_no\_while</span> <span
class="id" type="var">st'</span> <span class="id" type="var">c2</span>\
     | <span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span> ⇒\
         <span class="id" type="keyword">if</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b</span>)\
           <span class="id" type="keyword">then</span> <span class="id"
type="var">ceval\_fun\_no\_while</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span>\
           <span class="id" type="keyword">else</span> <span class="id"
type="var">ceval\_fun\_no\_while</span> <span class="id"
type="var">st</span> <span class="id" type="var">c2</span>\
     | <span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span> ⇒\
         <span class="id" type="var">st</span> <span
class="comment">(\* bogus \*)</span>\
   <span class="id" type="keyword">end</span>.\

</div>

<div class="doc">

In a traditional functional programming language like ML or Haskell we
could write the <span class="inlinecode"><span class="id"
type="var">WHILE</span></span> case as follows:
      Fixpoint ceval_fun (st : state) (c : com) : state :=
        match c with
          ...
          | WHILE b DO c END =>
              if (beval st b1)
                then ceval_fun st (c1; WHILE b DO c END)
                else st
        end.

Coq doesn't accept such a definition ("Error: Cannot guess decreasing
argument of fix") because the function we want to define is not
guaranteed to terminate. Indeed, it doesn't always terminate: for
example, the full version of the <span class="inlinecode"><span
class="id" type="var">ceval\_fun</span></span> function applied to the
<span class="inlinecode"><span class="id" type="var">loop</span></span>
program above would never terminate. Since Coq is not just a functional
programming language, but also a consistent logic, any potentially
non-terminating function needs to be rejected. Here is an (invalid!) Coq
program showing what would go wrong if Coq allowed non-terminating
recursive functions:
         Fixpoint loop_false (n : nat) : False := loop_false n.

That is, propositions like <span class="inlinecode"><span class="id"
type="var">False</span></span> would become provable (e.g. <span
class="inlinecode"><span class="id" type="var">loop\_false</span></span>
<span class="inlinecode">0</span> would be a proof of <span
class="inlinecode"><span class="id" type="var">False</span></span>),
which would be a disaster for Coq's logical consistency.
<div class="paragraph">

</div>

Thus, because it doesn't terminate on all inputs, the full version of
<span class="inlinecode"><span class="id"
type="var">ceval\_fun</span></span> cannot be written in Coq — at least
not without additional tricks (see chapter <span
class="inlinecode"><span class="id" type="var">ImpCEvalFun</span></span>
if curious).

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Evaluation as a Relation {.section}
------------------------

<div class="paragraph">

</div>

Here's a better way: we define <span class="inlinecode"><span class="id"
type="var">ceval</span></span> as a *relation* rather than a *function*
— i.e., we define it in <span class="inlinecode"><span class="id"
type="keyword">Prop</span></span> instead of <span
class="inlinecode"><span class="id" type="keyword">Type</span></span>,
as we did for <span class="inlinecode"><span class="id"
type="var">aevalR</span></span> above.
<div class="paragraph">

</div>

This is an important change. Besides freeing us from the awkward
workarounds that would be needed to define evaluation as a function, it
gives us a lot more flexibility in the definition. For example, if we
added concurrency features to the language, we'd want the definition of
evaluation to be non-deterministic — i.e., not only would it not be
total, it would not even be a partial function! We'll use the notation
<span class="inlinecode"><span class="id" type="var">c</span></span>
<span class="inlinecode">/</span> <span class="inlinecode"><span
class="id" type="var">st</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇓</span></span> <span
class="inlinecode"><span class="id" type="var">st'</span></span> for our
<span class="inlinecode"><span class="id" type="var">ceval</span></span>
relation: <span class="inlinecode"><span class="id"
type="var">c</span></span> <span class="inlinecode">/</span> <span
class="inlinecode"><span class="id" type="var">st</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇓</span></span>
<span class="inlinecode"><span class="id" type="var">st'</span></span>
means that executing program <span class="inlinecode"><span class="id"
type="var">c</span></span> in a starting state <span
class="inlinecode"><span class="id" type="var">st</span></span> results
in an ending state <span class="inlinecode"><span class="id"
type="var">st'</span></span>. This can be pronounced "<span
class="inlinecode"><span class="id" type="var">c</span></span> takes
state <span class="inlinecode"><span class="id"
type="var">st</span></span> to <span class="inlinecode"><span class="id"
type="var">st'</span></span>".
<div class="paragraph">

</div>

### Operational Semantics {.section}

  
(E\_Skip)  

------------------------------------------------------------------------

SKIP / st <span style="font-family: arial;">⇓</span> st
aeval st a1 = n
(E\_Ass)  

------------------------------------------------------------------------

x := a1 / st <span style="font-family: arial;">⇓</span> (update st x n)
c1 / st <span style="font-family: arial;">⇓</span> st'
c2 / st' <span style="font-family: arial;">⇓</span> st''
(E\_Seq)  

------------------------------------------------------------------------

c1;;c2 / st <span style="font-family: arial;">⇓</span> st''
beval st b1 = true
c1 / st <span style="font-family: arial;">⇓</span> st'
(E\_IfTrue)  

------------------------------------------------------------------------

IF b1 THEN c1 ELSE c2 FI / st <span
style="font-family: arial;">⇓</span> st'
beval st b1 = false
c2 / st <span style="font-family: arial;">⇓</span> st'
(E\_IfFalse)  

------------------------------------------------------------------------

IF b1 THEN c1 ELSE c2 FI / st <span
style="font-family: arial;">⇓</span> st'
beval st b1 = false
(E\_WhileEnd)  

------------------------------------------------------------------------

WHILE b DO c END / st <span style="font-family: arial;">⇓</span> st
beval st b1 = true
c / st <span style="font-family: arial;">⇓</span> st'
WHILE b DO c END / st' <span style="font-family: arial;">⇓</span> st''
(E\_WhileLoop)  

------------------------------------------------------------------------

WHILE b DO c END / st <span style="font-family: arial;">⇓</span> st''
<div class="paragraph">

</div>

Here is the formal definition. (Make sure you understand how it
corresponds to the inference rules.)

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
type="var">st</span>,\
       <span class="id" type="var">SKIP</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st</span>\
   | <span class="id" type="var">E\_Ass</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">a1</span> <span
class="id" type="var">n</span> <span class="id" type="var">x</span>,\
       <span class="id" type="var">aeval</span> <span class="id"
type="var">st</span> <span class="id" type="var">a1</span> = <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span>\
       (<span class="id" type="var">x</span> ::= <span class="id"
type="var">a1</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">x</span> <span class="id" type="var">n</span>)\
   | <span class="id" type="var">E\_Seq</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">c1</span> <span class="id" type="var">c2</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>
<span class="id" type="var">st''</span>,\
       <span class="id" type="var">c1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">c2</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st''</span> <span
style="font-family: arial;">→</span>\
       (<span class="id" type="var">c1</span> ;; <span class="id"
type="var">c2</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st''</span>\
   | <span class="id" type="var">E\_IfTrue</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">b</span> <span class="id" type="var">c1</span>
<span class="id" type="var">c2</span>,\
       <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">c1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
       (<span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span>\
   | <span class="id" type="var">E\_IfFalse</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">b</span> <span class="id" type="var">c1</span>
<span class="id" type="var">c2</span>,\
       <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">c2</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
       (<span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span>\
   | <span class="id" type="var">E\_WhileEnd</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">st</span> <span class="id"
type="var">c</span>,\
       <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span>\
       (<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span>) /
<span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st</span>\
   | <span class="id" type="var">E\_WhileLoop</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">st''</span> <span class="id" type="var">b</span>
<span class="id" type="var">c</span>,\
       <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
       (<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span>) /
<span class="id" type="var">st'</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st''</span> <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span>) /
<span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">st''</span>\
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
"E\_WhileLoop" ].\
\

</div>

<div class="doc">

###  {.section}

The cost of defining evaluation as a relation instead of a function is
that we now need to construct *proofs* that some program evaluates to
some result state, rather than just letting Coq's computation mechanism
do it for us.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">ceval\_example1</span>:\
     (<span class="id" type="var">X</span> ::= <span class="id"
type="var">ANum</span> 2;;\
      <span class="id" type="var">IFB</span> <span class="id"
type="var">BLe</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1)\
        <span class="id" type="var">THEN</span> <span class="id"
type="var">Y</span> ::= <span class="id" type="var">ANum</span> 3\
        <span class="id" type="var">ELSE</span> <span class="id"
type="var">Z</span> ::= <span class="id" type="var">ANum</span> 4\
      <span class="id" type="var">FI</span>)\
    / <span class="id" type="var">empty\_state</span>\
    <span style="font-family: arial;">⇓</span> (<span class="id"
type="var">update</span> (<span class="id" type="var">update</span>
<span class="id" type="var">empty\_state</span> <span class="id"
type="var">X</span> 2) <span class="id" type="var">Z</span> 4).\
 <span class="id" type="keyword">Proof</span>.\
   <span
class="comment">(\* We must supply the intermediate state \*)</span>\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Seq</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">update</span> <span class="id"
type="var">empty\_state</span> <span class="id" type="var">X</span> 2).\
   <span class="id" type="var">Case</span> "assignment command".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Ass</span>. <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "if command".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_IfFalse</span>.\
       <span class="id" type="tactic">reflexivity</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Ass</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (ceval\_example2) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">ceval\_example2</span>:\
     (<span class="id" type="var">X</span> ::= <span class="id"
type="var">ANum</span> 0;; <span class="id" type="var">Y</span> ::=
<span class="id" type="var">ANum</span> 1;; <span class="id"
type="var">Z</span> ::= <span class="id" type="var">ANum</span> 2) /
<span class="id" type="var">empty\_state</span> <span
style="font-family: arial;">⇓</span>\
     (<span class="id" type="var">update</span> (<span class="id"
type="var">update</span> (<span class="id" type="var">update</span>
<span class="id" type="var">empty\_state</span> <span class="id"
type="var">X</span> 0) <span class="id" type="var">Y</span> 1) <span
class="id" type="var">Z</span> 2).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (pup\_to\_n) {.section}

Write an Imp program that sums the numbers from <span
class="inlinecode">1</span> to <span class="inlinecode"><span class="id"
type="var">X</span></span> (inclusive: <span class="inlinecode">1</span>
<span class="inlinecode">+</span> <span class="inlinecode">2</span>
<span class="inlinecode">+</span> <span class="inlinecode">...</span>
<span class="inlinecode">+</span> <span class="inlinecode"><span
class="id" type="var">X</span></span>) in the variable <span
class="inlinecode"><span class="id" type="var">Y</span></span>. Prove
that this program executes as intended for X = 2 (this latter part is
trickier than you might expect).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">pup\_to\_n</span> : <span class="id" type="var">com</span>
:=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">pup\_to\_2\_ceval</span> :\
   <span class="id" type="var">pup\_to\_n</span> / (<span class="id"
type="var">update</span> <span class="id" type="var">empty\_state</span>
<span class="id" type="var">X</span> 2) <span
style="font-family: arial;">⇓</span>\
     <span class="id" type="var">update</span> (<span class="id"
type="var">update</span> (<span class="id" type="var">update</span>
(<span class="id" type="var">update</span> (<span class="id"
type="var">update</span> (<span class="id" type="var">update</span>
<span class="id" type="var">empty\_state</span>\
       <span class="id" type="var">X</span> 2) <span class="id"
type="var">Y</span> 0) <span class="id" type="var">Y</span> 2) <span
class="id" type="var">X</span> 1) <span class="id" type="var">Y</span>
3) <span class="id" type="var">X</span> 0.\
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

Determinism of Evaluation {.section}
-------------------------

<div class="paragraph">

</div>

Changing from a computational to a relational definition of evaluation
is a good move because it allows us to escape from the artificial
requirement (imposed by Coq's restrictions on <span
class="inlinecode"><span class="id"
type="keyword">Fixpoint</span></span> definitions) that evaluation
should be a total function. But it also raises a question: Is the second
definition of evaluation actually a partial function? That is, is it
possible that, beginning from the same state <span
class="inlinecode"><span class="id" type="var">st</span></span>, we
could evaluate some command <span class="inlinecode"><span class="id"
type="var">c</span></span> in different ways to reach two different
output states <span class="inlinecode"><span class="id"
type="var">st'</span></span> and <span class="inlinecode"><span
class="id" type="var">st''</span></span>?
<div class="paragraph">

</div>

In fact, this cannot happen: <span class="inlinecode"><span class="id"
type="var">ceval</span></span> is a partial function. Here's the proof:

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
<div id="proofcontrol2" class="togglescript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')">

<span class="show"></span>

</div>

<div id="proof2" class="proofscript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st1</span> <span class="id" type="var">st2</span>
<span class="id" type="var">E1</span> <span class="id"
type="var">E2</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st2</span>.\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">E1</span>)
<span class="id" type="var">Case</span>;\
            <span class="id" type="tactic">intros</span> <span
class="id" type="var">st2</span> <span class="id" type="var">E2</span>;
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">E2</span>; <span class="id" type="tactic">subst</span>.\
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
     <span class="id" type="var">SCase</span> "b1 evaluates to false".\
       <span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> "b1 evaluates to true
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H2</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H2</span>.\
   <span class="id" type="var">Case</span> "E\_WhileLoop".\
     <span class="id" type="var">SCase</span> "b1 evaluates to false
(contradiction)".\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H4</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H4</span>.\
     <span class="id" type="var">SCase</span> "b1 evaluates to true".\
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

</div>

\

</div>

<div class="doc">

Reasoning About Imp Programs {.section}
============================

<div class="paragraph">

</div>

We'll get much deeper into systematic techniques for reasoning about Imp
programs in the following chapters, but we can do quite a bit just
working with the bare definitions.

</div>

<div class="code code-tight">

\
 <span
class="comment">(\* This section explores some examples. \*)</span>\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">plus2\_spec</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">n</span> <span
class="id" type="var">st'</span>,\
   <span class="id" type="var">st</span> <span class="id"
type="var">X</span> = <span class="id" type="var">n</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">plus2</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">st'</span> <span class="id"
type="var">X</span> = <span class="id" type="var">n</span> + 2.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> <span class="id" type="var">n</span> <span
class="id" type="var">st'</span> <span class="id" type="var">HX</span>
<span class="id" type="var">Heval</span>.\
   <span
class="comment">(\* Inverting Heval essentially forces Coq to expand one\
      step of the ceval computation - in this case revealing\
      that st' must be st extended with the new value of X,\
      since plus2 is an assignment \*)</span>\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heval</span>. <span class="id" type="tactic">subst</span>.
<span class="id" type="tactic">clear</span> <span class="id"
type="var">Heval</span>. <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">update\_eq</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars (XtimesYinZ\_spec) {.section}

State and prove a specification of <span class="inlinecode"><span
class="id" type="var">XtimesYinZ</span></span>.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (loop\_never\_stops) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">loop\_never\_stops</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span>,\
   \~(<span class="id" type="var">loop</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">contra</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">loop</span>
<span class="id" type="keyword">in</span> <span class="id"
type="var">contra</span>.\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">WHILE</span> <span class="id" type="var">BTrue</span> <span
class="id" type="var">DO</span> <span class="id" type="var">SKIP</span>
<span class="id" type="var">END</span>) <span class="id"
type="keyword">as</span> <span class="id" type="var">loopdef</span>
<span class="id" type="var">eqn</span>:<span class="id"
type="var">Heqloopdef</span>.\
     <span
class="comment">(\* Proceed by induction on the assumed derivation showing that\
      <span class="inlinecode"><span class="id"
type="var">loopdef</span></span> terminates.  Most of the cases are immediately\
      contradictory (and so can be solved in one step with\
      <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span>). \*)</span>\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (no\_whilesR) {.section}

Consider the definition of the <span class="inlinecode"><span class="id"
type="var">no\_whiles</span></span> property below:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">no\_whiles</span> (<span class="id" type="var">c</span> :
<span class="id" type="var">com</span>) : <span class="id"
type="var">bool</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">c</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">SKIP</span> ⇒ <span class="id"
type="var">true</span>\
   | <span class="id" type="var">\_</span> ::= <span class="id"
type="var">\_</span> ⇒ <span class="id" type="var">true</span>\
   | <span class="id" type="var">c1</span> ;; <span class="id"
type="var">c2</span> ⇒ <span class="id" type="var">andb</span> (<span
class="id" type="var">no\_whiles</span> <span class="id"
type="var">c1</span>) (<span class="id" type="var">no\_whiles</span>
<span class="id" type="var">c2</span>)\
   | <span class="id" type="var">IFB</span> <span class="id"
type="var">\_</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">ct</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">cf</span> <span class="id"
type="var">FI</span> ⇒ <span class="id" type="var">andb</span> (<span
class="id" type="var">no\_whiles</span> <span class="id"
type="var">ct</span>) (<span class="id" type="var">no\_whiles</span>
<span class="id" type="var">cf</span>)\
   | <span class="id" type="var">WHILE</span> <span class="id"
type="var">\_</span> <span class="id" type="var">DO</span> <span
class="id" type="var">\_</span> <span class="id" type="var">END</span> ⇒
<span class="id" type="var">false</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

This property yields <span class="inlinecode"><span class="id"
type="var">true</span></span> just on programs that have no while loops.
Using <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span>, write a property <span
class="inlinecode"><span class="id" type="var">no\_whilesR</span></span>
such that <span class="inlinecode"><span class="id"
type="var">no\_whilesR</span></span> <span class="inlinecode"><span
class="id" type="var">c</span></span> is provable exactly when <span
class="inlinecode"><span class="id" type="var">c</span></span> is a
program with no while loops. Then prove its equivalence with <span
class="inlinecode"><span class="id" type="var">no\_whiles</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">no\_whilesR</span>: <span class="id" type="var">com</span>
<span style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
  <span class="comment">(\* FILL IN HERE \*)</span>\
   .\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">no\_whiles\_eqv</span>:\
    <span style="font-family: arial;">∀</span><span class="id"
type="var">c</span>, <span class="id" type="var">no\_whiles</span> <span
class="id" type="var">c</span> = <span class="id" type="var">true</span>
<span style="font-family: arial;">↔</span> <span class="id"
type="var">no\_whilesR</span> <span class="id" type="var">c</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars (no\_whiles\_terminating) {.section}

Imp programs that don't involve while loops always terminate. State and
prove a theorem <span class="inlinecode"><span class="id"
type="var">no\_whiles\_terminating</span></span> that says this. (Use
either <span class="inlinecode"><span class="id"
type="var">no\_whiles</span></span> or <span class="inlinecode"><span
class="id" type="var">no\_whilesR</span></span>, as you prefer.)

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

#### Exercise: 3 stars (stack\_compiler) {.section}

HP Calculators, programming languages like Forth and Postscript, and
abstract machines like the Java Virtual Machine all evaluate arithmetic
expressions using a stack. For instance, the expression
       (2*3)+(3*(4-2))

would be entered as
       2 3 * 3 4 2 - * +

and evaluated like this:
      []            |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

<div class="paragraph">

</div>

The task of this exercise is to write a small compiler that translates
<span class="inlinecode"><span class="id" type="var">aexp</span></span>s
into stack machine instructions.
<div class="paragraph">

</div>

The instruction set for our stack language will consist of the following
instructions:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">SPush</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span></span>: Push the number <span
    class="inlinecode"><span class="id" type="var">n</span></span> on
    the stack.
-   <span class="inlinecode"><span class="id"
    type="var">SLoad</span></span> <span class="inlinecode"><span
    class="id" type="var">x</span></span>: Load the identifier <span
    class="inlinecode"><span class="id" type="var">x</span></span> from
    the store and push it on the stack
-   <span class="inlinecode"><span class="id"
    type="var">SPlus</span></span>: Pop the two top numbers from the
    stack, add them, and push the result onto the stack.
-   <span class="inlinecode"><span class="id"
    type="var">SMinus</span></span>: Similar, but subtract.
-   <span class="inlinecode"><span class="id"
    type="var">SMult</span></span>: Similar, but multiply.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">sinstr</span> : <span class="id" type="keyword">Type</span>
:=\
 | <span class="id" type="var">SPush</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">sinstr</span>\
 | <span class="id" type="var">SLoad</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">sinstr</span>\
 | <span class="id" type="var">SPlus</span> : <span class="id"
type="var">sinstr</span>\
 | <span class="id" type="var">SMinus</span> : <span class="id"
type="var">sinstr</span>\
 | <span class="id" type="var">SMult</span> : <span class="id"
type="var">sinstr</span>.\
\

</div>

<div class="doc">

Write a function to evaluate programs in the stack language. It takes as
input a state, a stack represented as a list of numbers (top stack item
is the head of the list), and a program represented as a list of
instructions, and returns the stack after executing the program. Test
your function on the examples below.
<div class="paragraph">

</div>

Note that the specification leaves unspecified what to do when
encountering an <span class="inlinecode"><span class="id"
type="var">SPlus</span></span>, <span class="inlinecode"><span
class="id" type="var">SMinus</span></span>, or <span
class="inlinecode"><span class="id" type="var">SMult</span></span>
instruction if the stack contains less than two elements. In a sense, it
is immaterial what we do, since our compiler will never emit such a
malformed program.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">s\_execute</span> (<span class="id" type="var">st</span> :
<span class="id" type="var">state</span>) (<span class="id"
type="var">stack</span> : <span class="id" type="var">list</span> <span
class="id" type="var">nat</span>)\
                    (<span class="id" type="var">prog</span> : <span
class="id" type="var">list</span> <span class="id"
type="var">sinstr</span>)\
                  : <span class="id" type="var">list</span> <span
class="id" type="var">nat</span> :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">s\_execute1</span> :\
      <span class="id" type="var">s\_execute</span> <span class="id"
type="var">empty\_state</span> []\
        [<span class="id" type="var">SPush</span> 5; <span class="id"
type="var">SPush</span> 3; <span class="id" type="var">SPush</span> 1;
<span class="id" type="var">SMinus</span>]\
    = [2; 5].\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">s\_execute2</span> :\
      <span class="id" type="var">s\_execute</span> (<span class="id"
type="var">update</span> <span class="id" type="var">empty\_state</span>
<span class="id" type="var">X</span> 3) [3;4]\
        [<span class="id" type="var">SPush</span> 4; <span class="id"
type="var">SLoad</span> <span class="id" type="var">X</span>; <span
class="id" type="var">SMult</span>; <span class="id"
type="var">SPlus</span>]\
    = [15; 4].\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Next, write a function which compiles an <span class="inlinecode"><span
class="id" type="var">aexp</span></span> into a stack machine program.
The effect of running the program should be the same as pushing the
value of the expression on the stack.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">s\_compile</span> (<span class="id" type="var">e</span> :
<span class="id" type="var">aexp</span>) : <span class="id"
type="var">list</span> <span class="id" type="var">sinstr</span> :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\

</div>

<div class="doc">

After you've defined <span class="inlinecode"><span class="id"
type="var">s\_compile</span></span>, prove the following to test that it
works.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">s\_compile1</span> :\
     <span class="id" type="var">s\_compile</span> (<span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id"
type="var">AMult</span> (<span class="id" type="var">ANum</span> 2)
(<span class="id" type="var">AId</span> <span class="id"
type="var">Y</span>)))\
   = [<span class="id" type="var">SLoad</span> <span class="id"
type="var">X</span>; <span class="id" type="var">SPush</span> 2; <span
class="id" type="var">SLoad</span> <span class="id" type="var">Y</span>;
<span class="id" type="var">SMult</span>; <span class="id"
type="var">SMinus</span>].\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (stack\_compiler\_correct) {.section}

The task of this exercise is to prove the correctness of the compiler
implemented in the previous exercise. Remember that the specification
left unspecified what to do when encountering an <span
class="inlinecode"><span class="id" type="var">SPlus</span></span>,
<span class="inlinecode"><span class="id"
type="var">SMinus</span></span>, or <span class="inlinecode"><span
class="id" type="var">SMult</span></span> instruction if the stack
contains less than two elements. (In order to make your correctness
proof easier you may find it useful to go back and change your
implementation!)
<div class="paragraph">

</div>

Prove the following theorem, stating that the <span
class="inlinecode"><span class="id" type="var">compile</span></span>
function behaves correctly. You will need to start by stating a more
general lemma to get a usable induction hypothesis; the main theorem
will then be a simple corollary of this lemma.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">s\_compile\_correct</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st</span> : <span class="id" type="var">state</span>) (<span
class="id" type="var">e</span> : <span class="id"
type="var">aexp</span>),\
   <span class="id" type="var">s\_execute</span> <span class="id"
type="var">st</span> [] (<span class="id" type="var">s\_compile</span>
<span class="id" type="var">e</span>) = [ <span class="id"
type="var">aeval</span> <span class="id" type="var">st</span> <span
class="id" type="var">e</span> ].\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 5 stars, advanced (break\_imp) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Module</span> <span class="id"
type="var">BreakImp</span>.\
\

</div>

<div class="doc">

Imperative languages such as C or Java often have a <span
class="inlinecode"><span class="id" type="var">break</span></span> or
similar statement for interrupting the execution of loops. In this
exercise we will consider how to add <span class="inlinecode"><span
class="id" type="var">break</span></span> to Imp.
<div class="paragraph">

</div>

First, we need to enrich the language of commands with an additional
case.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">com</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">CSkip</span> : <span class="id"
type="var">com</span>\
   | <span class="id" type="var">CBreak</span> : <span class="id"
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
type="var">com</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span> "com\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "SKIP" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "BREAK"
| <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "::=" | <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">c</span> ";"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "IFB" | <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">c</span> "WHILE" ].\
\
 <span class="id" type="keyword">Notation</span> "'SKIP'" :=\
   <span class="id" type="var">CSkip</span>.\
 <span class="id" type="keyword">Notation</span> "'BREAK'" :=\
   <span class="id" type="var">CBreak</span>.\
 <span class="id" type="keyword">Notation</span> "x '::=' a" :=\
   (<span class="id" type="var">CAss</span> <span class="id"
type="var">x</span> <span class="id" type="var">a</span>) (<span
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
 <span class="id" type="keyword">Notation</span> "'IFB' c1 'THEN' c2
'ELSE' c3 'FI'" :=\
   (<span class="id" type="var">CIf</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c2</span> <span
class="id" type="var">c3</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 80,
<span class="id" type="var">right</span> <span class="id"
type="var">associativity</span>).\
\

</div>

<div class="doc">

Next, we need to define the behavior of <span class="inlinecode"><span
class="id" type="var">BREAK</span></span>. Informally, whenever <span
class="inlinecode"><span class="id" type="var">BREAK</span></span> is
executed in a sequence of commands, it stops the execution of that
sequence and signals that the innermost enclosing loop (if any) should
terminate. If there aren't any enclosing loops, then the whole program
simply terminates. The final state should be the same as the one in
which the <span class="inlinecode"><span class="id"
type="var">BREAK</span></span> statement was executed.
<div class="paragraph">

</div>

One important point is what to do when there are multiple loops
enclosing a given <span class="inlinecode"><span class="id"
type="var">BREAK</span></span>. In those cases, <span
class="inlinecode"><span class="id" type="var">BREAK</span></span>
should only terminate the *innermost* loop where it occurs. Thus, after
executing the following piece of code...
<div class="paragraph">

</div>

<div class="code code-tight">

   <span class="id" type="var">X</span> ::= 0;;\
    <span class="id" type="var">Y</span> ::= 1;;\
    <span class="id" type="var">WHILE</span> 0 ≠ <span class="id"
type="var">Y</span> <span class="id" type="var">DO</span>\
      <span class="id" type="var">WHILE</span> <span class="id"
type="var">TRUE</span> <span class="id" type="var">DO</span>\
        <span class="id" type="var">BREAK</span>\
      <span class="id" type="var">END</span>;;\
      <span class="id" type="var">X</span> ::= 1;;\
      <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> - 1\
    <span class="id" type="var">END</span>
<div class="paragraph">

</div>

</div>

... the value of <span class="inlinecode"><span class="id"
type="var">X</span></span> should be <span class="inlinecode">1</span>,
and not <span class="inlinecode">0</span>.
<div class="paragraph">

</div>

One way of expressing this behavior is to add another parameter to the
evaluation relation that specifies whether evaluation of a command
executes a <span class="inlinecode"><span class="id"
type="var">BREAK</span></span> statement:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">status</span> : <span class="id" type="keyword">Type</span>
:=\
   | <span class="id" type="var">SContinue</span> : <span class="id"
type="var">status</span>\
   | <span class="id" type="var">SBreak</span> : <span class="id"
type="var">status</span>.\
\
 <span class="id" type="keyword">Reserved Notation</span> "c1 '/' st
'<span style="font-family: arial;">⇓</span>' s '/' st'"\
                   (<span class="id" type="tactic">at</span> <span
class="id" type="var">level</span> 40, <span class="id"
type="var">st</span>, <span class="id" type="var">s</span> <span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 39).\
\

</div>

<div class="doc">

Intuitively, <span class="inlinecode"><span class="id"
type="var">c</span></span> <span class="inlinecode">/</span> <span
class="inlinecode"><span class="id" type="var">st</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇓</span></span>
<span class="inlinecode"><span class="id" type="var">s</span></span>
<span class="inlinecode">/</span> <span class="inlinecode"><span
class="id" type="var">st'</span></span> means that, if <span
class="inlinecode"><span class="id" type="var">c</span></span> is
started in state <span class="inlinecode"><span class="id"
type="var">st</span></span>, then it terminates in state <span
class="inlinecode"><span class="id" type="var">st'</span></span> and
either signals that any surrounding loop (or the whole program) should
exit immediately (<span class="inlinecode"><span class="id"
type="var">s</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">SBreak</span></span>) or
that execution should continue normally (<span class="inlinecode"><span
class="id" type="var">s</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">SContinue</span></span>).
<div class="paragraph">

</div>

The definition of the "<span class="inlinecode"><span class="id"
type="var">c</span></span> <span class="inlinecode">/</span> <span
class="inlinecode"><span class="id" type="var">st</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇓</span></span>
<span class="inlinecode"><span class="id" type="var">s</span></span>
<span class="inlinecode">/</span> <span class="inlinecode"><span
class="id" type="var">st'</span></span>" relation is very similar to the
one we gave above for the regular evaluation relation (<span
class="inlinecode"><span class="id" type="var">c</span></span> <span
class="inlinecode">/</span> <span class="inlinecode"><span class="id"
type="var">st</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇓</span></span> <span
class="inlinecode"><span class="id" type="var">s</span></span> <span
class="inlinecode">/</span> <span class="inlinecode"><span class="id"
type="var">st'</span></span>) — we just need to handle the termination
signals appropriately:
<div class="paragraph">

</div>

-   If the command is <span class="inlinecode"><span class="id"
    type="var">SKIP</span></span>, then the state doesn't change, and
    execution of any enclosing loop can continue normally.
    <div class="paragraph">

    </div>

-   If the command is <span class="inlinecode"><span class="id"
    type="var">BREAK</span></span>, the state stays unchanged, but we
    signal a <span class="inlinecode"><span class="id"
    type="var">SBreak</span></span>.
    <div class="paragraph">

    </div>

-   If the command is an assignment, then we update the binding for that
    variable in the state accordingly and signal that execution can
    continue normally.
    <div class="paragraph">

    </div>

-   If the command is of the form <span class="inlinecode"><span
    class="id" type="var">IF</span></span> <span
    class="inlinecode"><span class="id" type="var">b</span></span> <span
    class="inlinecode"><span class="id" type="var">THEN</span></span>
    <span class="inlinecode"><span class="id"
    type="var">c1</span></span> <span class="inlinecode"><span
    class="id" type="var">ELSE</span></span> <span
    class="inlinecode"><span class="id" type="var">c2</span></span>
    <span class="inlinecode"><span class="id"
    type="var">FI</span></span>, then the state is updated as in the
    original semantics of Imp, except that we also propagate the signal
    from the execution of whichever branch was taken.
    <div class="paragraph">

    </div>

-   If the command is a sequence <span class="inlinecode"><span
    class="id" type="var">c1</span></span> <span
    class="inlinecode">;</span> <span class="inlinecode"><span
    class="id" type="var">c2</span></span>, we first execute <span
    class="inlinecode"><span class="id" type="var">c1</span></span>. If
    this yields a <span class="inlinecode"><span class="id"
    type="var">SBreak</span></span>, we skip the execution of <span
    class="inlinecode"><span class="id" type="var">c2</span></span> and
    propagate the <span class="inlinecode"><span class="id"
    type="var">SBreak</span></span> signal to the surrounding context;
    the resulting state should be the same as the one obtained by
    executing <span class="inlinecode"><span class="id"
    type="var">c1</span></span> alone. Otherwise, we execute <span
    class="inlinecode"><span class="id" type="var">c2</span></span> on
    the state obtained after executing <span class="inlinecode"><span
    class="id" type="var">c1</span></span>, and propagate the signal
    that was generated there.
    <div class="paragraph">

    </div>

-   Finally, for a loop of the form <span class="inlinecode"><span
    class="id" type="var">WHILE</span></span> <span
    class="inlinecode"><span class="id" type="var">b</span></span> <span
    class="inlinecode"><span class="id" type="var">DO</span></span>
    <span class="inlinecode"><span class="id" type="var">c</span></span>
    <span class="inlinecode"><span class="id"
    type="var">END</span></span>, the semantics is almost the same as
    before. The only difference is that, when <span
    class="inlinecode"><span class="id" type="var">b</span></span>
    evaluates to true, we execute <span class="inlinecode"><span
    class="id" type="var">c</span></span> and check the signal that it
    raises. If that signal is <span class="inlinecode"><span class="id"
    type="var">SContinue</span></span>, then the execution proceeds as
    in the original semantics. Otherwise, we stop the execution of the
    loop, and the resulting state is the same as the one resulting from
    the execution of the current iteration. In either case, since <span
    class="inlinecode"><span class="id" type="var">BREAK</span></span>
    only terminates the innermost loop, <span class="inlinecode"><span
    class="id" type="var">WHILE</span></span> signals <span
    class="inlinecode"><span class="id"
    type="var">SContinue</span></span>.

<div class="paragraph">

</div>

Based on the above description, complete the definition of the <span
class="inlinecode"><span class="id" type="var">ceval</span></span>
relation.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ceval</span> : <span class="id" type="var">com</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">state</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">status</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">state</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">E\_Skip</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span>,\
       <span class="id" type="var">CSkip</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">SContinue</span> / <span class="id"
type="var">st</span>\
   <span class="comment">(\* FILL IN HERE \*)</span>\
\
   <span class="id" type="keyword">where</span> "c1 '/' st '<span
style="font-family: arial;">⇓</span>' s '/' st'" := (<span class="id"
type="var">ceval</span> <span class="id" type="var">c1</span> <span
class="id" type="var">st</span> <span class="id" type="var">s</span>
<span class="id" type="var">st'</span>).\
\
 <span class="id" type="keyword">Tactic Notation</span> "ceval\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_Skip"\
   <span class="comment">(\* FILL IN HERE \*)</span>\
   ].\
\

</div>

<div class="doc">

Now the following properties of your definition of <span
class="inlinecode"><span class="id" type="var">ceval</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">break\_ignore</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span> <span class="id" type="var">s</span>,\
      (<span class="id" type="var">BREAK</span>;; <span class="id"
type="var">c</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">s</span> / <span class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">st</span> = <span class="id"
type="var">st'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">while\_continue</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span> <span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">s</span>,\
   (<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span>) /
<span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">s</span> / <span class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">s</span> = <span class="id"
type="var">SContinue</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">while\_stops\_on\_break</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span> <span class="id"
type="var">st</span> <span class="id" type="var">st'</span>,\
   <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">SBreak</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span>) /
<span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">SContinue</span> / <span class="id" type="var">st'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars, advanced, optional (while\_break\_true) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">while\_break\_true</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span> <span class="id"
type="var">st</span> <span class="id" type="var">st'</span>,\
   (<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span>) /
<span class="id" type="var">st</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">SContinue</span> / <span class="id" type="var">st'</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">beval</span> <span class="id"
type="var">st'</span> <span class="id" type="var">b</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">st''</span>, <span class="id" type="var">c</span> / <span
class="id" type="var">st''</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">SBreak</span> / <span class="id" type="var">st'</span>.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

#### Exercise: 4 stars, advanced, optional (ceval\_deterministic) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_deterministic</span>: <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">c</span>:<span class="id" type="var">com</span>) <span
class="id" type="var">st</span> <span class="id" type="var">st1</span>
<span class="id" type="var">st2</span> <span class="id"
type="var">s~1~</span> <span class="id" type="var">s~2~</span>,\
      <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">s~1~</span> / <span class="id"
type="var">st1</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">s~2~</span> / <span class="id"
type="var">st2</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">st1</span> = <span class="id"
type="var">st2</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">s~1~</span> = <span class="id"
type="var">s~2~</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">BreakImp</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (short\_circuit) {.section}

Most modern programming languages use a "short-circuit" evaluation rule
for boolean <span class="inlinecode"><span class="id"
type="var">and</span></span>: to evaluate <span class="inlinecode"><span
class="id" type="var">BAnd</span></span> <span class="inlinecode"><span
class="id" type="var">b1</span></span> <span class="inlinecode"><span
class="id" type="var">b2</span></span>, first evaluate <span
class="inlinecode"><span class="id" type="var">b1</span></span>. If it
evaluates to <span class="inlinecode"><span class="id"
type="var">false</span></span>, then the entire <span
class="inlinecode"><span class="id" type="var">BAnd</span></span>
expression evaluates to <span class="inlinecode"><span class="id"
type="var">false</span></span> immediately, without evaluating <span
class="inlinecode"><span class="id" type="var">b2</span></span>.
Otherwise, <span class="inlinecode"><span class="id"
type="var">b2</span></span> is evaluated to determine the result of the
<span class="inlinecode"><span class="id" type="var">BAnd</span></span>
expression.
<div class="paragraph">

</div>

Write an alternate version of <span class="inlinecode"><span class="id"
type="var">beval</span></span> that performs short-circuit evaluation of
<span class="inlinecode"><span class="id" type="var">BAnd</span></span>
in this manner, and prove that it is equivalent to <span
class="inlinecode"><span class="id" type="var">beval</span></span>.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, optional (add\_for\_loop) {.section}

Add C-style <span class="inlinecode"><span class="id"
type="keyword">for</span></span> loops to the language of commands,
update the <span class="inlinecode"><span class="id"
type="var">ceval</span></span> definition to define the semantics of
<span class="inlinecode"><span class="id"
type="keyword">for</span></span> loops, and add cases for <span
class="inlinecode"><span class="id" type="keyword">for</span></span>
loops as needed so that all the proofs in this file are accepted by Coq.
<div class="paragraph">

</div>

A <span class="inlinecode"><span class="id"
type="keyword">for</span></span> loop should be parameterized by (a) a
statement executed initially, (b) a test that is run on each iteration
of the loop to determine whether the loop should continue, (c) a
statement executed at the end of each loop iteration, and (d) a
statement that makes up the body of the loop. (You don't need to worry
about making up a concrete Notation for <span class="inlinecode"><span
class="id" type="keyword">for</span></span> loops, but feel free to play
with this too if you like.)

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
 <span
class="comment">(\* \<\$Date: 2014-12-26 15:20:26 -0500 (Fri, 26 Dec 2014) \$ \*)</span>\
\

</div>

</div>

<div id="footer">

------------------------------------------------------------------------

[Index](http://www.cis.upenn.edu/~bcpierce/sf/current/coqindex.html)

</div>

</div>
