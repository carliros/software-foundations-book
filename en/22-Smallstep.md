<div id="page">

<div id="header">

</div>

<div id="main">

Smallstep<span class="subtitle">Small-step Operational Semantics</span> {.libtitle}
=======================================================================

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

The evaluators we have seen so far (e.g., the ones for <span
class="inlinecode"><span class="id" type="var">aexp</span></span>s,
<span class="inlinecode"><span class="id"
type="var">bexp</span></span>s, and commands) have been formulated in a
"big-step" style — they specify how a given expression can be evaluated
to its final value (or a command plus a store to a final store) "all in
one big step."
<div class="paragraph">

</div>

This style is simple and natural for many purposes — indeed, Gilles
Kahn, who popularized its use, called it *natural semantics*. But there
are some things it does not do well. In particular, it does not give us
a natural way of talking about *concurrent* programming languages, where
the "semantics" of a program — i.e., the essence of how it behaves — is
not just which input states get mapped to which output states, but also
includes the intermediate states that it passes through along the way,
since these states can also be observed by concurrently executing code.
<div class="paragraph">

</div>

Another shortcoming of the big-step style is more technical, but
critical in some situations. To see the issue, suppose we wanted to
define a variant of Imp where variables could hold *either* numbers *or*
lists of numbers (see the <span class="inlinecode"><span class="id"
type="var">HoareList</span></span> chapter for details). In the syntax
of this extended language, it will be possible to write strange
expressions like <span class="inlinecode">2</span> <span
class="inlinecode">+</span> <span class="inlinecode"><span class="id"
type="var">nil</span></span>, and our semantics for arithmetic
expressions will then need to say something about how such expressions
behave. One possibility (explored in the <span class="inlinecode"><span
class="id" type="var">HoareList</span></span> chapter) is to maintain
the convention that every arithmetic expressions evaluates to some
number by choosing some way of viewing a list as a number — e.g., by
specifying that a list should be interpreted as <span
class="inlinecode">0</span> when it occurs in a context expecting a
number. But this is really a bit of a hack.
<div class="paragraph">

</div>

A much more natural approach is simply to say that the behavior of an
expression like <span class="inlinecode">2+<span class="id"
type="var">nil</span></span> is *undefined* — it doesn't evaluate to any
result at all. And we can easily do this: we just have to formulate
<span class="inlinecode"><span class="id" type="var">aeval</span></span>
and <span class="inlinecode"><span class="id"
type="var">beval</span></span> as <span class="inlinecode"><span
class="id" type="keyword">Inductive</span></span> propositions rather
than Fixpoints, so that we can make them partial functions instead of
total ones.
<div class="paragraph">

</div>

However, now we encounter a serious deficiency. In this language, a
command might *fail* to map a given starting state to any ending state
for two quite different reasons: either because the execution gets into
an infinite loop or because, at some point, the program tries to do an
operation that makes no sense, such as adding a number to a list, and
none of the evaluation rules can be applied.
<div class="paragraph">

</div>

These two outcomes — nontermination vs. getting stuck in an erroneous
configuration — are quite different. In particular, we want to allow the
first (permitting the possibility of infinite loops is the price we pay
for the convenience of programming with general looping constructs like
<span class="inlinecode"><span class="id"
type="var">while</span></span>) but prevent the second (which is just
wrong), for example by adding some form of *typechecking* to the
language. Indeed, this will be a major topic for the rest of the course.
As a first step, we need a different way of presenting the semantics
that allows us to distinguish nontermination from erroneous "stuck
states."
<div class="paragraph">

</div>

So, for lots of reasons, we'd like to have a finer-grained way of
defining and reasoning about program behaviors. This is the topic of the
present chapter. We replace the "big-step" <span
class="inlinecode"><span class="id" type="var">eval</span></span>
relation with a "small-step" relation that specifies, for a given
program, how the "atomic steps" of computation are performed.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

A Toy Language {.section}
==============

<div class="paragraph">

</div>

To save space in the discussion, let's go back to an incredibly simple
language containing just constants and addition. (We use single letters
— <span class="inlinecode"><span class="id" type="var">C</span></span>
and <span class="inlinecode"><span class="id" type="var">P</span></span>
— for the constructor names, for brevity.) At the end of the chapter,
we'll see how to apply the same techniques to the full Imp language.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">tm</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">C</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
class="comment">(\* Constant \*)</span>\
   | <span class="id" type="var">P</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span>. <span class="comment">(\* Plus \*)</span>\
\
 <span class="id" type="keyword">Tactic Notation</span> "tm\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "C" | <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">c</span> "P" ].\
\

</div>

<div class="doc">

Here is a standard evaluator for this language, written in the same
(big-step) style as we've been using up to this point.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">evalF</span> (<span class="id" type="var">t</span> : <span
class="id" type="var">tm</span>) : <span class="id"
type="var">nat</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">t</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">C</span> <span class="id"
type="var">n</span> ⇒ <span class="id" type="var">n</span>\
   | <span class="id" type="var">P</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span> ⇒ <span
class="id" type="var">evalF</span> <span class="id"
type="var">a1</span> + <span class="id" type="var">evalF</span> <span
class="id" type="var">a2</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Now, here is the same evaluator, written in exactly the same style, but
formulated as an inductively defined relation. Again, we use the
notation <span class="inlinecode"><span class="id"
type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇓</span></span> <span
class="inlinecode"><span class="id" type="var">n</span></span> for
"<span class="inlinecode"><span class="id" type="var">t</span></span>
evaluates to <span class="inlinecode"><span class="id"
type="var">n</span></span>."
<div class="paragraph">

</div>

  
(E\_Const)  

------------------------------------------------------------------------

C n <span style="font-family: arial;">⇓</span> n
t~1~ <span style="font-family: arial;">⇓</span> n1
t~2~ <span style="font-family: arial;">⇓</span> n2
(E\_Plus)  

------------------------------------------------------------------------

P t~1~ t~2~ <span style="font-family: arial;">⇓</span> C (n1 + n2)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> " t '<span
style="font-family: arial;">⇓</span>' n " (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 50,
<span class="id" type="var">left</span> <span class="id"
type="var">associativity</span>).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">eval</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
<div id="proofcontrol1" class="togglescript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')">

<span class="show"></span>

</div>

<div id="proof1" class="proofscript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')"
style="display: none;">

  | <span class="id" type="var">E\_Const</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
       <span class="id" type="var">C</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">n</span>\
   | <span class="id" type="var">E\_Plus</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">n1</span> <span class="id" type="var">n2</span>,\
       <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n1</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n2</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">P</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇓</span> (<span class="id"
type="var">n1</span> + <span class="id" type="var">n2</span>)\
\
   <span class="id" type="keyword">where</span> " t '<span
style="font-family: arial;">⇓</span>' n " := (<span class="id"
type="var">eval</span> <span class="id" type="var">t</span> <span
class="id" type="var">n</span>).\
\
 <span class="id" type="keyword">Tactic Notation</span> "eval\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_Const" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"E\_Plus" ].\

</div>

\
\

</div>

<div class="doc">

Now, here is a small-step version.
<div class="paragraph">

</div>

  
(ST\_PlusConstConst)  

------------------------------------------------------------------------

P (C n1) (C n2) <span style="font-family: arial;">⇒</span> C (n1 + n2)
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Plus1)  

------------------------------------------------------------------------

P t~1~ t~2~ <span style="font-family: arial;">⇒</span> P t~1~' t~2~
t~2~ <span style="font-family: arial;">⇒</span> t~2~'
(ST\_Plus2)  

------------------------------------------------------------------------

P (C n1) t~2~ <span style="font-family: arial;">⇒</span> P (C n1) t~2~'

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> " t '<span
style="font-family: arial;">⇒</span>' t' " (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">step</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">ST\_PlusConstConst</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">n2</span>,\
       <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">C</span> <span class="id" type="var">n2</span>)
<span style="font-family: arial;">⇒</span> <span class="id"
type="var">C</span> (<span class="id" type="var">n1</span> + <span
class="id" type="var">n2</span>)\
   | <span class="id" type="var">ST\_Plus1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
       <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">P</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">P</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>\
   | <span class="id" type="var">ST\_Plus2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
       <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> <span class="id" type="var">n1</span>) <span
class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">P</span> (<span class="id" type="var">C</span> <span
class="id" type="var">n1</span>) <span class="id"
type="var">t~2~'</span>\
\
   <span class="id" type="keyword">where</span> " t '<span
style="font-family: arial;">⇒</span>' t' " := (<span class="id"
type="var">step</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span>).\
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
type="var">c</span> "ST\_PlusConstConst"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Plus1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Plus2" ].\

</div>

\

</div>

<div class="doc">

Things to notice:
<div class="paragraph">

</div>

-   We are defining just a single reduction step, in which one <span
    class="inlinecode"><span class="id" type="var">P</span></span> node
    is replaced by its value.
    <div class="paragraph">

    </div>

-   Each step finds the *leftmost* <span class="inlinecode"><span
    class="id" type="var">P</span></span> node that is ready to go (both
    of its operands are constants) and rewrites it in place. The first
    rule tells how to rewrite this <span class="inlinecode"><span
    class="id" type="var">P</span></span> node itself; the other two
    rules tell how to find it.
    <div class="paragraph">

    </div>

-   A term that is just a constant cannot take a step.

<div class="paragraph">

</div>

Let's pause and check a couple of examples of reasoning with the <span
class="inlinecode"><span class="id" type="var">step</span></span>
relation...
<div class="paragraph">

</div>

If <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> can take a step to <span
class="inlinecode"><span class="id" type="var">t~1~'</span></span>, then
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span class="id" type="var">t~1~</span></span>
<span class="inlinecode"><span class="id" type="var">t~2~</span></span>
steps to <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode"><span class="id"
type="var">t~1~'</span></span> <span class="inlinecode"><span class="id"
type="var">t~2~</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_step\_1</span> :\
       <span class="id" type="var">P</span>\
         (<span class="id" type="var">P</span> (<span class="id"
type="var">C</span> 0) (<span class="id" type="var">C</span> 3))\
         (<span class="id" type="var">P</span> (<span class="id"
type="var">C</span> 2) (<span class="id" type="var">C</span> 4))\
       <span style="font-family: arial;">⇒</span>\
       <span class="id" type="var">P</span>\
         (<span class="id" type="var">C</span> (0 + 3))\
         (<span class="id" type="var">P</span> (<span class="id"
type="var">C</span> 2) (<span class="id" type="var">C</span> 4)).\
<div id="proofcontrol3" class="togglescript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')">

<span class="show"></span>

</div>

<div id="proof3" class="proofscript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_Plus1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">ST\_PlusConstConst</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 1 star (test\_step\_2) {.section}

Right-hand sides of sums can take a step only when the left-hand side is
finished: if <span class="inlinecode"><span class="id"
type="var">t~2~</span></span> can take a step to <span
class="inlinecode"><span class="id" type="var">t~2~'</span></span>, then
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode">(<span class="id" type="var">C</span></span>
<span class="inlinecode"><span class="id" type="var">n</span>)</span>
<span class="inlinecode"><span class="id" type="var">t~2~</span></span>
steps to <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">(<span class="id"
type="var">C</span></span> <span class="inlinecode"><span class="id"
type="var">n</span>)</span> <span class="inlinecode"><span class="id"
type="var">t~2~'</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_step\_2</span> :\
       <span class="id" type="var">P</span>\
         (<span class="id" type="var">C</span> 0)\
         (<span class="id" type="var">P</span>\
           (<span class="id" type="var">C</span> 2)\
           (<span class="id" type="var">P</span> (<span class="id"
type="var">C</span> 0) (<span class="id" type="var">C</span> 3)))\
       <span style="font-family: arial;">⇒</span>\
       <span class="id" type="var">P</span>\
         (<span class="id" type="var">C</span> 0)\
         (<span class="id" type="var">P</span>\
           (<span class="id" type="var">C</span> 2)\
           (<span class="id" type="var">C</span> (0 + 3))).\
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

Relations {.section}
=========

<div class="paragraph">

</div>

We will be using several different step relations, so it is helpful to
generalize a bit and state a few definitions and theorems about
relations in general. (The optional chapter <span
class="inlinecode"><span class="id" type="var">Rel.v</span></span>
develops some of these ideas in a bit more detail; it may be useful if
the treatment here is too dense.)
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

Our main examples of such relations in this chapter will be the
single-step and multi-step reduction relations on terms, <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span> and
<span class="inlinecode"><span
style="font-family: arial;">⇒\*</span></span>, but there are many other
examples — some that come to mind are the "equals," "less than," "less
than or equal to," and "is the square of" relations on numbers, and the
"prefix of" relation on lists and strings.
<div class="paragraph">

</div>

One simple property of the <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> relation is that, like the
evaluation relation for our language of Imp programs, it is
*deterministic*.
<div class="paragraph">

</div>

*Theorem*: For each <span class="inlinecode"><span class="id"
type="var">t</span></span>, there is at most one <span
class="inlinecode"><span class="id" type="var">t'</span></span> such
that <span class="inlinecode"><span class="id"
type="var">t</span></span> steps to <span class="inlinecode"><span
class="id" type="var">t'</span></span> (<span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> is
provable). Formally, this is the same as saying that <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span> is
deterministic.
<div class="paragraph">

</div>

*Proof sketch*: We show that if <span class="inlinecode"><span
class="id" type="var">x</span></span> steps to both <span
class="inlinecode"><span class="id" type="var">y1</span></span> and
<span class="inlinecode"><span class="id" type="var">y2</span></span>
then <span class="inlinecode"><span class="id"
type="var">y1</span></span> and <span class="inlinecode"><span
class="id" type="var">y2</span></span> are equal, by induction on a
derivation of <span class="inlinecode"><span class="id"
type="var">step</span></span> <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode"><span class="id"
type="var">y1</span></span>. There are several cases to consider,
depending on the last rule used in this derivation and in the given
derivation of <span class="inlinecode"><span class="id"
type="var">step</span></span> <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode"><span class="id"
type="var">y2</span></span>.
<div class="paragraph">

</div>

-   If both are <span class="inlinecode"><span class="id"
    type="var">ST\_PlusConstConst</span></span>, the result is
    immediate.
    <div class="paragraph">

    </div>

-   The cases when both derivations end with <span
    class="inlinecode"><span class="id"
    type="var">ST\_Plus1</span></span> or <span class="inlinecode"><span
    class="id" type="var">ST\_Plus2</span></span> follow by the
    induction hypothesis.
    <div class="paragraph">

    </div>

-   It cannot happen that one is <span class="inlinecode"><span
    class="id" type="var">ST\_PlusConstConst</span></span> and the other
    is <span class="inlinecode"><span class="id"
    type="var">ST\_Plus1</span></span> or <span class="inlinecode"><span
    class="id" type="var">ST\_Plus2</span></span>, since this would
    imply that <span class="inlinecode"><span class="id"
    type="var">x</span></span> has the form <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> where both <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> are constants (by <span
    class="inlinecode"><span class="id"
    type="var">ST\_PlusConstConst</span></span>) *and* one of <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span> or
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> has the form <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode">...</span>.
    <div class="paragraph">

    </div>

-   Similarly, it cannot happen that one is <span
    class="inlinecode"><span class="id"
    type="var">ST\_Plus1</span></span> and the other is <span
    class="inlinecode"><span class="id"
    type="var">ST\_Plus2</span></span>, since this would imply that
    <span class="inlinecode"><span class="id" type="var">x</span></span>
    has the form <span class="inlinecode"><span class="id"
    type="var">P</span></span> <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> where <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    has both the form <span class="inlinecode"><span class="id"
    type="var">P</span></span> <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> and the form <span
    class="inlinecode"><span class="id" type="var">C</span></span> <span
    class="inlinecode"><span class="id" type="var">n</span></span>. ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">deterministic</span> {<span class="id" type="var">X</span>:
<span class="id" type="keyword">Type</span>} (<span class="id"
type="var">R</span>: <span class="id" type="var">relation</span> <span
class="id" type="var">X</span>) :=\
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
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">step\_deterministic</span>:\
   <span class="id" type="var">deterministic</span> <span class="id"
type="var">step</span>.\
<div id="proofcontrol4" class="togglescript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')">

<span class="show"></span>

</div>

<div id="proof4" class="proofscript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">deterministic</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">x</span> <span
class="id" type="var">y1</span> <span class="id" type="var">y2</span>
<span class="id" type="var">Hy1</span> <span class="id"
type="var">Hy2</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">y2</span>.\
   <span class="id" type="var">step\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Hy1</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">y2</span> <span
class="id" type="var">Hy2</span>.\
     <span class="id" type="var">Case</span> "ST\_PlusConstConst". <span
class="id" type="var">step\_cases</span> (<span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hy2</span>)
<span class="id" type="var">SCase</span>.\
       <span class="id" type="var">SCase</span> "ST\_PlusConstConst".
<span class="id" type="tactic">reflexivity</span>.\
       <span class="id" type="var">SCase</span> "ST\_Plus1". <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">H2</span>.\
       <span class="id" type="var">SCase</span> "ST\_Plus2". <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">H2</span>.\
     <span class="id" type="var">Case</span> "ST\_Plus1". <span
class="id" type="var">step\_cases</span> (<span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hy2</span>)
<span class="id" type="var">SCase</span>.\
       <span class="id" type="var">SCase</span> "ST\_PlusConstConst".
<span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hy1</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hy1</span>.\
       <span class="id" type="var">SCase</span> "ST\_Plus1".\
         <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> (<span class="id"
type="var">IHHy1</span> <span class="id" type="var">t~1~'0</span>).\
         <span class="id" type="tactic">reflexivity</span>. <span
class="id" type="tactic">assumption</span>.\
       <span class="id" type="var">SCase</span> "ST\_Plus2". <span
class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hy1</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hy1</span>.\
     <span class="id" type="var">Case</span> "ST\_Plus2". <span
class="id" type="var">step\_cases</span> (<span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hy2</span>)
<span class="id" type="var">SCase</span>.\
       <span class="id" type="var">SCase</span> "ST\_PlusConstConst".
<span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">H1</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hy1</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hy1</span>.\
       <span class="id" type="var">SCase</span> "ST\_Plus1". <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">H2</span>.\
       <span class="id" type="var">SCase</span> "ST\_Plus2".\
         <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> (<span class="id"
type="var">IHHy1</span> <span class="id" type="var">t~2~'0</span>).\
         <span class="id" type="tactic">reflexivity</span>. <span
class="id" type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

There is some annoying repetition in this proof. Each use of <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span> <span class="inlinecode"><span
class="id" type="var">Hy2</span></span> results in three subcases, only
one of which is relevant (the one which matches the current case in the
induction on <span class="inlinecode"><span class="id"
type="var">Hy1</span></span>). The other two subcases need to be
dismissed by finding the contradiction among the hypotheses and doing
inversion on it.
<div class="paragraph">

</div>

There is a tactic called <span class="inlinecode"><span class="id"
type="var">solve</span></span> <span class="inlinecode"><span class="id"
type="tactic">by</span></span> <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> defined in <span
class="inlinecode"><span class="id" type="var">SfLib.v</span></span>
that can be of use in such cases. It will solve the goal if it can be
solved by inverting some hypothesis; otherwise, it fails. (There are
variants <span class="inlinecode"><span class="id"
type="var">solve</span></span> <span class="inlinecode"><span class="id"
type="tactic">by</span></span> <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> <span class="inlinecode">2</span>
and <span class="inlinecode"><span class="id"
type="var">solve</span></span> <span class="inlinecode"><span class="id"
type="tactic">by</span></span> <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> <span class="inlinecode">3</span>
that work if two or three consecutive inversions will solve the goal.)
<div class="paragraph">

</div>

The example below shows how a proof of the previous theorem can be
simplified using this tactic.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">step\_deterministic\_alt</span>: <span class="id"
type="var">deterministic</span> <span class="id"
type="var">step</span>.\
<div id="proofcontrol5" class="togglescript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')">

<span class="show"></span>

</div>

<div id="proof5" class="proofscript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">y1</span> <span
class="id" type="var">y2</span> <span class="id" type="var">Hy1</span>
<span class="id" type="var">Hy2</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">y2</span>.\
   <span class="id" type="var">step\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Hy1</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">y2</span> <span
class="id" type="var">Hy2</span>;\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hy2</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">try</span> (<span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>).\
   <span class="id" type="var">Case</span> "ST\_PlusConstConst". <span
class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "ST\_Plus1".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHHy1</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H2</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">H2</span>.
<span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "ST\_Plus2".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHHy1</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H2</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">H2</span>.
<span class="id" type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">SimpleArith1</span>.\
\

</div>

<div class="doc">

Values {.section}
------

<div class="paragraph">

</div>

Let's take a moment to slightly generalize the way we state the
definition of single-step reduction.
<div class="paragraph">

</div>

It is useful to think of the <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> relation as defining an
*abstract machine*:
<div class="paragraph">

</div>

-   At any moment, the *state* of the machine is a term.
    <div class="paragraph">

    </div>

-   A *step* of the machine is an atomic unit of computation — here, a
    single "add" operation.
    <div class="paragraph">

    </div>

-   The *halting states* of the machine are ones where there is no more
    computation to be done.

<div class="paragraph">

</div>

We can then execute a term <span class="inlinecode"><span class="id"
type="var">t</span></span> as follows:
<div class="paragraph">

</div>

-   Take <span class="inlinecode"><span class="id"
    type="var">t</span></span> as the starting state of the machine.
    <div class="paragraph">

    </div>

-   Repeatedly use the <span class="inlinecode"><span
    style="font-family: arial;">⇒</span></span> relation to find a
    sequence of machine states, starting with <span
    class="inlinecode"><span class="id" type="var">t</span></span>,
    where each state steps to the next.
    <div class="paragraph">

    </div>

-   When no more reduction is possible, "read out" the final state of
    the machine as the result of execution.

<div class="paragraph">

</div>

Intuitively, it is clear that the final states of the machine are always
terms of the form <span class="inlinecode"><span class="id"
type="var">C</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> for some <span class="inlinecode"><span
class="id" type="var">n</span></span>. We call such terms *values*.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">value</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">v\_const</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">value</span> (<span
class="id" type="var">C</span> <span class="id" type="var">n</span>).\
\

</div>

<div class="doc">

Having introduced the idea of values, we can use it in the definition of
the <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> relation to write <span
class="inlinecode"><span class="id" type="var">ST\_Plus2</span></span>
rule in a slightly more elegant way:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

  
(ST\_PlusConstConst)  

------------------------------------------------------------------------

P (C n1) (C n2) <span style="font-family: arial;">⇒</span> C (n1 + n2)
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Plus1)  

------------------------------------------------------------------------

P t~1~ t~2~ <span style="font-family: arial;">⇒</span> P t~1~' t~2~
value v~1~
t~2~ <span style="font-family: arial;">⇒</span> t~2~'
(ST\_Plus2)  

------------------------------------------------------------------------

P v~1~ t~2~ <span style="font-family: arial;">⇒</span> P v~1~ t~2~'
Again, the variable names here carry important information: by
convention, <span class="inlinecode"><span class="id"
type="var">v~1~</span></span> ranges only over values, while <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> and
<span class="inlinecode"><span class="id" type="var">t~2~</span></span>
range over arbitrary terms. (Given this convention, the explicit <span
class="inlinecode"><span class="id" type="var">value</span></span>
hypothesis is arguably redundant. We'll keep it for now, to maintain a
close correspondence between the informal and Coq versions of the rules,
but later on we'll drop it in informal rules, for the sake of brevity.)
<div class="paragraph">

</div>

Here are the formal rules:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> " t '<span
style="font-family: arial;">⇒</span>' t' " (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">step</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">ST\_PlusConstConst</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">n2</span>,\
           <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">C</span> <span class="id" type="var">n2</span>)\
       <span style="font-family: arial;">⇒</span> <span class="id"
type="var">C</span> (<span class="id" type="var">n1</span> + <span
class="id" type="var">n2</span>)\
   | <span class="id" type="var">ST\_Plus1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
         <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
         <span class="id" type="var">P</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">P</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>\
   | <span class="id" type="var">ST\_Plus2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
         <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span> <span
class="comment">(\* \<----- n.b. \*)</span>\
         <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
         <span class="id" type="var">P</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">P</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>\
\
   <span class="id" type="keyword">where</span> " t '<span
style="font-family: arial;">⇒</span>' t' " := (<span class="id"
type="var">step</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span>).\
\
<div id="proofcontrol6" class="togglescript"
onclick="toggleDisplay('proof6');toggleDisplay('proofcontrol6')">

<span class="show"></span>

</div>

<div id="proof6" class="proofscript"
onclick="toggleDisplay('proof6');toggleDisplay('proofcontrol6')"
style="display: none;">

<span class="id" type="keyword">Tactic Notation</span> "step\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_PlusConstConst"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Plus1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Plus2" ].\

</div>

\

</div>

<div class="doc">

#### Exercise: 3 stars (redo\_determinism) {.section}

As a sanity check on this change, let's re-verify determinism
<div class="paragraph">

</div>

Proof sketch: We must show that if <span class="inlinecode"><span
class="id" type="var">x</span></span> steps to both <span
class="inlinecode"><span class="id" type="var">y1</span></span> and
<span class="inlinecode"><span class="id" type="var">y2</span></span>
then <span class="inlinecode"><span class="id"
type="var">y1</span></span> and <span class="inlinecode"><span
class="id" type="var">y2</span></span> are equal. Consider the final
rules used in the derivations of <span class="inlinecode"><span
class="id" type="var">step</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="var">y1</span></span> and <span
class="inlinecode"><span class="id" type="var">step</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">y2</span></span>.
<div class="paragraph">

</div>

-   If both are <span class="inlinecode"><span class="id"
    type="var">ST\_PlusConstConst</span></span>, the result is
    immediate.
    <div class="paragraph">

    </div>

-   It cannot happen that one is <span class="inlinecode"><span
    class="id" type="var">ST\_PlusConstConst</span></span> and the other
    is <span class="inlinecode"><span class="id"
    type="var">ST\_Plus1</span></span> or <span class="inlinecode"><span
    class="id" type="var">ST\_Plus2</span></span>, since this would
    imply that <span class="inlinecode"><span class="id"
    type="var">x</span></span> has the form <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> where both <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> are constants (by <span
    class="inlinecode"><span class="id"
    type="var">ST\_PlusConstConst</span></span>) AND one of <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span> or
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> has the form <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode">...</span>.
    <div class="paragraph">

    </div>

-   Similarly, it cannot happen that one is <span
    class="inlinecode"><span class="id"
    type="var">ST\_Plus1</span></span> and the other is <span
    class="inlinecode"><span class="id"
    type="var">ST\_Plus2</span></span>, since this would imply that
    <span class="inlinecode"><span class="id" type="var">x</span></span>
    has the form <span class="inlinecode"><span class="id"
    type="var">P</span></span> <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> where <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    both has the form <span class="inlinecode"><span class="id"
    type="var">P</span></span> <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> and is a value (hence has
    the form <span class="inlinecode"><span class="id"
    type="var">C</span></span> <span class="inlinecode"><span class="id"
    type="var">n</span></span>).
    <div class="paragraph">

    </div>

-   The cases when both derivations end with <span
    class="inlinecode"><span class="id"
    type="var">ST\_Plus1</span></span> or <span class="inlinecode"><span
    class="id" type="var">ST\_Plus2</span></span> follow by the
    induction hypothesis. ☐

<div class="paragraph">

</div>

Most of this proof is the same as the one above. But to get maximum
benefit from the exercise you should try to write it from scratch and
just use the earlier one if you get stuck.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">step\_deterministic</span> :\
   <span class="id" type="var">deterministic</span> <span class="id"
type="var">step</span>.\
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

Strong Progress and Normal Forms {.section}
--------------------------------

<div class="paragraph">

</div>

The definition of single-step reduction for our toy language is fairly
simple, but for a larger language it would be pretty easy to forget one
of the rules and create a situation where some term cannot take a step
even though it has not been completely reduced to a value. The following
theorem shows that we did not, in fact, make such a mistake here.
<div class="paragraph">

</div>

*Theorem* (*Strong Progress*): If <span class="inlinecode"><span
class="id" type="var">t</span></span> is a term, then either <span
class="inlinecode"><span class="id" type="var">t</span></span> is a
value, or there exists a term <span class="inlinecode"><span class="id"
type="var">t'</span></span> such that <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span>.
<div class="paragraph">

</div>

*Proof*: By induction on <span class="inlinecode"><span class="id"
type="var">t</span></span>.
<div class="paragraph">

</div>

-   Suppose <span class="inlinecode"><span class="id"
    type="var">t</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">C</span></span> <span
    class="inlinecode"><span class="id" type="var">n</span></span>. Then
    <span class="inlinecode"><span class="id" type="var">t</span></span>
    is a <span class="inlinecode"><span class="id"
    type="var">value</span></span>.
    <div class="paragraph">

    </div>

-   Suppose <span class="inlinecode"><span class="id"
    type="var">t</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span>, where (by the IH) <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span> is
    either a value or can step to some <span class="inlinecode"><span
    class="id" type="var">t~1~'</span></span>, and where <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span> is
    either a value or can step to some <span class="inlinecode"><span
    class="id" type="var">t~2~'</span></span>. We must show <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> is either a value or steps to some
    <span class="inlinecode"><span class="id"
    type="var">t'</span></span>.
    <div class="paragraph">

    </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> and <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span> are both values, then
        <span class="inlinecode"><span class="id"
        type="var">t</span></span> can take a step, by <span
        class="inlinecode"><span class="id"
        type="var">ST\_PlusConstConst</span></span>.
        <div class="paragraph">

        </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> is a value and <span
        class="inlinecode"><span class="id"
        type="var">t~2~</span></span> can take a step, then so can <span
        class="inlinecode"><span class="id" type="var">t</span></span>,
        by <span class="inlinecode"><span class="id"
        type="var">ST\_Plus2</span></span>.
        <div class="paragraph">

        </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> can take a step, then so can <span
        class="inlinecode"><span class="id" type="var">t</span></span>,
        by <span class="inlinecode"><span class="id"
        type="var">ST\_Plus1</span></span>. ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">strong\_progress</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>,\
   <span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">∨</span> (<span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>, <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span>).\
<div id="proofcontrol7" class="togglescript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')">

<span class="show"></span>

</div>

<div id="proof7" class="proofscript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">tm\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">t</span>)
<span class="id" type="var">Case</span>.\
     <span class="id" type="var">Case</span> "C". <span class="id"
type="var">left</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">v\_const</span>.\
     <span class="id" type="var">Case</span> "P". <span class="id"
type="var">right</span>. <span class="id" type="tactic">inversion</span>
<span class="id" type="var">IHt1</span>.\
       <span class="id" type="var">SCase</span> "l". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">IHt2</span>.\
         <span class="id" type="var">SSCase</span> "l". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span>.\
           <span style="font-family: arial;">∃</span>(<span class="id"
type="var">C</span> (<span class="id" type="var">n</span> + <span
class="id" type="var">n0</span>)).\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_PlusConstConst</span>.\
         <span class="id" type="var">SSCase</span> "r". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H0</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">t'</span> <span class="id" type="var">H1</span>].\
           <span style="font-family: arial;">∃</span>(<span class="id"
type="var">P</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t'</span>).\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_Plus2</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">H</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H1</span>.\
       <span class="id" type="var">SCase</span> "r". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">t'</span> <span class="id" type="var">H0</span>].\
           <span style="font-family: arial;">∃</span>(<span class="id"
type="var">P</span> <span class="id" type="var">t'</span> <span
class="id" type="var">t~2~</span>).\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_Plus1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">H0</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

This important property is called *strong progress*, because every term
either is a value or can "make progress" by stepping to some other term.
(The qualifier "strong" distinguishes it from a more refined version
that we'll see in later chapters, called simply "progress.")
<div class="paragraph">

</div>

The idea of "making progress" can be extended to tell us something
interesting about <span class="inlinecode"><span class="id"
type="var">value</span></span>s: in this language <span
class="inlinecode"><span class="id" type="var">value</span></span>s are
exactly the terms that *cannot* make progress in this sense.
<div class="paragraph">

</div>

To state this observation formally, let's begin by giving a name to
terms that cannot make progress. We'll call them *normal forms*.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">normal\_form</span> {<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>} (<span
class="id" type="var">R</span>:<span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">t</span>:<span class="id" type="var">X</span>) :
<span class="id" type="keyword">Prop</span> :=\
   ¬ <span style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>, <span class="id" type="var">R</span> <span
class="id" type="var">t</span> <span class="id" type="var">t'</span>.\
\

</div>

<div class="doc">

This definition actually specifies what it is to be a normal form for an
*arbitrary* relation <span class="inlinecode"><span class="id"
type="var">R</span></span> over an arbitrary set <span
class="inlinecode"><span class="id" type="var">X</span></span>, not just
for the particular single-step reduction relation over terms that we are
interested in at the moment. We'll re-use the same terminology for
talking about other relations later in the course.
<div class="paragraph">

</div>

We can use this terminology to generalize the observation we made in the
strong progress theorem: in this language, normal forms and values are
actually the same thing.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">value\_is\_nf</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v</span>,\
   <span class="id" type="var">value</span> <span class="id"
type="var">v</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">normal\_form</span> <span class="id"
type="var">step</span> <span class="id" type="var">v</span>.\
<div id="proofcontrol8" class="togglescript"
onclick="toggleDisplay('proof8');toggleDisplay('proofcontrol8')">

<span class="show"></span>

</div>

<div id="proof8" class="proofscript"
onclick="toggleDisplay('proof8');toggleDisplay('proofcontrol8')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">normal\_form</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">v</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">contra</span>. <span class="id"
type="tactic">inversion</span> <span class="id"
type="var">contra</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H1</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">nf\_is\_value</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>,\
   <span class="id" type="var">normal\_form</span> <span class="id"
type="var">step</span> <span class="id" type="var">t</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">value</span> <span class="id" type="var">t</span>.\
<div id="proofcontrol9" class="togglescript"
onclick="toggleDisplay('proof9');toggleDisplay('proofcontrol9')">

<span class="show"></span>

</div>

<div id="proof9" class="proofscript"
onclick="toggleDisplay('proof9');toggleDisplay('proofcontrol9')"
style="display: none;">

<span class="id" type="keyword">Proof</span>. <span
class="comment">(\* a corollary of <span class="inlinecode"><span
class="id" type="var">strong\_progress</span></span>... \*)</span>\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">normal\_form</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">t</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">G</span> : <span class="id" type="var">value</span> <span
class="id" type="var">t</span> <span
style="font-family: arial;">∨</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>, <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span>).\
     <span class="id" type="var">SCase</span> "Proof of assertion".
<span class="id" type="tactic">apply</span> <span class="id"
type="var">strong\_progress</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">G</span>.\
     <span class="id" type="var">SCase</span> "l". <span class="id"
type="tactic">apply</span> <span class="id" type="var">H0</span>.\
     <span class="id" type="var">SCase</span> "r". <span class="id"
type="tactic">apply</span> <span class="id"
type="var">ex\_falso\_quodlibet</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">assumption</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Corollary</span> <span class="id"
type="var">nf\_same\_as\_value</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>,\
   <span class="id" type="var">normal\_form</span> <span class="id"
type="var">step</span> <span class="id" type="var">t</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">value</span> <span class="id" type="var">t</span>.\
<div id="proofcontrol10" class="togglescript"
onclick="toggleDisplay('proof10');toggleDisplay('proofcontrol10')">

<span class="show"></span>

</div>

<div id="proof10" class="proofscript"
onclick="toggleDisplay('proof10');toggleDisplay('proofcontrol10')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">nf\_is\_value</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">value\_is\_nf</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Why is this interesting?
<div class="paragraph">

</div>

Because <span class="inlinecode"><span class="id"
type="var">value</span></span> is a syntactic concept — it is defined by
looking at the form of a term — while <span class="inlinecode"><span
class="id" type="var">normal\_form</span></span> is a semantic one — it
is defined by looking at how the term steps. It is not obvious that
these concepts should coincide!
<div class="paragraph">

</div>

Indeed, we could easily have written the definitions so that they would
not coincide...

</div>

<div class="code code-tight">

\
\

</div>

<div class="doc">

We might, for example, mistakenly define <span class="inlinecode"><span
class="id" type="var">value</span></span> so that it includes some terms
that are not finished reducing.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Temp1</span>.\
 <span
class="comment">(\* Open an inner module so we can redefine value and step. \*)</span>\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">value</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
 | <span class="id" type="var">v\_const</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">value</span> (<span
class="id" type="var">C</span> <span class="id" type="var">n</span>)\
 | <span class="id" type="var">v\_funny</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">n2</span>, <span
class="comment">(\* \<---- \*)</span>\
               <span class="id" type="var">value</span> (<span
class="id" type="var">P</span> <span class="id" type="var">t~1~</span>
(<span class="id" type="var">C</span> <span class="id"
type="var">n2</span>)).\
\
 <span class="id" type="keyword">Reserved Notation</span> " t '<span
style="font-family: arial;">⇒</span>' t' " (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">step</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">ST\_PlusConstConst</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">n2</span>,\
       <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">C</span> <span class="id" type="var">n2</span>)
<span style="font-family: arial;">⇒</span> <span class="id"
type="var">C</span> (<span class="id" type="var">n1</span> + <span
class="id" type="var">n2</span>)\
   | <span class="id" type="var">ST\_Plus1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
       <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">P</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">P</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>\
   | <span class="id" type="var">ST\_Plus2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
       <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">P</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">P</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>\
\
   <span class="id" type="keyword">where</span> " t '<span
style="font-family: arial;">⇒</span>' t' " := (<span class="id"
type="var">step</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span>).\
\

</div>

<div class="doc">

#### Exercise: 3 stars, advanced (value\_not\_same\_as\_normal\_form) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">value\_not\_same\_as\_normal\_form</span> :\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">v</span>, <span class="id" type="var">value</span> <span
class="id" type="var">v</span> <span
style="font-family: arial;">∧</span> ¬ <span class="id"
type="var">normal\_form</span> <span class="id" type="var">step</span>
<span class="id" type="var">v</span>.\
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

Alternatively, we might mistakenly define <span class="inlinecode"><span
class="id" type="var">step</span></span> so that it permits something
designated as a value to reduce further.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Temp2</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">value</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
 | <span class="id" type="var">v\_const</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">value</span> (<span
class="id" type="var">C</span> <span class="id" type="var">n</span>).\
\
 <span class="id" type="keyword">Reserved Notation</span> " t '<span
style="font-family: arial;">⇒</span>' t' " (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">step</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">ST\_Funny</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="comment">(\* \<---- \*)</span>\
       <span class="id" type="var">C</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">P</span> (<span class="id" type="var">C</span>
<span class="id" type="var">n</span>) (<span class="id"
type="var">C</span> 0)\
   | <span class="id" type="var">ST\_PlusConstConst</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">n2</span>,\
       <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">C</span> <span class="id" type="var">n2</span>)
<span style="font-family: arial;">⇒</span> <span class="id"
type="var">C</span> (<span class="id" type="var">n1</span> + <span
class="id" type="var">n2</span>)\
   | <span class="id" type="var">ST\_Plus1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
       <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">P</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">P</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>\
   | <span class="id" type="var">ST\_Plus2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
       <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">P</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">P</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>\
\
   <span class="id" type="keyword">where</span> " t '<span
style="font-family: arial;">⇒</span>' t' " := (<span class="id"
type="var">step</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span>).\
\

</div>

<div class="doc">

#### Exercise: 2 stars, advanced (value\_not\_same\_as\_normal\_form) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">value\_not\_same\_as\_normal\_form</span> :\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">v</span>, <span class="id" type="var">value</span> <span
class="id" type="var">v</span> <span
style="font-family: arial;">∧</span> ¬ <span class="id"
type="var">normal\_form</span> <span class="id" type="var">step</span>
<span class="id" type="var">v</span>.\
<div id="proofcontrol11" class="togglescript"
onclick="toggleDisplay('proof11');toggleDisplay('proofcontrol11')">

<span class="show"></span>

</div>

<div id="proof11" class="proofscript"
onclick="toggleDisplay('proof11');toggleDisplay('proofcontrol11')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Finally, we might define <span class="inlinecode"><span class="id"
type="var">value</span></span> and <span class="inlinecode"><span
class="id" type="var">step</span></span> so that there is some term that
is not a value but that cannot take a step in the <span
class="inlinecode"><span class="id" type="var">step</span></span>
relation. Such terms are said to be *stuck*. In this case this is caused
by a mistake in the semantics, but we will also see situations where,
even in a correct language definition, it makes sense to allow some
terms to be stuck.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Temp3</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">value</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">v\_const</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">value</span> (<span
class="id" type="var">C</span> <span class="id" type="var">n</span>).\
\
 <span class="id" type="keyword">Reserved Notation</span> " t '<span
style="font-family: arial;">⇒</span>' t' " (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">step</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">ST\_PlusConstConst</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">n2</span>,\
       <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">C</span> <span class="id" type="var">n2</span>)
<span style="font-family: arial;">⇒</span> <span class="id"
type="var">C</span> (<span class="id" type="var">n1</span> + <span
class="id" type="var">n2</span>)\
   | <span class="id" type="var">ST\_Plus1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
       <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">P</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">P</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>\
\
   <span class="id" type="keyword">where</span> " t '<span
style="font-family: arial;">⇒</span>' t' " := (<span class="id"
type="var">step</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span>).\
\

</div>

<div class="doc">

(Note that <span class="inlinecode"><span class="id"
type="var">ST\_Plus2</span></span> is missing.)
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (value\_not\_same\_as\_normal\_form') {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">value\_not\_same\_as\_normal\_form</span> :\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">t</span>, ¬ <span class="id" type="var">value</span> <span
class="id" type="var">t</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">normal\_form</span> <span class="id" type="var">step</span>
<span class="id" type="var">t</span>.\
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
type="var">Temp3</span>.\
\

</div>

<div class="doc">

### Additional Exercises {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Temp4</span>.\
\

</div>

<div class="doc">

Here is another very simple language whose terms, instead of being just
plus and numbers, are just the booleans true and false and a conditional
expression...

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
class="id" type="var">tm</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">value</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">v\_true</span> : <span class="id"
type="var">value</span> <span class="id" type="var">ttrue</span>\
   | <span class="id" type="var">v\_false</span> : <span class="id"
type="var">value</span> <span class="id" type="var">tfalse</span>.\
\
 <span class="id" type="keyword">Reserved Notation</span> " t '<span
style="font-family: arial;">⇒</span>' t' " (<span class="id"
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
       <span class="id" type="var">tif</span> <span class="id"
type="var">ttrue</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~</span>\
   | <span class="id" type="var">ST\_IfFalse</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span class="id" type="var">tif</span> <span class="id"
type="var">tfalse</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span
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
       <span class="id" type="var">tif</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tif</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>\
\
   <span class="id" type="keyword">where</span> " t '<span
style="font-family: arial;">⇒</span>' t' " := (<span class="id"
type="var">step</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span>).\
\

</div>

<div class="doc">

#### Exercise: 1 star (smallstep\_bools) {.section}

Which of the following propositions are provable? (This is just a
thought exercise, but for an extra challenge feel free to prove your
answers in Coq.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">bool\_step\_prop1</span> :=\
   <span class="id" type="var">tfalse</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tfalse</span>.\
\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">bool\_step\_prop2</span> :=\
      <span class="id" type="var">tif</span>\
        <span class="id" type="var">ttrue</span>\
        (<span class="id" type="var">tif</span> <span class="id"
type="var">ttrue</span> <span class="id" type="var">ttrue</span> <span
class="id" type="var">ttrue</span>)\
        (<span class="id" type="var">tif</span> <span class="id"
type="var">tfalse</span> <span class="id" type="var">tfalse</span> <span
class="id" type="var">tfalse</span>)\
   <span style="font-family: arial;">⇒</span>\
      <span class="id" type="var">ttrue</span>.\
\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">bool\_step\_prop3</span> :=\
      <span class="id" type="var">tif</span>\
        (<span class="id" type="var">tif</span> <span class="id"
type="var">ttrue</span> <span class="id" type="var">ttrue</span> <span
class="id" type="var">ttrue</span>)\
        (<span class="id" type="var">tif</span> <span class="id"
type="var">ttrue</span> <span class="id" type="var">ttrue</span> <span
class="id" type="var">ttrue</span>)\
        <span class="id" type="var">tfalse</span>\
    <span style="font-family: arial;">⇒</span>\
      <span class="id" type="var">tif</span>\
        <span class="id" type="var">ttrue</span>\
        (<span class="id" type="var">tif</span> <span class="id"
type="var">ttrue</span> <span class="id" type="var">ttrue</span> <span
class="id" type="var">ttrue</span>)\
        <span class="id" type="var">tfalse</span>.\
\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (progress\_bool) {.section}

Just as we proved a progress theorem for plus expressions, we can do so
for boolean expressions, as well.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">strong\_progress</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t</span>,\
   <span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">∨</span> (<span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>, <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (step\_deterministic) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">step\_deterministic</span> :\
   <span class="id" type="var">deterministic</span> <span class="id"
type="var">step</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Temp5</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (smallstep\_bool\_shortcut) {.section}

Suppose we want to add a "short circuit" to the step relation for
boolean expressions, so that it can recognize when the <span
class="inlinecode"><span class="id" type="keyword">then</span></span>
and <span class="inlinecode"><span class="id"
type="keyword">else</span></span> branches of a conditional are the same
value (either <span class="inlinecode"><span class="id"
type="var">ttrue</span></span> or <span class="inlinecode"><span
class="id" type="var">tfalse</span></span>) and reduce the whole
conditional to this value in a single step, even if the guard has not
yet been reduced to a value. For example, we would like this proposition
to be provable:
<div class="paragraph">

</div>

<div class="code code-tight">

         <span class="id" type="var">tif</span>\
             (<span class="id" type="var">tif</span> <span class="id"
type="var">ttrue</span> <span class="id" type="var">ttrue</span> <span
class="id" type="var">ttrue</span>)\
             <span class="id" type="var">tfalse</span>\
             <span class="id" type="var">tfalse</span>\
      <span style="font-family: arial;">⇒</span> \
          <span class="id" type="var">tfalse</span>.
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Write an extra clause for the step relation that achieves this effect
and prove <span class="inlinecode"><span class="id"
type="var">bool\_step\_prop4</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> " t '<span
style="font-family: arial;">⇒</span>' t' " (<span class="id"
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
       <span class="id" type="var">tif</span> <span class="id"
type="var">ttrue</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~</span>\
   | <span class="id" type="var">ST\_IfFalse</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span class="id" type="var">tif</span> <span class="id"
type="var">tfalse</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span
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
       <span class="id" type="var">tif</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tif</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\
   <span class="id" type="keyword">where</span> " t '<span
style="font-family: arial;">⇒</span>' t' " := (<span class="id"
type="var">step</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span>).\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">bool\_step\_prop4</span> :=\
          <span class="id" type="var">tif</span>\
             (<span class="id" type="var">tif</span> <span class="id"
type="var">ttrue</span> <span class="id" type="var">ttrue</span> <span
class="id" type="var">ttrue</span>)\
             <span class="id" type="var">tfalse</span>\
             <span class="id" type="var">tfalse</span>\
      <span style="font-family: arial;">⇒</span>\
          <span class="id" type="var">tfalse</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">bool\_step\_prop4\_holds</span> :\
   <span class="id" type="var">bool\_step\_prop4</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (properties\_of\_altered\_step) {.section}

It can be shown that the determinism and strong progress theorems for
the step relation in the lecture notes also hold for the definition of
step given above. After we add the clause <span class="inlinecode"><span
class="id" type="var">ST\_ShortCircuit</span></span>...
<div class="paragraph">

</div>

-   Is the <span class="inlinecode"><span class="id"
    type="var">step</span></span> relation still deterministic? Write
    yes or no and briefly (1 sentence) explain your answer.
    <div class="paragraph">

    </div>

    Optional: prove your answer correct in Coq.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

<div class="paragraph">

</div>

-   Does a strong progress theorem hold? Write yes or no and briefly (1
    sentence) explain your answer.
    <div class="paragraph">

    </div>

    Optional: prove your answer correct in Coq.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

<div class="paragraph">

</div>

-   In general, is there any way we could cause strong progress to fail
    if we took away one or more constructors from the original step
    relation? Write yes or no and briefly (1 sentence) explain your
    answer.

<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Temp5</span>.\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Temp4</span>.\
\

</div>

<div class="doc">

Multi-Step Reduction {.section}
====================

<div class="paragraph">

</div>

Until now, we've been working with the *single-step reduction* relation
<span class="inlinecode"><span
style="font-family: arial;">⇒</span></span>, which formalizes the
individual steps of an *abstract machine* for executing programs.
<div class="paragraph">

</div>

We can also use this machine to reduce programs to completion — to find
out what final result they yield. This can be formalized as follows:
<div class="paragraph">

</div>

-   First, we define a *multi-step reduction relation* <span
    class="inlinecode"><span
    style="font-family: arial;">⇒\*</span></span>, which relates terms
    <span class="inlinecode"><span class="id" type="var">t</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">t'</span></span> if <span class="inlinecode"><span
    class="id" type="var">t</span></span> can reach <span
    class="inlinecode"><span class="id" type="var">t'</span></span> by
    any number of single reduction steps (including zero steps!).
    <div class="paragraph">

    </div>

-   Then we define a "result" of a term <span class="inlinecode"><span
    class="id" type="var">t</span></span> as a normal form that <span
    class="inlinecode"><span class="id" type="var">t</span></span> can
    reach by multi-step reduction.

</div>

<div class="code code-tight">

\
\

</div>

<div class="doc">

Since we'll want to reuse the idea of multi-step reduction many times in
this and future chapters, let's take a little extra trouble here and
define it generically.
<div class="paragraph">

</div>

Given a relation <span class="inlinecode"><span class="id"
type="var">R</span></span>, we define a relation <span
class="inlinecode"><span class="id" type="var">multi</span></span> <span
class="inlinecode"><span class="id" type="var">R</span></span>, called
the *multi-step closure of <span class="inlinecode"><span class="id"
type="var">R</span></span>* as follows:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">multi</span> {<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">R</span>: <span class="id" type="var">relation</span> <span
class="id" type="var">X</span>) : <span class="id"
type="var">relation</span> <span class="id" type="var">X</span> :=\
   | <span class="id" type="var">multi\_refl</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> : <span class="id" type="var">X</span>), <span
class="id" type="var">multi</span> <span class="id" type="var">R</span>
<span class="id" type="var">x</span> <span class="id"
type="var">x</span>\
   | <span class="id" type="var">multi\_step</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span> : <span class="id" type="var">X</span>),\
                     <span class="id" type="var">R</span> <span
class="id" type="var">x</span> <span class="id" type="var">y</span>
<span style="font-family: arial;">→</span>\
                     <span class="id" type="var">multi</span> <span
class="id" type="var">R</span> <span class="id" type="var">y</span>
<span class="id" type="var">z</span> <span
style="font-family: arial;">→</span>\
                     <span class="id" type="var">multi</span> <span
class="id" type="var">R</span> <span class="id" type="var">x</span>
<span class="id" type="var">z</span>.\
\

</div>

<div class="doc">

The effect of this definition is that <span class="inlinecode"><span
class="id" type="var">multi</span></span> <span class="inlinecode"><span
class="id" type="var">R</span></span> relates two elements <span
class="inlinecode"><span class="id" type="var">x</span></span> and <span
class="inlinecode"><span class="id" type="var">y</span></span> if either
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">x</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">y</span></span>, or else
-   there is some sequence <span class="inlinecode"><span class="id"
    type="var">z1</span></span>, <span class="inlinecode"><span
    class="id" type="var">z2</span></span>, ..., <span
    class="inlinecode"><span class="id" type="var">zn</span></span> such
    that
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">R</span> <span class="id"
    type="var">x</span> <span class="id" type="var">z1</span>\
       <span class="id" type="var">R</span> <span class="id"
    type="var">z1</span> <span class="id" type="var">z2</span>\
       ...\
       <span class="id" type="var">R</span> <span class="id"
    type="var">zn</span> <span class="id" type="var">y</span>.
    <div class="paragraph">

    </div>

    </div>

<div class="paragraph">

</div>

Thus, if <span class="inlinecode"><span class="id"
type="var">R</span></span> describes a single-step of computation, <span
class="inlinecode"><span class="id" type="var">z1</span></span>, ...
<span class="inlinecode"><span class="id" type="var">zn</span></span> is
the sequence of intermediate steps of computation between <span
class="inlinecode"><span class="id" type="var">x</span></span> and <span
class="inlinecode"><span class="id" type="var">y</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Tactic Notation</span> "multi\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "multi\_refl" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"multi\_step" ].\
\

</div>

<div class="doc">

We write <span class="inlinecode"><span
style="font-family: arial;">⇒\*</span></span> for the <span
class="inlinecode"><span class="id" type="var">multi</span></span> <span
class="inlinecode"><span class="id" type="var">step</span></span>
relation — i.e., the relation that relates two terms <span
class="inlinecode"><span class="id" type="var">t</span></span> and <span
class="inlinecode"><span class="id" type="var">t'</span></span> if we
can get from <span class="inlinecode"><span class="id"
type="var">t</span></span> to <span class="inlinecode"><span class="id"
type="var">t'</span></span> using the <span class="inlinecode"><span
class="id" type="var">step</span></span> relation zero or more times.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> " t '<span
style="font-family: arial;">⇒\*</span>' t' " := (<span class="id"
type="var">multi</span> <span class="id" type="var">step</span> <span
class="id" type="var">t</span> <span class="id" type="var">t'</span>)
(<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 40).\
\

</div>

<div class="doc">

The relation <span class="inlinecode"><span class="id"
type="var">multi</span></span> <span class="inlinecode"><span class="id"
type="var">R</span></span> has several crucial properties.
<div class="paragraph">

</div>

First, it is obviously *reflexive* (that is, <span
class="inlinecode"><span style="font-family: arial;">∀</span></span>
<span class="inlinecode"><span class="id" type="var">x</span>,</span>
<span class="inlinecode"><span class="id" type="var">multi</span></span>
<span class="inlinecode"><span class="id" type="var">R</span></span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode"><span class="id" type="var">x</span></span>).
In the case of the <span class="inlinecode"><span
style="font-family: arial;">⇒\*</span></span> (i.e. <span
class="inlinecode"><span class="id" type="var">multi</span></span> <span
class="inlinecode"><span class="id" type="var">step</span></span>)
relation, the intuition is that a term can execute to itself by taking
zero steps of execution.
<div class="paragraph">

</div>

Second, it contains <span class="inlinecode"><span class="id"
type="var">R</span></span> — that is, single-step executions are a
particular case of multi-step executions. (It is this fact that
justifies the word "closure" in the term "multi-step closure of <span
class="inlinecode"><span class="id" type="var">R</span></span>.")

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">multi\_R</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">R</span>:<span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">x</span> <span class="id" type="var">y</span> :
<span class="id" type="var">X</span>),\
        <span class="id" type="var">R</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
style="font-family: arial;">→</span> (<span class="id"
type="var">multi</span> <span class="id" type="var">R</span>) <span
class="id" type="var">x</span> <span class="id" type="var">y</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">X</span> <span class="id" type="var">R</span> <span
class="id" type="var">x</span> <span class="id" type="var">y</span>
<span class="id" type="var">H</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_step</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">y</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">multi\_refl</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Third, <span class="inlinecode"><span class="id"
type="var">multi</span></span> <span class="inlinecode"><span class="id"
type="var">R</span></span> is *transitive*.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">multi\_trans</span> :\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">R</span>: <span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">x</span> <span class="id" type="var">y</span>
<span class="id" type="var">z</span> : <span class="id"
type="var">X</span>),\
       <span class="id" type="var">multi</span> <span class="id"
type="var">R</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">multi</span> <span class="id"
type="var">R</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">multi</span> <span class="id"
type="var">R</span> <span class="id" type="var">x</span> <span
class="id" type="var">z</span>.\
<div id="proofcontrol12" class="togglescript"
onclick="toggleDisplay('proof12');toggleDisplay('proofcontrol12')">

<span class="show"></span>

</div>

<div id="proof12" class="proofscript"
onclick="toggleDisplay('proof12');toggleDisplay('proofcontrol12')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">X</span> <span class="id" type="var">R</span> <span
class="id" type="var">x</span> <span class="id" type="var">y</span>
<span class="id" type="var">z</span> <span class="id"
type="var">G</span> <span class="id" type="var">H</span>.\
   <span class="id" type="var">multi\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">G</span>)
<span class="id" type="var">Case</span>.\
     <span class="id" type="var">Case</span> "multi\_refl". <span
class="id" type="tactic">assumption</span>.\
     <span class="id" type="var">Case</span> "multi\_step".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_step</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">y</span>. <span
class="id" type="tactic">assumption</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHG</span>. <span class="id" type="tactic">assumption</span>.
<span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

That is, if <span class="inlinecode"><span class="id"
type="var">t~1~</span><span style="font-family: arial;">⇒\*</span><span
class="id" type="var">t~2~</span></span> and <span
class="inlinecode"><span class="id" type="var">t~2~</span><span
style="font-family: arial;">⇒\*</span><span class="id"
type="var">t~3~</span></span>, then <span class="inlinecode"><span
class="id" type="var">t~1~</span><span
style="font-family: arial;">⇒\*</span><span class="id"
type="var">t~3~</span></span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Examples {.section}
--------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">test\_multistep\_1</span>:\
       <span class="id" type="var">P</span>\
         (<span class="id" type="var">P</span> (<span class="id"
type="var">C</span> 0) (<span class="id" type="var">C</span> 3))\
         (<span class="id" type="var">P</span> (<span class="id"
type="var">C</span> 2) (<span class="id" type="var">C</span> 4))\
    <span style="font-family: arial;">⇒\*</span>\
       <span class="id" type="var">C</span> ((0 + 3) + (2 + 4)).\
<div id="proofcontrol13" class="togglescript"
onclick="toggleDisplay('proof13');toggleDisplay('proofcontrol13')">

<span class="show"></span>

</div>

<div id="proof13" class="proofscript"
onclick="toggleDisplay('proof13');toggleDisplay('proofcontrol13')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_step</span> <span class="id"
type="keyword">with</span>\
             (<span class="id" type="var">P</span>\
                 (<span class="id" type="var">C</span> (0 + 3))\
                 (<span class="id" type="var">P</span> (<span class="id"
type="var">C</span> 2) (<span class="id" type="var">C</span> 4))).\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_Plus1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">ST\_PlusConstConst</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_step</span> <span class="id"
type="keyword">with</span>\
             (<span class="id" type="var">P</span>\
                 (<span class="id" type="var">C</span> (0 + 3))\
                 (<span class="id" type="var">C</span> (2 + 4))).\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_Plus2</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">v\_const</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_PlusConstConst</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_R</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_PlusConstConst</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Here's an alternate proof that uses <span class="inlinecode"><span
class="id" type="tactic">eapply</span></span> to avoid explicitly
constructing all the intermediate terms.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">test\_multistep\_1'</span>:\
       <span class="id" type="var">P</span>\
         (<span class="id" type="var">P</span> (<span class="id"
type="var">C</span> 0) (<span class="id" type="var">C</span> 3))\
         (<span class="id" type="var">P</span> (<span class="id"
type="var">C</span> 2) (<span class="id" type="var">C</span> 4))\
   <span style="font-family: arial;">⇒\*</span>\
       <span class="id" type="var">C</span> ((0 + 3) + (2 + 4)).\
<div id="proofcontrol14" class="togglescript"
onclick="toggleDisplay('proof14');toggleDisplay('proofcontrol14')">

<span class="show"></span>

</div>

<div id="proof14" class="proofscript"
onclick="toggleDisplay('proof14');toggleDisplay('proofcontrol14')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">ST\_Plus1</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_PlusConstConst</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">ST\_Plus2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">v\_const</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_PlusConstConst</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">ST\_PlusConstConst</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 1 star, optional (test\_multistep\_2) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">test\_multistep\_2</span>:\
   <span class="id" type="var">C</span> 3 <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">C</span> 3.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (test\_multistep\_3) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">test\_multistep\_3</span>:\
       <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> 0) (<span class="id" type="var">C</span> 3)\
    <span style="font-family: arial;">⇒\*</span>\
       <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> 0) (<span class="id" type="var">C</span> 3).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (test\_multistep\_4) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">test\_multistep\_4</span>:\
       <span class="id" type="var">P</span>\
         (<span class="id" type="var">C</span> 0)\
         (<span class="id" type="var">P</span>\
           (<span class="id" type="var">C</span> 2)\
           (<span class="id" type="var">P</span> (<span class="id"
type="var">C</span> 0) (<span class="id" type="var">C</span> 3)))\
   <span style="font-family: arial;">⇒\*</span>\
       <span class="id" type="var">P</span>\
         (<span class="id" type="var">C</span> 0)\
         (<span class="id" type="var">C</span> (2 + (0 + 3))).\
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

Normal Forms Again {.section}
------------------

<div class="paragraph">

</div>

If <span class="inlinecode"><span class="id" type="var">t</span></span>
reduces to <span class="inlinecode"><span class="id"
type="var">t'</span></span> in zero or more steps and <span
class="inlinecode"><span class="id" type="var">t'</span></span> is a
normal form, we say that "<span class="inlinecode"><span class="id"
type="var">t'</span></span> is a normal form of <span
class="inlinecode"><span class="id" type="var">t</span></span>."

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">step\_normal\_form</span> := <span class="id"
type="var">normal\_form</span> <span class="id" type="var">step</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">normal\_form\_of</span> (<span class="id" type="var">t</span>
<span class="id" type="var">t'</span> : <span class="id"
type="var">tm</span>) :=\
   (<span class="id" type="var">t</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">t'</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">step\_normal\_form</span> <span class="id"
type="var">t'</span>).\
\

</div>

<div class="doc">

We have already seen that, for our language, single-step reduction is
deterministic — i.e., a given term can take a single step in at most one
way. It follows from this that, if <span class="inlinecode"><span
class="id" type="var">t</span></span> can reach a normal form, then this
normal form is unique. In other words, we can actually pronounce <span
class="inlinecode"><span class="id"
type="var">normal\_form</span></span> <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
class="id" type="var">t'</span></span> as "<span
class="inlinecode"><span class="id" type="var">t'</span></span> is *the*
normal form of <span class="inlinecode"><span class="id"
type="var">t</span></span>."
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (normal\_forms\_unique) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">normal\_forms\_unique</span>:\
   <span class="id" type="var">deterministic</span> <span class="id"
type="var">normal\_form\_of</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">deterministic</span>. <span class="id"
type="tactic">unfold</span> <span class="id"
type="var">normal\_form\_of</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">x</span> <span
class="id" type="var">y1</span> <span class="id" type="var">y2</span>
<span class="id" type="var">P1</span> <span class="id"
type="var">P2</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">P1</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">P11</span> <span class="id"
type="var">P12</span>]; <span class="id" type="tactic">clear</span>
<span class="id" type="var">P1</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">P2</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">P21</span> <span class="id" type="var">P22</span>]; <span
class="id" type="tactic">clear</span> <span class="id"
type="var">P2</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">y2</span>.\
   <span
class="comment">(\* We recommend using this initial setup as-is! \*)</span>\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Indeed, something stronger is true for this language (though not for all
languages): the reduction of *any* term <span class="inlinecode"><span
class="id" type="var">t</span></span> will eventually reach a normal
form — i.e., <span class="inlinecode"><span class="id"
type="var">normal\_form\_of</span></span> is a *total* function.
Formally, we say the <span class="inlinecode"><span class="id"
type="var">step</span></span> relation is *normalizing*.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">normalizing</span> {<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>} (<span
class="id" type="var">R</span>:<span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">t</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">t'</span>,\
     (<span class="id" type="var">multi</span> <span class="id"
type="var">R</span>) <span class="id" type="var">t</span> <span
class="id" type="var">t'</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">normal\_form</span> <span class="id" type="var">R</span>
<span class="id" type="var">t'</span>.\
\

</div>

<div class="doc">

To prove that <span class="inlinecode"><span class="id"
type="var">step</span></span> is normalizing, we need a couple of
lemmas.
<div class="paragraph">

</div>

First, we observe that, if <span class="inlinecode"><span class="id"
type="var">t</span></span> reduces to <span class="inlinecode"><span
class="id" type="var">t'</span></span> in many steps, then the same
sequence of reduction steps within <span class="inlinecode"><span
class="id" type="var">t</span></span> is also possible when <span
class="inlinecode"><span class="id" type="var">t</span></span> appears
as the left-hand child of a <span class="inlinecode"><span class="id"
type="var">P</span></span> node, and similarly when <span
class="inlinecode"><span class="id" type="var">t</span></span> appears
as the right-hand child of a <span class="inlinecode"><span class="id"
type="var">P</span></span> node whose left-hand child is a value.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">multistep\_congr\_1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
      <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">P</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">P</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>.\
<div id="proofcontrol15" class="togglescript"
onclick="toggleDisplay('proof15');toggleDisplay('proofcontrol15')">

<span class="show"></span>

</div>

<div id="proof15" class="proofscript"
onclick="toggleDisplay('proof15');toggleDisplay('proofcontrol15')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">H</span>.
<span class="id" type="var">multi\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>)
<span class="id" type="var">Case</span>.\
     <span class="id" type="var">Case</span> "multi\_refl". <span
class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>.\
     <span class="id" type="var">Case</span> "multi\_step". <span
class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_step</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">P</span> <span
class="id" type="var">y</span> <span class="id"
type="var">t~2~</span>).\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_Plus1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">H</span>.\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHmulti</span>. <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 2 stars (multistep\_congr\_2) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">multistep\_congr\_2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
      <span class="id" type="var">value</span> <span class="id"
type="var">t~1~</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">P</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">P</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~'</span>.\
<div id="proofcontrol16" class="togglescript"
onclick="toggleDisplay('proof16');toggleDisplay('proofcontrol16')">

<span class="show"></span>

</div>

<div id="proof16" class="proofscript"
onclick="toggleDisplay('proof16');toggleDisplay('proofcontrol16')"
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

*Theorem*: The <span class="inlinecode"><span class="id"
type="var">step</span></span> function is normalizing — i.e., for every
<span class="inlinecode"><span class="id" type="var">t</span></span>
there exists some <span class="inlinecode"><span class="id"
type="var">t'</span></span> such that <span class="inlinecode"><span
class="id" type="var">t</span></span> steps to <span
class="inlinecode"><span class="id" type="var">t'</span></span> and
<span class="inlinecode"><span class="id" type="var">t'</span></span> is
a normal form.
<div class="paragraph">

</div>

*Proof sketch*: By induction on terms. There are two cases to consider:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">t</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">C</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> for some <span
    class="inlinecode"><span class="id" type="var">n</span></span>. Here
    <span class="inlinecode"><span class="id" type="var">t</span></span>
    doesn't take a step, and we have <span class="inlinecode"><span
    class="id" type="var">t'</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">t</span></span>. We can derive the left-hand
    side by reflexivity and the right-hand side by observing (a) that
    values are normal forms (by <span class="inlinecode"><span
    class="id" type="var">nf\_same\_as\_value</span></span>) and (b)
    that <span class="inlinecode"><span class="id"
    type="var">t</span></span> is a value (by <span
    class="inlinecode"><span class="id"
    type="var">v\_const</span></span>).
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id" type="var">t</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">P</span></span> <span class="inlinecode"><span
    class="id" type="var">t~1~</span></span> <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span>
    for some <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> and <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span>. By the IH, <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> have normal forms <span
    class="inlinecode"><span class="id" type="var">t~1~'</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">t~2~'</span></span>. Recall that normal forms are values
    (by <span class="inlinecode"><span class="id"
    type="var">nf\_same\_as\_value</span></span>); we know that <span
    class="inlinecode"><span class="id" type="var">t~1~'</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">C</span></span> <span class="inlinecode"><span
    class="id" type="var">n1</span></span> and <span
    class="inlinecode"><span class="id" type="var">t~2~'</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">C</span></span> <span class="inlinecode"><span
    class="id" type="var">n2</span></span>, for some <span
    class="inlinecode"><span class="id" type="var">n1</span></span> and
    <span class="inlinecode"><span class="id"
    type="var">n2</span></span>. We can combine the <span
    class="inlinecode"><span
    style="font-family: arial;">⇒\*</span></span> derivations for <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> to prove that <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> reduces in many steps to <span
    class="inlinecode"><span class="id" type="var">C</span></span> <span
    class="inlinecode">(<span class="id" type="var">n1</span></span>
    <span class="inlinecode">+</span> <span class="inlinecode"><span
    class="id" type="var">n2</span>)</span>.
    <div class="paragraph">

    </div>

    It is clear that our choice of <span class="inlinecode"><span
    class="id" type="var">t'</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">C</span></span> <span
    class="inlinecode">(<span class="id" type="var">n1</span></span>
    <span class="inlinecode">+</span> <span class="inlinecode"><span
    class="id" type="var">n2</span>)</span> is a value, which is in turn
    a normal form. ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">step\_normalizing</span> :\
   <span class="id" type="var">normalizing</span> <span class="id"
type="var">step</span>.\
<div id="proofcontrol17" class="togglescript"
onclick="toggleDisplay('proof17');toggleDisplay('proofcontrol17')">

<span class="show"></span>

</div>

<div id="proof17" class="proofscript"
onclick="toggleDisplay('proof17');toggleDisplay('proofcontrol17')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">normalizing</span>.\
   <span class="id" type="var">tm\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">t</span>)
<span class="id" type="var">Case</span>.\
     <span class="id" type="var">Case</span> "C".\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">C</span> <span class="id" type="var">n</span>).\
       <span class="id" type="tactic">split</span>.\
       <span class="id" type="var">SCase</span> "l". <span class="id"
type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>.\
       <span class="id" type="var">SCase</span> "r".\
         <span class="comment">(\* We can use <span
class="inlinecode"><span class="id"
type="tactic">rewrite</span></span> with "iff" statements, not\
            just equalities: \*)</span>\
         <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">nf\_same\_as\_value</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">v\_const</span>.\
     <span class="id" type="var">Case</span> "P".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">IHt1</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">H1</span>]; <span class="id" type="tactic">clear</span> <span
class="id" type="var">IHt1</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">IHt2</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">t~2~'</span> <span class="id" type="var">H2</span>]; <span
class="id" type="tactic">clear</span> <span class="id"
type="var">IHt2</span>.\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H1</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">H11</span> <span class="id"
type="var">H12</span>]; <span class="id" type="tactic">clear</span>
<span class="id" type="var">H1</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H2</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">H21</span> <span class="id" type="var">H22</span>]; <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H2</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">nf\_same\_as\_value</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H12</span>. <span
class="id" type="tactic">rewrite</span> <span class="id"
type="var">nf\_same\_as\_value</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H22</span>.\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H12</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">n1</span>]. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H22</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">n2</span>].\
       <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H11</span>.\
       <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H21</span>.\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">C</span> (<span class="id" type="var">n1</span> + <span
class="id" type="var">n2</span>)).\
       <span class="id" type="tactic">split</span>.\
         <span class="id" type="var">SCase</span> "l".\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_trans</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">P</span> (<span
class="id" type="var">C</span> <span class="id" type="var">n1</span>)
<span class="id" type="var">t~2~</span>).\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">multistep\_congr\_1</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H11</span>.\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_trans</span> <span class="id"
type="keyword">with</span>\
              (<span class="id" type="var">P</span> (<span class="id"
type="var">C</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">C</span> <span class="id" type="var">n2</span>)).\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">multistep\_congr\_2</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">v\_const</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">H21</span>.\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_R</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">ST\_PlusConstConst</span>.\
         <span class="id" type="var">SCase</span> "r".\
           <span class="id" type="tactic">rewrite</span> <span
class="id" type="var">nf\_same\_as\_value</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">v\_const</span>.
<span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Equivalence of Big-Step and Small-Step Reduction {.section}
------------------------------------------------

<div class="paragraph">

</div>

Having defined the operational semantics of our tiny programming
language in two different styles, it makes sense to ask whether these
definitions actually define the same thing! They do, though it takes a
little work to show it. (The details are left as an exercise).
<div class="paragraph">

</div>

#### Exercise: 3 stars (eval\_\_multistep) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">eval\_\_multistep</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">n</span>,\
   <span class="id" type="var">t</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">t</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">C</span> <span class="id" type="var">n</span>.\
\

</div>

<div class="doc">

The key idea behind the proof comes from the following picture:
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="var">P</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span>            (<span class="id"
type="tactic">by</span> <span class="id" type="var">ST\_Plus1</span>) \
        <span class="id" type="var">P</span> <span class="id"
type="var">t~1~'</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span>           (<span class="id"
type="tactic">by</span> <span class="id" type="var">ST\_Plus1</span>)  \
        <span class="id" type="var">P</span> <span class="id"
type="var">t~1~''</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span>          (<span class="id"
type="tactic">by</span> <span class="id" type="var">ST\_Plus1</span>) \
        ...\
        <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> <span class="id" type="var">n1</span>) <span
class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span>        (<span class="id"
type="tactic">by</span> <span class="id" type="var">ST\_Plus2</span>)\
        <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> <span class="id" type="var">n1</span>) <span
class="id" type="var">t~2~'</span> <span
style="font-family: arial;">⇒</span>       (<span class="id"
type="tactic">by</span> <span class="id" type="var">ST\_Plus2</span>)\
        <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> <span class="id" type="var">n1</span>) <span
class="id" type="var">t~2~''</span> <span
style="font-family: arial;">⇒</span>      (<span class="id"
type="tactic">by</span> <span class="id" type="var">ST\_Plus2</span>)\
        ...\
        <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">C</span> <span class="id"
type="var">n2</span>) <span
style="font-family: arial;">⇒</span>    (<span class="id"
type="tactic">by</span> <span class="id"
type="var">ST\_PlusConstConst</span>)\
        <span class="id" type="var">C</span> (<span class="id"
type="var">n1</span> + <span class="id"
type="var">n2</span>)              
<div class="paragraph">

</div>

</div>

That is, the multistep reduction of a term of the form <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> <span
class="inlinecode"><span class="id" type="var">t~2~</span></span>
proceeds in three phases:
<div class="paragraph">

</div>

-   First, we use <span class="inlinecode"><span class="id"
    type="var">ST\_Plus1</span></span> some number of times to reduce
    <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> to a normal form, which must (by <span
    class="inlinecode"><span class="id"
    type="var">nf\_same\_as\_value</span></span>) be a term of the form
    <span class="inlinecode"><span class="id" type="var">C</span></span>
    <span class="inlinecode"><span class="id"
    type="var">n1</span></span> for some <span class="inlinecode"><span
    class="id" type="var">n1</span></span>.
-   Next, we use <span class="inlinecode"><span class="id"
    type="var">ST\_Plus2</span></span> some number of times to reduce
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> to a normal form, which must again be
    a term of the form <span class="inlinecode"><span class="id"
    type="var">C</span></span> <span class="inlinecode"><span class="id"
    type="var">n2</span></span> for some <span class="inlinecode"><span
    class="id" type="var">n2</span></span>.
-   Finally, we use <span class="inlinecode"><span class="id"
    type="var">ST\_PlusConstConst</span></span> one time to reduce <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode">(<span class="id" type="var">C</span></span>
    <span class="inlinecode"><span class="id"
    type="var">n1</span>)</span> <span class="inlinecode">(<span
    class="id" type="var">C</span></span> <span class="inlinecode"><span
    class="id" type="var">n2</span>)</span> to <span
    class="inlinecode"><span class="id" type="var">C</span></span> <span
    class="inlinecode">(<span class="id" type="var">n1</span></span>
    <span class="inlinecode">+</span> <span class="inlinecode"><span
    class="id" type="var">n2</span>)</span>.

<div class="paragraph">

</div>

To formalize this intuition, you'll need to use the congruence lemmas
from above (you might want to review them now, so that you'll be able to
recognize when they are useful), plus some basic properties of <span
class="inlinecode"><span style="font-family: arial;">⇒\*</span></span>:
that it is reflexive, transitive, and includes <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (eval\_\_multistep\_inf) {.section}

Write a detailed informal version of the proof of <span
class="inlinecode"><span class="id"
type="var">eval\_\_multistep</span></span>.
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐ For the other direction, we need one lemma, which establishes a
relation between single-step reduction and big-step evaluation.
<div class="paragraph">

</div>

#### Exercise: 3 stars (step\_\_eval) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_\_eval</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">t'</span> <span class="id"
type="var">n</span>,\
      <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">t'</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">t</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">t'</span> <span
class="id" type="var">n</span> <span class="id" type="var">Hs</span>.
<span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">n</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

The fact that small-step reduction implies big-step is now
straightforward to prove, once it is stated correctly.
<div class="paragraph">

</div>

The proof proceeds by induction on the multi-step reduction sequence
that is buried in the hypothesis <span class="inlinecode"><span
class="id" type="var">normal\_form\_of</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span>. Make
sure you understand the statement before you start to work on the proof.
<div class="paragraph">

</div>

#### Exercise: 3 stars (multistep\_\_eval) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">multistep\_\_eval</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">t'</span>,\
   <span class="id" type="var">normal\_form\_of</span> <span class="id"
type="var">t</span> <span class="id" type="var">t'</span> <span
style="font-family: arial;">→</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">n</span>, <span class="id" type="var">t'</span> = <span
class="id" type="var">C</span> <span class="id" type="var">n</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">n</span>.\
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

#### Exercise: 3 stars, optional (interp\_tm) {.section}

Remember that we also defined big-step evaluation of <span
class="inlinecode"><span class="id" type="var">tm</span></span>s as a
function <span class="inlinecode"><span class="id"
type="var">evalF</span></span>. Prove that it is equivalent to the
existing semantics.
<div class="paragraph">

</div>

Hint: we just proved that <span class="inlinecode"><span class="id"
type="var">eval</span></span> and <span class="inlinecode"><span
class="id" type="var">multistep</span></span> are equivalent, so
logically it doesn't matter which you choose. One will be easier than
the other, though!

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">evalF\_eval</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">n</span>,\
   <span class="id" type="var">evalF</span> <span class="id"
type="var">t</span> = <span class="id" type="var">n</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">n</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars (combined\_properties) {.section}

We've considered the arithmetic and conditional expressions separately.
This exercise explores how the two interact.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Combined</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">tm</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">C</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">P</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span>\
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
<div id="proofcontrol18" class="togglescript"
onclick="toggleDisplay('proof18');toggleDisplay('proofcontrol18')">

<span class="show"></span>

</div>

<div id="proof18" class="proofscript"
onclick="toggleDisplay('proof18');toggleDisplay('proofcontrol18')"
style="display: none;">

\
 <span class="id" type="keyword">Tactic Notation</span> "tm\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "C" | <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">c</span> "P"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ttrue" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"tfalse" | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tif" ].\

</div>

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">value</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">v\_const</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">value</span> (<span
class="id" type="var">C</span> <span class="id" type="var">n</span>)\
   | <span class="id" type="var">v\_true</span> : <span class="id"
type="var">value</span> <span class="id" type="var">ttrue</span>\
   | <span class="id" type="var">v\_false</span> : <span class="id"
type="var">value</span> <span class="id" type="var">tfalse</span>.\
\
 <span class="id" type="keyword">Reserved Notation</span> " t '<span
style="font-family: arial;">⇒</span>' t' " (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">step</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">ST\_PlusConstConst</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">n2</span>,\
       <span class="id" type="var">P</span> (<span class="id"
type="var">C</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">C</span> <span class="id" type="var">n2</span>)
<span style="font-family: arial;">⇒</span> <span class="id"
type="var">C</span> (<span class="id" type="var">n1</span> + <span
class="id" type="var">n2</span>)\
   | <span class="id" type="var">ST\_Plus1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>,\
       <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">P</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">P</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>\
   | <span class="id" type="var">ST\_Plus2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
       <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">P</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">P</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>\
   | <span class="id" type="var">ST\_IfTrue</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span class="id" type="var">tif</span> <span class="id"
type="var">ttrue</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~</span>\
   | <span class="id" type="var">ST\_IfFalse</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span class="id" type="var">tif</span> <span class="id"
type="var">tfalse</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span
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
       <span class="id" type="var">tif</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tif</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>\
\
   <span class="id" type="keyword">where</span> " t '<span
style="font-family: arial;">⇒</span>' t' " := (<span class="id"
type="var">step</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span>).\
<div id="proofcontrol19" class="togglescript"
onclick="toggleDisplay('proof19');toggleDisplay('proofcontrol19')">

<span class="show"></span>

</div>

<div id="proof19" class="proofscript"
onclick="toggleDisplay('proof19');toggleDisplay('proofcontrol19')"
style="display: none;">

\
 <span class="id" type="keyword">Tactic Notation</span> "step\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_PlusConstConst"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Plus1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Plus2"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_IfTrue" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_IfFalse" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "ST\_If" ].\

</div>

\

</div>

<div class="doc">

Earlier, we separately proved for both plus- and if-expressions...
<div class="paragraph">

</div>

-   that the step relation was deterministic, and
    <div class="paragraph">

    </div>

-   a strong progress lemma, stating that every term is either a value
    or can take a step.

Prove or disprove these two properties for the combined language.

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
type="var">Combined</span>.\
\

</div>

<div class="doc">

Small-Step Imp {.section}
==============

<div class="paragraph">

</div>

For a more serious example, here is the small-step version of the Imp
operational semantics.
<div class="paragraph">

</div>

The small-step evaluation relations for arithmetic and boolean
expressions are straightforward extensions of the tiny language we've
been working up to now. To make them easier to read, we introduce the
symbolic notations <span class="inlinecode"><span
style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span></span> and <span class="inlinecode"><span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span></span>, respectively, for the arithmetic and
boolean step relations.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">aval</span> : <span class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">av\_num</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">aval</span> (<span
class="id" type="var">ANum</span> <span class="id"
type="var">n</span>).\
\

</div>

<div class="doc">

We are not actually going to bother to define boolean values, since they
aren't needed in the definition of <span class="inlinecode"><span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span></span> below (why?), though they might be if our
language were a bit larger (why?).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> " t '/' st
'<span style="font-family: arial;">⇒</span>~a~' t' " (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40,
<span class="id" type="var">st</span> <span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 39).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">astep</span> : <span class="id" type="var">state</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">aexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">AS\_Id</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">i</span>,\
       <span class="id" type="var">AId</span> <span class="id"
type="var">i</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span> <span class="id" type="var">ANum</span> (<span
class="id" type="var">st</span> <span class="id" type="var">i</span>)\
   | <span class="id" type="var">AS\_Plus</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">n1</span> <span
class="id" type="var">n2</span>,\
       <span class="id" type="var">APlus</span> (<span class="id"
type="var">ANum</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">ANum</span> <span class="id" type="var">n2</span>)
/ <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span> <span class="id" type="var">ANum</span> (<span
class="id" type="var">n1</span> + <span class="id"
type="var">n2</span>)\
   | <span class="id" type="var">AS\_Plus1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">a1</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2</span>,\
       <span class="id" type="var">a1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~a~</span> <span class="id" type="var">a1'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">APlus</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span> (<span class="id" type="var">APlus</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2</span>)\
   | <span class="id" type="var">AS\_Plus2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">a2</span> <span class="id" type="var">a2'</span>,\
       <span class="id" type="var">aval</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">a2</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~a~</span> <span class="id" type="var">a2'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">APlus</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">a2</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span> (<span class="id" type="var">APlus</span> <span
class="id" type="var">v~1~</span> <span class="id"
type="var">a2'</span>)\
   | <span class="id" type="var">AS\_Minus</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">n1</span> <span
class="id" type="var">n2</span>,\
       (<span class="id" type="var">AMinus</span> (<span class="id"
type="var">ANum</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">ANum</span> <span class="id"
type="var">n2</span>)) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span> (<span class="id" type="var">ANum</span> (<span
class="id" type="var">minus</span> <span class="id" type="var">n1</span>
<span class="id" type="var">n2</span>))\
   | <span class="id" type="var">AS\_Minus1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">a1</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2</span>,\
       <span class="id" type="var">a1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~a~</span> <span class="id" type="var">a1'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">AMinus</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span> (<span class="id" type="var">AMinus</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2</span>)\
   | <span class="id" type="var">AS\_Minus2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">a2</span> <span class="id" type="var">a2'</span>,\
       <span class="id" type="var">aval</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">a2</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~a~</span> <span class="id" type="var">a2'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">AMinus</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">a2</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span> (<span class="id" type="var">AMinus</span> <span
class="id" type="var">v~1~</span> <span class="id"
type="var">a2'</span>)\
   | <span class="id" type="var">AS\_Mult</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">n1</span> <span
class="id" type="var">n2</span>,\
       (<span class="id" type="var">AMult</span> (<span class="id"
type="var">ANum</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">ANum</span> <span class="id"
type="var">n2</span>)) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span> (<span class="id" type="var">ANum</span> (<span
class="id" type="var">mult</span> <span class="id" type="var">n1</span>
<span class="id" type="var">n2</span>))\
   | <span class="id" type="var">AS\_Mult1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">a1</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2</span>,\
       <span class="id" type="var">a1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~a~</span> <span class="id" type="var">a1'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">AMult</span> (<span class="id"
type="var">a1</span>) (<span class="id" type="var">a2</span>)) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span> (<span class="id" type="var">AMult</span> (<span
class="id" type="var">a1'</span>) (<span class="id"
type="var">a2</span>))\
   | <span class="id" type="var">AS\_Mult2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">a2</span> <span class="id" type="var">a2'</span>,\
       <span class="id" type="var">aval</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">a2</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~a~</span> <span class="id" type="var">a2'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">AMult</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">a2</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~a~</span> (<span class="id" type="var">AMult</span> <span
class="id" type="var">v~1~</span> <span class="id"
type="var">a2'</span>)\
\
     <span class="id" type="keyword">where</span> " t '/' st '<span
style="font-family: arial;">⇒</span>~a~' t' " := (<span class="id"
type="var">astep</span> <span class="id" type="var">st</span> <span
class="id" type="var">t</span> <span class="id" type="var">t'</span>).\
\
   <span class="id" type="keyword">Reserved Notation</span> " t '/' st
'<span style="font-family: arial;">⇒</span>~b~' t' " (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40,
<span class="id" type="var">st</span> <span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 39).\
\
   <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">bstep</span> : <span class="id" type="var">state</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">bexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">BS\_Eq</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">n1</span> <span
class="id" type="var">n2</span>,\
       (<span class="id" type="var">BEq</span> (<span class="id"
type="var">ANum</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">ANum</span> <span class="id"
type="var">n2</span>)) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span>\
       (<span class="id" type="keyword">if</span> (<span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n1</span> <span
class="id" type="var">n2</span>) <span class="id"
type="keyword">then</span> <span class="id" type="var">BTrue</span>
<span class="id" type="keyword">else</span> <span class="id"
type="var">BFalse</span>)\
   | <span class="id" type="var">BS\_Eq1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">a1</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2</span>,\
       <span class="id" type="var">a1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~a~</span> <span class="id" type="var">a1'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">BEq</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span> (<span class="id" type="var">BEq</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2</span>)\
   | <span class="id" type="var">BS\_Eq2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">a2</span> <span class="id" type="var">a2'</span>,\
       <span class="id" type="var">aval</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">a2</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~a~</span> <span class="id" type="var">a2'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">BEq</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">a2</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span> (<span class="id" type="var">BEq</span> <span
class="id" type="var">v~1~</span> <span class="id"
type="var">a2'</span>)\
   | <span class="id" type="var">BS\_LtEq</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">n1</span> <span
class="id" type="var">n2</span>,\
       (<span class="id" type="var">BLe</span> (<span class="id"
type="var">ANum</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">ANum</span> <span class="id"
type="var">n2</span>)) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span>\
                (<span class="id" type="keyword">if</span> (<span
class="id" type="var">ble\_nat</span> <span class="id"
type="var">n1</span> <span class="id" type="var">n2</span>) <span
class="id" type="keyword">then</span> <span class="id"
type="var">BTrue</span> <span class="id" type="keyword">else</span>
<span class="id" type="var">BFalse</span>)\
   | <span class="id" type="var">BS\_LtEq1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">a1</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2</span>,\
       <span class="id" type="var">a1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~a~</span> <span class="id" type="var">a1'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">BLe</span> <span class="id"
type="var">a1</span> <span class="id" type="var">a2</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span> (<span class="id" type="var">BLe</span> <span
class="id" type="var">a1'</span> <span class="id" type="var">a2</span>)\
   | <span class="id" type="var">BS\_LtEq2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">a2</span> <span class="id" type="var">a2'</span>,\
       <span class="id" type="var">aval</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">a2</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~a~</span> <span class="id" type="var">a2'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">BLe</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">a2</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span> (<span class="id" type="var">BLe</span> <span
class="id" type="var">v~1~</span> (<span class="id"
type="var">a2'</span>))\
   | <span class="id" type="var">BS\_NotTrue</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span>,\
       (<span class="id" type="var">BNot</span> <span class="id"
type="var">BTrue</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span> <span class="id" type="var">BFalse</span>\
   | <span class="id" type="var">BS\_NotFalse</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span>,\
       (<span class="id" type="var">BNot</span> <span class="id"
type="var">BFalse</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span> <span class="id" type="var">BTrue</span>\
   | <span class="id" type="var">BS\_NotStep</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">b1</span> <span
class="id" type="var">b1'</span>,\
       <span class="id" type="var">b1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~b~</span> <span class="id" type="var">b1'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">BNot</span> <span class="id"
type="var">b1</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span> (<span class="id" type="var">BNot</span> <span
class="id" type="var">b1'</span>)\
   | <span class="id" type="var">BS\_AndTrueTrue</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span>,\
       (<span class="id" type="var">BAnd</span> <span class="id"
type="var">BTrue</span> <span class="id" type="var">BTrue</span>) /
<span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span> <span class="id" type="var">BTrue</span>\
   | <span class="id" type="var">BS\_AndTrueFalse</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span>,\
       (<span class="id" type="var">BAnd</span> <span class="id"
type="var">BTrue</span> <span class="id" type="var">BFalse</span>) /
<span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span> <span class="id" type="var">BFalse</span>\
   | <span class="id" type="var">BS\_AndFalse</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">b2</span>,\
       (<span class="id" type="var">BAnd</span> <span class="id"
type="var">BFalse</span> <span class="id" type="var">b2</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span> <span class="id" type="var">BFalse</span>\
   | <span class="id" type="var">BS\_AndTrueStep</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">b2</span> <span
class="id" type="var">b2'</span>,\
       <span class="id" type="var">b2</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~b~</span> <span class="id" type="var">b2'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">BAnd</span> <span class="id"
type="var">BTrue</span> <span class="id" type="var">b2</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span> (<span class="id" type="var">BAnd</span> <span
class="id" type="var">BTrue</span> <span class="id"
type="var">b2'</span>)\
   | <span class="id" type="var">BS\_AndStep</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">b1</span> <span
class="id" type="var">b1'</span> <span class="id" type="var">b2</span>,\
       <span class="id" type="var">b1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~b~</span> <span class="id" type="var">b1'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">BAnd</span> <span class="id"
type="var">b1</span> <span class="id" type="var">b2</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span><span class="id"
type="var">~b~</span> (<span class="id" type="var">BAnd</span> <span
class="id" type="var">b1'</span> <span class="id" type="var">b2</span>)\
\
   <span class="id" type="keyword">where</span> " t '/' st '<span
style="font-family: arial;">⇒</span>~b~' t' " := (<span class="id"
type="var">bstep</span> <span class="id" type="var">st</span> <span
class="id" type="var">t</span> <span class="id" type="var">t'</span>).\
\

</div>

<div class="doc">

The semantics of commands is the interesting part. We need two small
tricks to make it work:
<div class="paragraph">

</div>

-   We use <span class="inlinecode"><span class="id"
    type="var">SKIP</span></span> as a "command value" — i.e., a command
    that has reached a normal form.
    <div class="paragraph">

    </div>

    -   An assignment command reduces to <span class="inlinecode"><span
        class="id" type="var">SKIP</span></span> (and an updated state).
        <div class="paragraph">

        </div>

    -   The sequencing command waits until its left-hand subcommand has
        reduced to <span class="inlinecode"><span class="id"
        type="var">SKIP</span></span>, then throws it away so that
        reduction can continue with the right-hand subcommand.
        <div class="paragraph">

        </div>
-   We reduce a <span class="inlinecode"><span class="id"
    type="var">WHILE</span></span> command by transforming it into a
    conditional followed by the same <span class="inlinecode"><span
    class="id" type="var">WHILE</span></span>.

<div class="paragraph">

</div>

(There are other ways of achieving the effect of the latter trick, but
they all share the feature that the original <span
class="inlinecode"><span class="id" type="var">WHILE</span></span>
command needs to be saved somewhere while a single copy of the loop body
is being evaluated.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> " t '/' st
'<span style="font-family: arial;">⇒</span>' t' '/' st' "\
                   (<span class="id" type="tactic">at</span> <span
class="id" type="var">level</span> 40, <span class="id"
type="var">st</span> <span class="id" type="tactic">at</span> <span
class="id" type="var">level</span> 39, <span class="id"
type="var">t'</span> <span class="id" type="tactic">at</span> <span
class="id" type="var">level</span> 39).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">cstep</span> : (<span class="id" type="var">com</span> ×
<span class="id" type="var">state</span>) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">com</span> × <span class="id" type="var">state</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">CS\_AssStep</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">i</span> <span
class="id" type="var">a</span> <span class="id" type="var">a'</span>,\
       <span class="id" type="var">a</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~a~</span> <span class="id" type="var">a'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">i</span> ::= <span class="id"
type="var">a</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">i</span> ::= <span class="id" type="var">a'</span>) / <span
class="id" type="var">st</span>\
   | <span class="id" type="var">CS\_Ass</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">i</span> <span
class="id" type="var">n</span>,\
       (<span class="id" type="var">i</span> ::= (<span class="id"
type="var">ANum</span> <span class="id" type="var">n</span>)) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">SKIP</span> / (<span class="id" type="var">update</span>
<span class="id" type="var">st</span> <span class="id"
type="var">i</span> <span class="id" type="var">n</span>)\
   | <span class="id" type="var">CS\_SeqStep</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c1'</span> <span class="id" type="var">st'</span>
<span class="id" type="var">c2</span>,\
       <span class="id" type="var">c1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">c1'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">c1</span> ;; <span class="id"
type="var">c2</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">c1'</span> ;; <span class="id" type="var">c2</span>) / <span
class="id" type="var">st'</span>\
   | <span class="id" type="var">CS\_SeqFinish</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">c2</span>,\
       (<span class="id" type="var">SKIP</span> ;; <span class="id"
type="var">c2</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">c2</span> / <span class="id" type="var">st</span>\
   | <span class="id" type="var">CS\_IfTrue</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c2</span>,\
       <span class="id" type="var">IFB</span> <span class="id"
type="var">BTrue</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">c1</span> / <span class="id" type="var">st</span>\
   | <span class="id" type="var">CS\_IfFalse</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c2</span>,\
       <span class="id" type="var">IFB</span> <span class="id"
type="var">BFalse</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">c2</span> / <span class="id" type="var">st</span>\
   | <span class="id" type="var">CS\_IfStep</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">b</span> <span
class="id" type="var">b'</span> <span class="id" type="var">c1</span>
<span class="id" type="var">c2</span>,\
       <span class="id" type="var">b</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~b~</span> <span class="id" type="var">b'</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">IFB</span> <span class="id" type="var">b'</span> <span
class="id" type="var">THEN</span> <span class="id" type="var">c1</span>
<span class="id" type="var">ELSE</span> <span class="id"
type="var">c2</span> <span class="id" type="var">FI</span>) / <span
class="id" type="var">st</span>\
   | <span class="id" type="var">CS\_While</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">b</span> <span
class="id" type="var">c1</span>,\
           (<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c1</span> <span class="id" type="var">END</span>)
/ <span class="id" type="var">st</span>\
       <span style="font-family: arial;">⇒</span> (<span class="id"
type="var">IFB</span> <span class="id" type="var">b</span> <span
class="id" type="var">THEN</span> (<span class="id"
type="var">c1</span>;; (<span class="id" type="var">WHILE</span> <span
class="id" type="var">b</span> <span class="id" type="var">DO</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">END</span>)) <span class="id" type="var">ELSE</span> <span
class="id" type="var">SKIP</span> <span class="id" type="var">FI</span>)
/ <span class="id" type="var">st</span>\
\
   <span class="id" type="keyword">where</span> " t '/' st '<span
style="font-family: arial;">⇒</span>' t' '/' st' " := (<span class="id"
type="var">cstep</span> (<span class="id" type="var">t</span>,<span
class="id" type="var">st</span>) (<span class="id"
type="var">t'</span>,<span class="id" type="var">st'</span>)).\
\

</div>

<div class="doc">

Concurrent Imp {.section}
==============

<div class="paragraph">

</div>

Finally, to show the power of this definitional style, let's enrich Imp
with a new form of command that runs two subcommands in parallel and
terminates when both have terminated. To reflect the unpredictability of
scheduling, the actions of the subcommands may be interleaved in any
order, but they share the same memory and can communicate by reading and
writing the same variables.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">CImp</span>.\
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
   <span class="comment">(\* New: \*)</span>\
   | <span class="id" type="var">CPar</span> : <span class="id"
type="var">com</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">com</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">com</span>.\
<div id="proofcontrol20" class="togglescript"
onclick="toggleDisplay('proof20');toggleDisplay('proofcontrol20')">

<span class="show"></span>

</div>

<div id="proof20" class="proofscript"
onclick="toggleDisplay('proof20');toggleDisplay('proofcontrol20')"
style="display: none;">

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
<span class="id" type="var">c</span> "WHILE" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "PAR"
].\

</div>

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
 <span class="id" type="keyword">Notation</span> "'IFB' b 'THEN' c1
'ELSE' c2 'FI'" :=\
   (<span class="id" type="var">CIf</span> <span class="id"
type="var">b</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c2</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 80,
<span class="id" type="var">right</span> <span class="id"
type="var">associativity</span>).\
 <span class="id" type="keyword">Notation</span> "'PAR' c1 'WITH' c2
'END'" :=\
   (<span class="id" type="var">CPar</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c2</span>) (<span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 80, <span class="id" type="var">right</span>
<span class="id" type="var">associativity</span>).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">cstep</span> : (<span class="id" type="var">com</span> ×
<span class="id" type="var">state</span>) <span
style="font-family: arial;">→</span> (<span class="id"
type="var">com</span> × <span class="id" type="var">state</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
     <span class="comment">(\* Old part \*)</span>\
   | <span class="id" type="var">CS\_AssStep</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">i</span> <span
class="id" type="var">a</span> <span class="id" type="var">a'</span>,\
       <span class="id" type="var">a</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~a~</span> <span class="id" type="var">a'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">i</span> ::= <span class="id"
type="var">a</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">i</span> ::= <span class="id" type="var">a'</span>) / <span
class="id" type="var">st</span>\
   | <span class="id" type="var">CS\_Ass</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">i</span> <span
class="id" type="var">n</span>,\
       (<span class="id" type="var">i</span> ::= (<span class="id"
type="var">ANum</span> <span class="id" type="var">n</span>)) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">SKIP</span> / (<span class="id" type="var">update</span>
<span class="id" type="var">st</span> <span class="id"
type="var">i</span> <span class="id" type="var">n</span>)\
   | <span class="id" type="var">CS\_SeqStep</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c1'</span> <span class="id" type="var">st'</span>
<span class="id" type="var">c2</span>,\
       <span class="id" type="var">c1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">c1'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">c1</span> ;; <span class="id"
type="var">c2</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">c1'</span> ;; <span class="id" type="var">c2</span>) / <span
class="id" type="var">st'</span>\
   | <span class="id" type="var">CS\_SeqFinish</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">c2</span>,\
       (<span class="id" type="var">SKIP</span> ;; <span class="id"
type="var">c2</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">c2</span> / <span class="id" type="var">st</span>\
   | <span class="id" type="var">CS\_IfTrue</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c2</span>,\
       (<span class="id" type="var">IFB</span> <span class="id"
type="var">BTrue</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">c1</span> / <span class="id" type="var">st</span>\
   | <span class="id" type="var">CS\_IfFalse</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c2</span>,\
       (<span class="id" type="var">IFB</span> <span class="id"
type="var">BFalse</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">c2</span> / <span class="id" type="var">st</span>\
   | <span class="id" type="var">CS\_IfStep</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">b</span> <span
class="id" type="var">b'</span> <span class="id" type="var">c1</span>
<span class="id" type="var">c2</span>,\
       <span class="id" type="var">b</span> /<span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span><span
class="id" type="var">~b~</span> <span class="id" type="var">b'</span>
<span style="font-family: arial;">→</span>\
       (<span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">IFB</span> <span class="id" type="var">b'</span> <span
class="id" type="var">THEN</span> <span class="id" type="var">c1</span>
<span class="id" type="var">ELSE</span> <span class="id"
type="var">c2</span> <span class="id" type="var">FI</span>) / <span
class="id" type="var">st</span>\
   | <span class="id" type="var">CS\_While</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">b</span> <span
class="id" type="var">c1</span>,\
       (<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c1</span> <span class="id" type="var">END</span>)
/ <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span>\
                (<span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> (<span
class="id" type="var">c1</span>;; (<span class="id"
type="var">WHILE</span> <span class="id" type="var">b</span> <span
class="id" type="var">DO</span> <span class="id" type="var">c1</span>
<span class="id" type="var">END</span>)) <span class="id"
type="var">ELSE</span> <span class="id" type="var">SKIP</span> <span
class="id" type="var">FI</span>) / <span class="id"
type="var">st</span>\
     <span class="comment">(\* New part: \*)</span>\
   | <span class="id" type="var">CS\_Par1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c1'</span> <span class="id" type="var">c2</span>
<span class="id" type="var">st'</span>,\
       <span class="id" type="var">c1</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">c1'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">PAR</span> <span class="id"
type="var">c1</span> <span class="id" type="var">WITH</span> <span
class="id" type="var">c2</span> <span class="id" type="var">END</span>)
/ <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">PAR</span> <span class="id" type="var">c1'</span> <span
class="id" type="var">WITH</span> <span class="id" type="var">c2</span>
<span class="id" type="var">END</span>) / <span class="id"
type="var">st'</span>\
   | <span class="id" type="var">CS\_Par2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c2</span> <span class="id" type="var">c2'</span>
<span class="id" type="var">st'</span>,\
       <span class="id" type="var">c2</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">c2'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">PAR</span> <span class="id"
type="var">c1</span> <span class="id" type="var">WITH</span> <span
class="id" type="var">c2</span> <span class="id" type="var">END</span>)
/ <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">PAR</span> <span class="id" type="var">c1</span> <span
class="id" type="var">WITH</span> <span class="id" type="var">c2'</span>
<span class="id" type="var">END</span>) / <span class="id"
type="var">st'</span>\
   | <span class="id" type="var">CS\_ParDone</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span>,\
       (<span class="id" type="var">PAR</span> <span class="id"
type="var">SKIP</span> <span class="id" type="var">WITH</span> <span
class="id" type="var">SKIP</span> <span class="id"
type="var">END</span>) / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">SKIP</span> / <span class="id" type="var">st</span>\
   <span class="id" type="keyword">where</span> " t '/' st '<span
style="font-family: arial;">⇒</span>' t' '/' st' " := (<span class="id"
type="var">cstep</span> (<span class="id" type="var">t</span>,<span
class="id" type="var">st</span>) (<span class="id"
type="var">t'</span>,<span class="id" type="var">st'</span>)).\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">cmultistep</span> := <span class="id" type="var">multi</span>
<span class="id" type="var">cstep</span>.\
\
 <span class="id" type="keyword">Notation</span> " t '/' st '<span
style="font-family: arial;">⇒\*</span>' t' '/' st' " :=\
    (<span class="id" type="var">multi</span> <span class="id"
type="var">cstep</span> (<span class="id" type="var">t</span>,<span
class="id" type="var">st</span>) (<span class="id"
type="var">t'</span>,<span class="id" type="var">st'</span>))\
    (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 40, <span class="id" type="var">st</span> <span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 39, <span class="id" type="var">t'</span> <span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 39).\
\

</div>

<div class="doc">

Among the many interesting properties of this language is the fact that
the following program can terminate with the variable <span
class="inlinecode"><span class="id" type="var">X</span></span> set to
any value...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">par\_loop</span> : <span class="id" type="var">com</span> :=\
   <span class="id" type="var">PAR</span>\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">ANum</span> 1\
   <span class="id" type="var">WITH</span>\
     <span class="id" type="var">WHILE</span> <span class="id"
type="var">BEq</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">Y</span>) (<span class="id" type="var">ANum</span>
0) <span class="id" type="var">DO</span>\
       <span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1)\
     <span class="id" type="var">END</span>\
   <span class="id" type="var">END</span>.\
\

</div>

<div class="doc">

In particular, it can terminate with <span class="inlinecode"><span
class="id" type="var">X</span></span> set to <span
class="inlinecode">0</span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">par\_loop\_example\_0</span>:\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>,\
        <span class="id" type="var">par\_loop</span> / <span class="id"
type="var">empty\_state</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">SKIP</span> / <span class="id" type="var">st'</span>\
     <span style="font-family: arial;">∧</span> <span class="id"
type="var">st'</span> <span class="id" type="var">X</span> = 0.\
<div id="proofcontrol21" class="togglescript"
onclick="toggleDisplay('proof21');toggleDisplay('proofcontrol21')">

<span class="show"></span>

</div>

<div id="proof21" class="proofscript"
onclick="toggleDisplay('proof21');toggleDisplay('proofcontrol21')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">ex\_intro</span>. <span class="id"
type="tactic">split</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">par\_loop</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par1</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_Ass</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_While</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">BS\_Eq1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">AS\_Id</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">BS\_Eq</span>. <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfFalse</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">CS\_ParDone</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_refl</span>.\
   <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

It can also terminate with <span class="inlinecode"><span class="id"
type="var">X</span></span> set to <span class="inlinecode">2</span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">par\_loop\_example\_2</span>:\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>,\
        <span class="id" type="var">par\_loop</span> / <span class="id"
type="var">empty\_state</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">SKIP</span> / <span class="id" type="var">st'</span>\
     <span style="font-family: arial;">∧</span> <span class="id"
type="var">st'</span> <span class="id" type="var">X</span> = 2.\
<div id="proofcontrol22" class="togglescript"
onclick="toggleDisplay('proof22');toggleDisplay('proofcontrol22')">

<span class="show"></span>

</div>

<div id="proof22" class="proofscript"
onclick="toggleDisplay('proof22');toggleDisplay('proofcontrol22')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">ex\_intro</span>. <span class="id"
type="tactic">split</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_While</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">BS\_Eq1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">AS\_Id</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">BS\_Eq</span>. <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfTrue</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_SeqStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_AssStep</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">AS\_Plus1</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">AS\_Id</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_SeqStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_AssStep</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">AS\_Plus</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_SeqStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_Ass</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_SeqFinish</span>.\
\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_While</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">BS\_Eq1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">AS\_Id</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">BS\_Eq</span>. <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfTrue</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_SeqStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_AssStep</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">AS\_Plus1</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">AS\_Id</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_SeqStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_AssStep</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">AS\_Plus</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_SeqStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_Ass</span>.\
\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par1</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_Ass</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_SeqFinish</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_While</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">BS\_Eq1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">AS\_Id</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">BS\_Eq</span>. <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfFalse</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">CS\_ParDone</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_refl</span>.\
   <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

More generally...
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">par\_body\_n\_\_Sn</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">st</span>,\
   <span class="id" type="var">st</span> <span class="id"
type="var">X</span> = <span class="id" type="var">n</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">st</span> <span class="id" type="var">Y</span> = 0 <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">par\_loop</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒\*</span> <span
class="id" type="var">par\_loop</span> / (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">X</span> (<span class="id" type="var">S</span>
<span class="id" type="var">n</span>)).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">par\_body\_n</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">st</span>,\
   <span class="id" type="var">st</span> <span class="id"
type="var">X</span> = 0 <span style="font-family: arial;">∧</span> <span
class="id" type="var">st</span> <span class="id" type="var">Y</span> = 0
<span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>,\
     <span class="id" type="var">par\_loop</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒\*</span> <span
class="id" type="var">par\_loop</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">st'</span> <span class="id" type="var">X</span> =
<span class="id" type="var">n</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">st'</span> <span class="id" type="var">Y</span> = 0.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

... the above loop can exit with <span class="inlinecode"><span
class="id" type="var">X</span></span> having any value whatsoever.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">par\_loop\_any\_X</span>:\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">st'</span>,\
     <span class="id" type="var">par\_loop</span> / <span class="id"
type="var">empty\_state</span> <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">SKIP</span> / <span class="id" type="var">st'</span>\
     <span style="font-family: arial;">∧</span> <span class="id"
type="var">st'</span> <span class="id" type="var">X</span> = <span
class="id" type="var">n</span>.\
<div id="proofcontrol23" class="togglescript"
onclick="toggleDisplay('proof23');toggleDisplay('proofcontrol23')">

<span class="show"></span>

</div>

<div id="proof23" class="proofscript"
onclick="toggleDisplay('proof23');toggleDisplay('proofcontrol23')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span>.\
   <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">par\_body\_n</span> <span class="id" type="var">n</span>
<span class="id" type="var">empty\_state</span>).\
     <span class="id" type="tactic">split</span>; <span class="id"
type="tactic">unfold</span> <span class="id" type="var">update</span>;
<span class="id" type="tactic">reflexivity</span>.\
\
   <span class="id" type="tactic">rename</span> <span class="id"
type="var">x</span> <span class="id" type="var">into</span> <span
class="id" type="var">st</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">H'</span> [<span class="id" type="var">HX</span>
<span class="id" type="var">HY</span>]]; <span class="id"
type="tactic">clear</span> <span class="id" type="var">H</span>.\
   <span style="font-family: arial;">∃</span>(<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">Y</span> 1). <span class="id"
type="tactic">split</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_trans</span> <span class="id"
type="keyword">with</span> (<span class="id"
type="var">par\_loop</span>,<span class="id" type="var">st</span>).
<span class="id" type="tactic">apply</span> <span class="id"
type="var">H'</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par1</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_Ass</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_While</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">BS\_Eq1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">AS\_Id</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">update\_eq</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfStep</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">BS\_Eq</span>. <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">CS\_Par2</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">CS\_IfFalse</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">CS\_ParDone</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>.\
\
   <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">update\_neq</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="tactic">intro</span> <span class="id" type="var">X</span>; <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">X</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">CImp</span>.\
\

</div>

<div class="doc">

A Small-Step Stack Machine {.section}
==========================

<div class="paragraph">

</div>

Last example: a small-step semantics for the stack machine example from
Imp.v.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">stack</span> := <span class="id" type="var">list</span> <span
class="id" type="var">nat</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">prog</span> := <span class="id" type="var">list</span> <span
class="id" type="var">sinstr</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">stack\_step</span> : <span class="id" type="var">state</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">prog</span> × <span class="id" type="var">stack</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">prog</span> × <span class="id" type="var">stack</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">SS\_Push</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">stk</span> <span
class="id" type="var">n</span> <span class="id" type="var">p'</span>,\
     <span class="id" type="var">stack\_step</span> <span class="id"
type="var">st</span> (<span class="id" type="var">SPush</span> <span
class="id" type="var">n</span> :: <span class="id" type="var">p'</span>,
<span class="id" type="var">stk</span>) (<span class="id"
type="var">p'</span>, <span class="id" type="var">n</span> :: <span
class="id" type="var">stk</span>)\
   | <span class="id" type="var">SS\_Load</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">stk</span> <span
class="id" type="var">i</span> <span class="id" type="var">p'</span>,\
     <span class="id" type="var">stack\_step</span> <span class="id"
type="var">st</span> (<span class="id" type="var">SLoad</span> <span
class="id" type="var">i</span> :: <span class="id" type="var">p'</span>,
<span class="id" type="var">stk</span>) (<span class="id"
type="var">p'</span>, <span class="id" type="var">st</span> <span
class="id" type="var">i</span> :: <span class="id"
type="var">stk</span>)\
   | <span class="id" type="var">SS\_Plus</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">stk</span> <span
class="id" type="var">n</span> <span class="id" type="var">m</span>
<span class="id" type="var">p'</span>,\
     <span class="id" type="var">stack\_step</span> <span class="id"
type="var">st</span> (<span class="id" type="var">SPlus</span> :: <span
class="id" type="var">p'</span>, <span class="id"
type="var">n</span>::<span class="id" type="var">m</span>::<span
class="id" type="var">stk</span>) (<span class="id"
type="var">p'</span>, (<span class="id" type="var">m</span>+<span
class="id" type="var">n</span>)::<span class="id"
type="var">stk</span>)\
   | <span class="id" type="var">SS\_Minus</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">stk</span> <span
class="id" type="var">n</span> <span class="id" type="var">m</span>
<span class="id" type="var">p'</span>,\
     <span class="id" type="var">stack\_step</span> <span class="id"
type="var">st</span> (<span class="id" type="var">SMinus</span> :: <span
class="id" type="var">p'</span>, <span class="id"
type="var">n</span>::<span class="id" type="var">m</span>::<span
class="id" type="var">stk</span>) (<span class="id"
type="var">p'</span>, (<span class="id" type="var">m</span>-<span
class="id" type="var">n</span>)::<span class="id"
type="var">stk</span>)\
   | <span class="id" type="var">SS\_Mult</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">stk</span> <span
class="id" type="var">n</span> <span class="id" type="var">m</span>
<span class="id" type="var">p'</span>,\
     <span class="id" type="var">stack\_step</span> <span class="id"
type="var">st</span> (<span class="id" type="var">SMult</span> :: <span
class="id" type="var">p'</span>, <span class="id"
type="var">n</span>::<span class="id" type="var">m</span>::<span
class="id" type="var">stk</span>) (<span class="id"
type="var">p'</span>, (<span class="id" type="var">m</span>×<span
class="id" type="var">n</span>)::<span class="id"
type="var">stk</span>).\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">stack\_step\_deterministic</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span>,\
   <span class="id" type="var">deterministic</span> (<span class="id"
type="var">stack\_step</span> <span class="id" type="var">st</span>).\
<div id="proofcontrol24" class="togglescript"
onclick="toggleDisplay('proof24');toggleDisplay('proofcontrol24')">

<span class="show"></span>

</div>

<div id="proof24" class="proofscript"
onclick="toggleDisplay('proof24');toggleDisplay('proofcontrol24')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">deterministic</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">st</span> <span
class="id" type="var">x</span> <span class="id" type="var">y1</span>
<span class="id" type="var">y2</span> <span class="id"
type="var">H1</span> <span class="id" type="var">H2</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">H1</span>; <span class="id" type="tactic">inversion</span>
<span class="id" type="var">H2</span>; <span class="id"
type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">stack\_multistep</span> <span class="id" type="var">st</span>
:= <span class="id" type="var">multi</span> (<span class="id"
type="var">stack\_step</span> <span class="id" type="var">st</span>).\
\

</div>

<div class="doc">

#### Exercise: 3 stars, advanced (compiler\_is\_correct) {.section}

Remember the definition of <span class="inlinecode"><span class="id"
type="var">compile</span></span> for <span class="inlinecode"><span
class="id" type="var">aexp</span></span> given in the <span
class="inlinecode"><span class="id" type="var">Imp</span></span>
chapter. We want now to prove <span class="inlinecode"><span class="id"
type="var">compile</span></span> correct with respect to the stack
machine.
<div class="paragraph">

</div>

State what it means for the compiler to be correct according to the
stack machine small step semantics and then prove it.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">compiler\_is\_correct\_statement</span> : <span class="id"
type="keyword">Prop</span> :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">compiler\_is\_correct</span> : <span class="id"
type="var">compiler\_is\_correct\_statement</span>.\
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

\

</div>

</div>

<div id="footer">

------------------------------------------------------------------------

[Index](http://www.cis.upenn.edu/~bcpierce/sf/current/coqindex.html)

</div>

</div>
