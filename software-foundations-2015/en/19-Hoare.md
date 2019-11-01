<div id="page">

<div id="header">

</div>

<div id="main">

Hoare<span class="subtitle">Hoare Logic, Part I</span> {.libtitle}
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

In the past couple of chapters, we've begun applying the mathematical
tools developed in the first part of the course to studying the theory
of a small programming language, Imp.
<div class="paragraph">

</div>

-   We defined a type of *abstract syntax trees* for Imp, together with
    an *evaluation relation* (a partial function on states) that
    specifies the *operational semantics* of programs.
    <div class="paragraph">

    </div>

    The language we defined, though small, captures some of the key
    features of full-blown languages like C, C++, and Java, including
    the fundamental notion of mutable state and some common control
    structures.
    <div class="paragraph">

    </div>

-   We proved a number of *metatheoretic properties* — "meta" in the
    sense that they are properties of the language as a whole, rather
    than properties of particular programs in the language. These
    included:
    <div class="paragraph">

    </div>

    -   determinism of evaluation
        <div class="paragraph">

        </div>

    -   equivalence of some different ways of writing down the
        definitions (e.g. functional and relational definitions of
        arithmetic expression evaluation)
        <div class="paragraph">

        </div>

    -   guaranteed termination of certain classes of programs
        <div class="paragraph">

        </div>

    -   correctness (in the sense of preserving meaning) of a number of
        useful program transformations
        <div class="paragraph">

        </div>

    -   behavioral equivalence of programs (in the <span
        class="inlinecode"><span class="id"
        type="var">Equiv</span></span> chapter).

If we stopped here, we would already have something useful: a set of
tools for defining and discussing programming languages and language
features that are mathematically precise, flexible, and easy to work
with, applied to a set of key properties. All of these properties are
things that language designers, compiler writers, and users might care
about knowing. Indeed, many of them are so fundamental to our
understanding of the programming languages we deal with that we might
not consciously recognize them as "theorems." But properties that seem
intuitively obvious can sometimes be quite subtle (in some cases, even
subtly wrong!).
<div class="paragraph">

</div>

We'll return to the theme of metatheoretic properties of whole languages
later in the course when we discuss *types* and *type soundness*. In
this chapter, though, we'll turn to a different set of issues.
<div class="paragraph">

</div>

Our goal is to see how to carry out some simple examples of *program
verification* — i.e., using the precise definition of Imp to prove
formally that particular programs satisfy particular specifications of
their behavior. We'll develop a reasoning system called *Floyd-Hoare
Logic* — often shortened to just *Hoare Logic* — in which each of the
syntactic constructs of Imp is equipped with a single, generic "proof
rule" that can be used to reason compositionally about the correctness
of programs involving this construct.
<div class="paragraph">

</div>

Hoare Logic originates in the 1960s, and it continues to be the subject
of intensive research right up to the present day. It lies at the core
of a multitude of tools that are being used in academia and industry to
specify and verify real software systems.

</div>

<div class="code code-tight">

\
\

</div>

<div class="doc">

Hoare Logic {.section}
===========

<div class="paragraph">

</div>

Hoare Logic combines two beautiful ideas: a natural way of writing down
*specifications* of programs, and a *compositional proof technique* for
proving that programs are correct with respect to such specifications —
where by "compositional" we mean that the structure of proofs directly
mirrors the structure of the programs that they are about.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Assertions {.section}
----------

<div class="paragraph">

</div>

To talk about specifications of programs, the first thing we need is a
way of making *assertions* about properties that hold at particular
points during a program's execution — i.e., claims about the current
state of the memory when program execution reaches that point. Formally,
an assertion is just a family of propositions indexed by a <span
class="inlinecode"><span class="id" type="var">state</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">Assertion</span> := <span class="id" type="var">state</span>
<span style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star, optional (assertions) {.section}

</div>

<div class="code code-space">

\

</div>

<div class="doc">

Paraphrase the following assertions in English.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">as1</span> : <span class="id" type="var">Assertion</span> :=
<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">st</span> <span
class="id" type="var">X</span> = 3.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">as2</span> : <span class="id" type="var">Assertion</span> :=
<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">st</span> <span
class="id" type="var">X</span> ≤ <span class="id" type="var">st</span>
<span class="id" type="var">Y</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">as3</span> : <span class="id" type="var">Assertion</span> :=\
   <span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">st</span> <span
class="id" type="var">X</span> = 3 <span
style="font-family: arial;">∨</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> ≤ <span
class="id" type="var">st</span> <span class="id" type="var">Y</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">as4</span> : <span class="id" type="var">Assertion</span> :=\
   <span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">st</span> <span
class="id" type="var">Z</span> × <span class="id" type="var">st</span>
<span class="id" type="var">Z</span> ≤ <span class="id"
type="var">st</span> <span class="id" type="var">X</span> <span
style="font-family: arial;">∧</span>\
             ¬ (((<span class="id" type="var">S</span> (<span class="id"
type="var">st</span> <span class="id" type="var">Z</span>)) × (<span
class="id" type="var">S</span> (<span class="id" type="var">st</span>
<span class="id" type="var">Z</span>))) ≤ <span class="id"
type="var">st</span> <span class="id" type="var">X</span>).\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">as5</span> : <span class="id" type="var">Assertion</span> :=
<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">True</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">as6</span> : <span class="id" type="var">Assertion</span> :=
<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">False</span>.\
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

Notation for Assertions {.section}
-----------------------

<div class="paragraph">

</div>

This way of writing assertions can be a little bit heavy, for two
reasons: (1) every single assertion that we ever write is going to begin
with <span class="inlinecode"><span class="id"
type="keyword">fun</span></span> <span class="inlinecode"><span
class="id" type="var">st</span></span> <span class="inlinecode">⇒</span>
<span class="inlinecode"></span>; and (2) this state <span
class="inlinecode"><span class="id" type="var">st</span></span> is the
only one that we ever use to look up variables (we will never need to
talk about two different memory states at the same time). For discussing
examples informally, we'll adopt some simplifying conventions: we'll
drop the initial <span class="inlinecode"><span class="id"
type="keyword">fun</span></span> <span class="inlinecode"><span
class="id" type="var">st</span></span> <span
class="inlinecode">⇒</span>, and we'll write just <span
class="inlinecode"><span class="id" type="var">X</span></span> to mean
<span class="inlinecode"><span class="id" type="var">st</span></span>
<span class="inlinecode"><span class="id" type="var">X</span></span>.
Thus, instead of writing
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ (<span class="id" type="var">st</span> <span
class="id" type="var">Z</span>) × (<span class="id"
type="var">st</span> <span class="id" type="var">Z</span>) ≤ <span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span>\
                 ¬ ((<span class="id" type="var">S</span> (<span
class="id" type="var">st</span> <span class="id"
type="var">Z</span>)) × (<span class="id" type="var">S</span> (<span
class="id" type="var">st</span> <span class="id"
type="var">Z</span>)) ≤ <span class="id" type="var">m</span>)
<div class="paragraph">

</div>

</div>

we'll write just
<div class="paragraph">

</div>

<div class="code code-tight">

         <span class="id" type="var">Z</span> × <span class="id"
type="var">Z</span> ≤ <span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> \~((<span class="id"
type="var">S</span> <span class="id" type="var">Z</span>) × (<span
class="id" type="var">S</span> <span class="id"
type="var">Z</span>) ≤ <span class="id" type="var">m</span>).
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Given two assertions <span class="inlinecode"><span class="id"
type="var">P</span></span> and <span class="inlinecode"><span class="id"
type="var">Q</span></span>, we say that <span class="inlinecode"><span
class="id" type="var">P</span></span> *implies* <span
class="inlinecode"><span class="id" type="var">Q</span></span>, written
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span
style="font-family: arial;">⇾</span></span> <span
class="inlinecode"><span class="id" type="var">Q</span></span> (in
ASCII, <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">-</span><span
class="inlinecode">\></span><span class="inlinecode">\></span> <span
class="inlinecode"><span class="id" type="var">Q</span></span>), if,
whenever <span class="inlinecode"><span class="id"
type="var">P</span></span> holds in some state <span
class="inlinecode"><span class="id" type="var">st</span></span>, <span
class="inlinecode"><span class="id" type="var">Q</span></span> also
holds.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">assert\_implies</span> (<span class="id" type="var">P</span>
<span class="id" type="var">Q</span> : <span class="id"
type="var">Assertion</span>) : <span class="id"
type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">st</span>, <span class="id" type="var">P</span> <span
class="id" type="var">st</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span> <span class="id" type="var">st</span>.\
\
 <span class="id" type="keyword">Notation</span> "P <span
style="font-family: arial;">⇾</span> Q" :=\
   (<span class="id" type="var">assert\_implies</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span>) (<span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 80) : <span class="id"
type="var">hoare\_spec\_scope</span>.\
 <span class="id" type="keyword">Open</span> <span class="id"
type="keyword">Scope</span> <span class="id"
type="var">hoare\_spec\_scope</span>.\
\

</div>

<div class="doc">

We'll also have occasion to use the "iff" variant of implication between
assertions:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "P <span
style="font-family: arial;">⇿</span> Q" :=\
   (<span class="id" type="var">P</span> <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">Q</span> <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">P</span>) (<span class="id" type="tactic">at</span> <span
class="id" type="var">level</span> 80) : <span class="id"
type="var">hoare\_spec\_scope</span>.\
\

</div>

<div class="doc">

Hoare Triples {.section}
-------------

<div class="paragraph">

</div>

Next, we need a way of making formal claims about the behavior of
commands.
<div class="paragraph">

</div>

Since the behavior of a command is to transform one state to another, it
is natural to express claims about commands in terms of assertions that
are true before and after the command executes:
<div class="paragraph">

</div>

-   "If command <span class="inlinecode"><span class="id"
    type="var">c</span></span> is started in a state satisfying
    assertion <span class="inlinecode"><span class="id"
    type="var">P</span></span>, and if <span class="inlinecode"><span
    class="id" type="var">c</span></span> eventually terminates in some
    final state, then this final state will satisfy the assertion <span
    class="inlinecode"><span class="id" type="var">Q</span></span>."

<div class="paragraph">

</div>

Such a claim is called a *Hoare Triple*. The property <span
class="inlinecode"><span class="id" type="var">P</span></span> is called
the *precondition* of <span class="inlinecode"><span class="id"
type="var">c</span></span>, while <span class="inlinecode"><span
class="id" type="var">Q</span></span> is the *postcondition*. Formally:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">hoare\_triple</span>\
            (<span class="id" type="var">P</span>:<span class="id"
type="var">Assertion</span>) (<span class="id" type="var">c</span>:<span
class="id" type="var">com</span>) (<span class="id"
type="var">Q</span>:<span class="id" type="var">Assertion</span>) :
<span class="id" type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span>,\
        <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
        <span class="id" type="var">P</span> <span class="id"
type="var">st</span> <span style="font-family: arial;">→</span>\
        <span class="id" type="var">Q</span> <span class="id"
type="var">st'</span>.\
\

</div>

<div class="doc">

Since we'll be working a lot with Hoare triples, it's useful to have a
compact notation:
<div class="paragraph">

</div>

<div class="code code-tight">

       <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}.
<div class="paragraph">

</div>

</div>

(The traditional notation is <span class="inlinecode">{<span class="id"
type="var">P</span>}</span> <span class="inlinecode"><span class="id"
type="var">c</span></span> <span class="inlinecode">{<span class="id"
type="var">Q</span>}</span>, but single braces are already used for
other things in Coq.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "<span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{ Q <span
style="letter-spacing:-.4em;">}</span>}" :=\
   (<span class="id" type="var">hoare\_triple</span> <span class="id"
type="var">P</span> <span class="id" type="var">c</span> <span
class="id" type="var">Q</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 90,
<span class="id" type="var">c</span> <span class="id"
type="tactic">at</span> <span class="id" type="var">next</span> <span
class="id" type="var">level</span>)\
   : <span class="id" type="var">hoare\_spec\_scope</span>.\
\

</div>

<div class="doc">

(The <span class="inlinecode"><span class="id"
type="var">hoare\_spec\_scope</span></span> annotation here tells Coq
that this notation is not global but is intended to be used in
particular contexts. The <span class="inlinecode"><span class="id"
type="keyword">Open</span></span> <span class="inlinecode"><span
class="id" type="keyword">Scope</span></span> tells Coq that this file
is one such context.)
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (triples) {.section}

Paraphrase the following Hoare triples in English.
<div class="paragraph">

</div>

<div class="code code-tight">

   1) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">True</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">c</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">X</span> = 5<span
style="letter-spacing:-.4em;">}</span>}\
\
    2) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = <span class="id" type="var">m</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">c</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> + 5)<span style="letter-spacing:-.4em;">}</span>}\
\
    3) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> ≤ <span class="id" type="var">Y</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">c</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">Y</span> ≤ <span class="id"
type="var">X</span><span style="letter-spacing:-.4em;">}</span>}\
\
    4) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">True</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">c</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">False</span><span
style="letter-spacing:-.4em;">}</span>}\
\
    5) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = <span class="id" type="var">m</span><span
style="letter-spacing:-.4em;">}</span>} \
       <span class="id" type="var">c</span>\
       <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Y</span> = <span class="id"
type="var">real\_fact</span> <span class="id" type="var">m</span><span
style="letter-spacing:-.4em;">}</span>}.\
\
    6) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">True</span><span style="letter-spacing:-.4em;">}</span>} \
       <span class="id" type="var">c</span> \
       <span style="letter-spacing:-.4em;">{</span>{(<span class="id"
type="var">Z</span> × <span class="id" type="var">Z</span>) ≤ <span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> ¬ (((<span class="id"
type="var">S</span> <span class="id" type="var">Z</span>) × (<span
class="id" type="var">S</span> <span class="id"
type="var">Z</span>)) ≤ <span class="id" type="var">m</span>)<span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (valid\_triples) {.section}

Which of the following Hoare triples are *valid* — i.e., the claimed
relation between <span class="inlinecode"><span class="id"
type="var">P</span></span>, <span class="inlinecode"><span class="id"
type="var">c</span></span>, and <span class="inlinecode"><span
class="id" type="var">Q</span></span> is true?
<div class="paragraph">

</div>

<div class="code code-tight">

   1) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">True</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">X</span> ::= 5 <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = 5<span style="letter-spacing:-.4em;">}</span>}\
\
    2) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = 2<span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">X</span> ::= <span class="id" type="var">X</span> + 1 <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = 3<span style="letter-spacing:-.4em;">}</span>}\
\
    3) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">True</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">X</span> ::= 5; <span class="id"
type="var">Y</span> ::= 0 <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = 5<span style="letter-spacing:-.4em;">}</span>}\
\
    4) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = 2 <span style="font-family: arial;">∧</span> <span
class="id" type="var">X</span> = 3<span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">X</span> ::= 5 <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = 0<span style="letter-spacing:-.4em;">}</span>}\
\
    5) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">True</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">SKIP</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">False</span><span style="letter-spacing:-.4em;">}</span>}\
\
    6) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">False</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">SKIP</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">True</span><span style="letter-spacing:-.4em;">}</span>}\
\
    7) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">True</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">WHILE</span> <span class="id" type="var">True</span> <span
class="id" type="var">DO</span> <span class="id"
type="var">SKIP</span> <span class="id" type="var">END</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">False</span><span style="letter-spacing:-.4em;">}</span>}\
\
    8) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = 0<span style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> == 0 <span class="id" type="var">DO</span> <span
class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> + 1 <span class="id" type="var">END</span>\
       <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = 1<span style="letter-spacing:-.4em;">}</span>}\
\
    9) <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = 1<span style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ 0 <span class="id" type="var">DO</span> <span
class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> + 1 <span class="id" type="var">END</span>\
       <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = 100<span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

</div>

<div class="code code-tight">

<span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

(Note that we're using informal mathematical notations for expressions
inside of commands, for readability, rather than their formal <span
class="inlinecode"><span class="id" type="var">aexp</span></span> and
<span class="inlinecode"><span class="id" type="var">bexp</span></span>
encodings. We'll continue doing so throughout the chapter.)
<div class="paragraph">

</div>

To get us warmed up for what's coming, here are two simple facts about
Hoare triples.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_post\_true</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> : <span
class="id" type="var">Assertion</span>) <span class="id"
type="var">c</span>,\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">st</span>, <span class="id" type="var">Q</span> <span
class="id" type="var">st</span>) <span
style="font-family: arial;">→</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol1" class="togglescript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')">

<span class="show"></span>

</div>

<div id="proof1" class="proofscript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">c</span> <span class="id" type="var">H</span>.
<span class="id" type="tactic">unfold</span> <span class="id"
type="var">hoare\_triple</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">Heval</span> <span class="id"
type="var">HP</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">H</span>. <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_pre\_false</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> : <span
class="id" type="var">Assertion</span>) <span class="id"
type="var">c</span>,\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">st</span>, \~(<span class="id" type="var">P</span> <span
class="id" type="var">st</span>)) <span
style="font-family: arial;">→</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol2" class="togglescript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')">

<span class="show"></span>

</div>

<div id="proof2" class="proofscript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">c</span> <span class="id" type="var">H</span>.
<span class="id" type="tactic">unfold</span> <span class="id"
type="var">hoare\_triple</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">Heval</span> <span class="id"
type="var">HP</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">not</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span> <span
class="id" type="keyword">in</span> <span class="id"
type="var">HP</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HP</span>. <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Proof Rules {.section}
-----------

<div class="paragraph">

</div>

The goal of Hoare logic is to provide a *compositional* method for
proving the validity of Hoare triples. That is, the structure of a
program's correctness proof should mirror the structure of the program
itself. To this end, in the sections below, we'll introduce one rule for
reasoning about each of the different syntactic forms of commands in Imp
— one for assignment, one for sequencing, one for conditionals, etc. —
plus a couple of "structural" rules that are useful for gluing things
together. We will prove programs correct using these proof rules,
without ever unfolding the definition of <span class="inlinecode"><span
class="id" type="var">hoare\_triple</span></span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Assignment {.section}

<div class="paragraph">

</div>

The rule for assignment is the most fundamental of the Hoare logic proof
rules. Here's how it works.
<div class="paragraph">

</div>

Consider this (valid) Hoare triple:
<div class="paragraph">

</div>

<div class="code code-tight">

       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Y</span> = 1 <span
style="letter-spacing:-.4em;">}</span>}  <span class="id"
type="var">X</span> ::= <span class="id" type="var">Y</span>  <span
style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = 1 <span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

In English: if we start out in a state where the value of <span
class="inlinecode"><span class="id" type="var">Y</span></span> is <span
class="inlinecode">1</span> and we assign <span class="inlinecode"><span
class="id" type="var">Y</span></span> to <span class="inlinecode"><span
class="id" type="var">X</span></span>, then we'll finish in a state
where <span class="inlinecode"><span class="id"
type="var">X</span></span> is <span class="inlinecode">1</span>. That
is, the property of being equal to <span class="inlinecode">1</span>
gets transferred from <span class="inlinecode"><span class="id"
type="var">Y</span></span> to <span class="inlinecode"><span class="id"
type="var">X</span></span>.
<div class="paragraph">

</div>

Similarly, in
<div class="paragraph">

</div>

<div class="code code-tight">

       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Y</span> + <span class="id" type="var">Z</span> = 1 <span
style="letter-spacing:-.4em;">}</span>}  <span class="id"
type="var">X</span> ::= <span class="id" type="var">Y</span> + <span
class="id" type="var">Z</span>  <span
style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = 1 <span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

the same property (being equal to one) gets transferred to <span
class="inlinecode"><span class="id" type="var">X</span></span> from the
expression <span class="inlinecode"><span class="id"
type="var">Y</span></span> <span class="inlinecode">+</span> <span
class="inlinecode"><span class="id" type="var">Z</span></span> on the
right-hand side of the assignment.
<div class="paragraph">

</div>

More generally, if <span class="inlinecode"><span class="id"
type="var">a</span></span> is *any* arithmetic expression, then
<div class="paragraph">

</div>

<div class="code code-tight">

       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">a</span> = 1 <span
style="letter-spacing:-.4em;">}</span>}  <span class="id"
type="var">X</span> ::= <span class="id" type="var">a</span> <span
style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = 1 <span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

is a valid Hoare triple.
<div class="paragraph">

</div>

This can be made even more general. To conclude that an *arbitrary*
property <span class="inlinecode"><span class="id"
type="var">Q</span></span> holds after <span class="inlinecode"><span
class="id" type="var">X</span></span> <span
class="inlinecode">::=</span> <span class="inlinecode"><span class="id"
type="var">a</span></span>, we need to assume that <span
class="inlinecode"><span class="id" type="var">Q</span></span> holds
before <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode">::=</span> <span
class="inlinecode"><span class="id" type="var">a</span></span>, but
*with all occurrences of* <span class="inlinecode"><span class="id"
type="var">X</span></span> replaced by <span class="inlinecode"><span
class="id" type="var">a</span></span> in <span class="inlinecode"><span
class="id" type="var">Q</span></span>. This leads to the Hoare rule for
assignment
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Q</span> [<span class="id" type="var">X</span> <span
style="font-family: arial;">↦</span> <span class="id"
type="var">a</span>] <span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">X</span> ::= <span class="id"
type="var">a</span> <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Q</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

where "<span class="inlinecode"><span class="id"
type="var">Q</span></span> <span class="inlinecode">[<span class="id"
type="var">X</span></span> <span class="inlinecode"><span
style="font-family: arial;">↦</span></span> <span
class="inlinecode"><span class="id" type="var">a</span>]</span>" is
pronounced "<span class="inlinecode"><span class="id"
type="var">Q</span></span> where <span class="inlinecode"><span
class="id" type="var">a</span></span> is substituted for <span
class="inlinecode"><span class="id" type="var">X</span></span>".
<div class="paragraph">

</div>

For example, these are valid applications of the assignment rule:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{ (<span class="id"
type="var">X</span> ≤ 5) [<span class="id" type="var">X</span> <span
style="font-family: arial;">↦</span> <span class="id"
type="var">X</span> + 1]\
          <span class="id" type="var">i.e</span>., <span class="id"
type="var">X</span> + 1 ≤ 5 <span
style="letter-spacing:-.4em;">}</span>}  \
       <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> + 1  \
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> ≤ 5 <span style="letter-spacing:-.4em;">}</span>}\
\
       <span style="letter-spacing:-.4em;">{</span>{ (<span class="id"
type="var">X</span> = 3) [<span class="id" type="var">X</span> <span
style="font-family: arial;">↦</span> 3]\
          <span class="id" type="var">i.e</span>., 3 = 3<span
style="letter-spacing:-.4em;">}</span>}  \
       <span class="id" type="var">X</span> ::= 3  \
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = 3 <span style="letter-spacing:-.4em;">}</span>}\
\
       <span style="letter-spacing:-.4em;">{</span>{ (0 ≤ <span
class="id" type="var">X</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> ≤ 5) [<span class="id" type="var">X</span> <span
style="font-family: arial;">↦</span> 3]\
          <span class="id" type="var">i.e</span>., (0 ≤ 3 <span
style="font-family: arial;">∧</span> 3 ≤ 5)<span
style="letter-spacing:-.4em;">}</span>}  \
       <span class="id" type="var">X</span> ::= 3  \
       <span style="letter-spacing:-.4em;">{</span>{ 0 ≤ <span
class="id" type="var">X</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> ≤ 5 <span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

To formalize the rule, we must first formalize the idea of "substituting
an expression for an Imp variable in an assertion." That is, given a
proposition <span class="inlinecode"><span class="id"
type="var">P</span></span>, a variable <span class="inlinecode"><span
class="id" type="var">X</span></span>, and an arithmetic expression
<span class="inlinecode"><span class="id" type="var">a</span></span>, we
want to derive another proposition <span class="inlinecode"><span
class="id" type="var">P'</span></span> that is just the same as <span
class="inlinecode"><span class="id" type="var">P</span></span> except
that, wherever <span class="inlinecode"><span class="id"
type="var">P</span></span> mentions <span class="inlinecode"><span
class="id" type="var">X</span></span>, <span class="inlinecode"><span
class="id" type="var">P'</span></span> should instead mention <span
class="inlinecode"><span class="id" type="var">a</span></span>.
<div class="paragraph">

</div>

Since <span class="inlinecode"><span class="id"
type="var">P</span></span> is an arbitrary Coq proposition, we can't
directly "edit" its text. Instead, we can achieve the effect we want by
evaluating <span class="inlinecode"><span class="id"
type="var">P</span></span> in an updated state:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">assn\_sub</span> <span class="id" type="var">X</span> <span
class="id" type="var">a</span> <span class="id" type="var">P</span> :
<span class="id" type="var">Assertion</span> :=\
   <span class="id" type="keyword">fun</span> (<span class="id"
type="var">st</span> : <span class="id" type="var">state</span>) ⇒\
     <span class="id" type="var">P</span> (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">X</span> (<span class="id" type="var">aeval</span>
<span class="id" type="var">st</span> <span class="id"
type="var">a</span>)).\
\
 <span class="id" type="keyword">Notation</span> "P [ X |-\> a ]" :=
(<span class="id" type="var">assn\_sub</span> <span class="id"
type="var">X</span> <span class="id" type="var">a</span> <span
class="id" type="var">P</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 10).\
\

</div>

<div class="doc">

That is, <span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode">[<span class="id"
type="var">X</span></span> <span class="inlinecode"><span
style="font-family: arial;">↦</span></span> <span
class="inlinecode"><span class="id" type="var">a</span>]</span> is an
assertion <span class="inlinecode"><span class="id"
type="var">P'</span></span> that is just like <span
class="inlinecode"><span class="id" type="var">P</span></span> except
that, wherever <span class="inlinecode"><span class="id"
type="var">P</span></span> looks up the variable <span
class="inlinecode"><span class="id" type="var">X</span></span> in the
current state, <span class="inlinecode"><span class="id"
type="var">P'</span></span> instead uses the value of the expression
<span class="inlinecode"><span class="id" type="var">a</span></span>.
<div class="paragraph">

</div>

To see how this works, let's calculate what happens with a couple of
examples. First, suppose <span class="inlinecode"><span class="id"
type="var">P'</span></span> is <span class="inlinecode">(<span
class="id" type="var">X</span></span> <span class="inlinecode">≤</span>
<span class="inlinecode">5)</span> <span class="inlinecode">[<span
class="id" type="var">X</span></span> <span class="inlinecode"><span
style="font-family: arial;">↦</span></span> <span
class="inlinecode">3]</span> — that is, more formally, <span
class="inlinecode"><span class="id" type="var">P'</span></span> is the
Coq expression
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ \
       (<span class="id" type="keyword">fun</span> <span class="id"
type="var">st'</span> ⇒ <span class="id" type="var">st'</span> <span
class="id" type="var">X</span> ≤ 5) \
       (<span class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> (<span
class="id" type="var">aeval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">ANum</span> 3))),
<div class="paragraph">

</div>

</div>

which simplifies to
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ \
       (<span class="id" type="keyword">fun</span> <span class="id"
type="var">st'</span> ⇒ <span class="id" type="var">st'</span> <span
class="id" type="var">X</span> ≤ 5) \
       (<span class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> 3)
<div class="paragraph">

</div>

</div>

and further simplifies to
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ \
       ((<span class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> 3) <span
class="id" type="var">X</span>) ≤ 5)
<div class="paragraph">

</div>

</div>

and by further simplification to
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ \
       (3 ≤ 5).
<div class="paragraph">

</div>

</div>

That is, <span class="inlinecode"><span class="id"
type="var">P'</span></span> is the assertion that <span
class="inlinecode">3</span> is less than or equal to <span
class="inlinecode">5</span> (as expected).
<div class="paragraph">

</div>

For a more interesting example, suppose <span class="inlinecode"><span
class="id" type="var">P'</span></span> is <span
class="inlinecode">(<span class="id" type="var">X</span></span> <span
class="inlinecode">≤</span> <span class="inlinecode">5)</span> <span
class="inlinecode">[<span class="id" type="var">X</span></span> <span
class="inlinecode"><span style="font-family: arial;">↦</span></span>
<span class="inlinecode"><span class="id" type="var">X</span>+1]</span>.
Formally, <span class="inlinecode"><span class="id"
type="var">P'</span></span> is the Coq expression
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ \
       (<span class="id" type="keyword">fun</span> <span class="id"
type="var">st'</span> ⇒ <span class="id" type="var">st'</span> <span
class="id" type="var">X</span> ≤ 5) \
       (<span class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> (<span
class="id" type="var">aeval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">ANum</span> 1)))),
<div class="paragraph">

</div>

</div>

which simplifies to
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ \
       (((<span class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> (<span
class="id" type="var">aeval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id"
type="var">X</span>) (<span class="id"
type="var">ANum</span> 1))))) <span class="id" type="var">X</span>) ≤ 5
<div class="paragraph">

</div>

</div>

and further simplifies to
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ \
       (<span class="id" type="var">aeval</span> <span class="id"
type="var">st</span> (<span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">ANum</span> 1))) ≤ 5.
<div class="paragraph">

</div>

</div>

That is, <span class="inlinecode"><span class="id"
type="var">P'</span></span> is the assertion that <span
class="inlinecode"><span class="id" type="var">X</span>+1</span> is at
most <span class="inlinecode">5</span>.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

Now we can give the precise proof rule for assignment:
  
(hoare\_asgn)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{Q [X <span
style="font-family: arial;">↦</span> a]<span
style="letter-spacing:-.4em;">}</span>} X ::= a <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

We can prove formally that this rule is indeed valid.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_asgn</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">Q</span>
<span class="id" type="var">X</span> <span class="id"
type="var">a</span>,\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span> [<span class="id" type="var">X</span> <span
style="font-family: arial;">↦</span> <span class="id"
type="var">a</span>]<span style="letter-spacing:-.4em;">}</span>} (<span
class="id" type="var">X</span> ::= <span class="id" type="var">a</span>)
<span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol3" class="togglescript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')">

<span class="show"></span>

</div>

<div id="proof3" class="proofscript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">hoare\_triple</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">Q</span> <span class="id" type="var">X</span> <span
class="id" type="var">a</span> <span class="id" type="var">st</span>
<span class="id" type="var">st'</span> <span class="id"
type="var">HE</span> <span class="id" type="var">HQ</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>. <span class="id" type="tactic">subst</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">assn\_sub</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">HQ</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Here's a first formal proof using this rule.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">assn\_sub\_example</span> :\
   <span style="letter-spacing:-.4em;">{</span>{(<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> =
3) [<span class="id" type="var">X</span> <span
style="font-family: arial;">↦</span> <span class="id"
type="var">ANum</span> 3]<span style="letter-spacing:-.4em;">}</span>}\
   (<span class="id" type="var">X</span> ::= (<span class="id"
type="var">ANum</span> 3))\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> =
3<span style="letter-spacing:-.4em;">}</span>}.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_asgn</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (hoare\_asgn\_examples) {.section}

Translate these informal Hoare triples...
<div class="paragraph">

</div>

<div class="code code-tight">

    1) <span style="letter-spacing:-.4em;">{</span>{ (<span class="id"
type="var">X</span> ≤ 5) [<span class="id" type="var">X</span> <span
style="font-family: arial;">↦</span> <span class="id"
type="var">X</span> + 1] <span style="letter-spacing:-.4em;">}</span>}\
        <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> + 1\
        <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> ≤ 5 <span style="letter-spacing:-.4em;">}</span>}\
\
     2) <span style="letter-spacing:-.4em;">{</span>{ (0 ≤ <span
class="id" type="var">X</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> ≤ 5) [<span class="id" type="var">X</span> <span
style="font-family: arial;">↦</span> 3] <span
style="letter-spacing:-.4em;">}</span>}\
        <span class="id" type="var">X</span> ::= 3\
        <span style="letter-spacing:-.4em;">{</span>{ 0 ≤ <span
class="id" type="var">X</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> ≤ 5 <span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

...into formal statements <span class="inlinecode"><span class="id"
type="var">assn\_sub\_ex1</span>,</span> <span class="inlinecode"><span
class="id" type="var">assn\_sub\_ex2</span></span> and use <span
class="inlinecode"><span class="id" type="var">hoare\_asgn</span></span>
to prove them.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (hoare\_asgn\_wrong) {.section}

The assignment rule looks backward to almost everyone the first time
they see it. If it still seems backward to you, it may help to think a
little about alternative "forward" rules. Here is a seemingly natural
one:
  
(hoare\_asgn\_wrong)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{ True <span
style="letter-spacing:-.4em;">}</span>} X ::= a <span
style="letter-spacing:-.4em;">{</span>{ X = a <span
style="letter-spacing:-.4em;">}</span>}
Give a counterexample showing that this rule is incorrect (informally).
Hint: The rule universally quantifies over the arithmetic expression
<span class="inlinecode"><span class="id" type="var">a</span></span>,
and your counterexample needs to exhibit an <span
class="inlinecode"><span class="id" type="var">a</span></span> for which
the rule doesn't work.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (hoare\_asgn\_fwd) {.section}

However, using an auxiliary variable <span class="inlinecode"><span
class="id" type="var">m</span></span> to remember the original value of
<span class="inlinecode"><span class="id" type="var">X</span></span> we
can define a Hoare rule for assignment that does, intuitively, "work
forwards" rather than backwards.
  
(hoare\_asgn\_fwd)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{fun st ⇒ P st <span
style="font-family: arial;">∧</span> st X = m<span
style="letter-spacing:-.4em;">}</span>}
X ::= a
<span style="letter-spacing:-.4em;">{</span>{fun st ⇒ P st' <span
style="font-family: arial;">∧</span> st X = aeval st' a <span
style="letter-spacing:-.4em;">}</span>}
(where st' = update st X m)
Note that we use the original value of <span class="inlinecode"><span
class="id" type="var">X</span></span> to reconstruct the state <span
class="inlinecode"><span class="id" type="var">st'</span></span> before
the assignment took place. Prove that this rule is correct (the first
hypothesis is the functional extensionality axiom, which you will need
at some point). Also note that this rule is more complicated than <span
class="inlinecode"><span class="id"
type="var">hoare\_asgn</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_asgn\_fwd</span> :\
   (<span style="font-family: arial;">∀</span>{<span class="id"
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
class="id" type="var">f</span> = <span class="id" type="var">g</span>)
<span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">m</span> <span class="id" type="var">a</span> <span
class="id" type="var">P</span>,\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">P</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> = <span
class="id" type="var">m</span><span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">a</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">P</span> (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">X</span> <span class="id" type="var">m</span>)
<span style="font-family: arial;">∧</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> = <span
class="id" type="var">aeval</span> (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">X</span> <span class="id" type="var">m</span>)
<span class="id" type="var">a</span> <span
style="letter-spacing:-.4em;">}</span>}.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">functional\_extensionality</span> <span class="id"
type="var">m</span> <span class="id" type="var">a</span> <span
class="id" type="var">P</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, advanced (hoare\_asgn\_fwd\_exists) {.section}

Another way to define a forward rule for assignment is to existentially
quantify over the previous value of the assigned variable.
  
(hoare\_asgn\_fwd\_exists)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{fun st ⇒ P st<span
style="letter-spacing:-.4em;">}</span>}
X ::= a
<span style="letter-spacing:-.4em;">{</span>{fun st ⇒ <span
style="font-family: arial;">∃</span>m, P (update st X m) <span
style="font-family: arial;">∧</span>
st X = aeval (update st X m) a <span
style="letter-spacing:-.4em;">}</span>}

</div>

<div class="code code-tight">

<span
class="comment">(\* This rule was proposed by Nick Giannarakis and Zoe Paraskevopoulou. \*)</span>\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_asgn\_fwd\_exists</span> :\
   (<span style="font-family: arial;">∀</span>{<span class="id"
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
class="id" type="var">f</span> = <span class="id" type="var">g</span>)
<span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">a</span> <span class="id" type="var">P</span>,\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">P</span> <span class="id"
type="var">st</span><span style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">a</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
style="font-family: arial;">∃</span><span class="id"
type="var">m</span>, <span class="id" type="var">P</span> (<span
class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> <span
class="id" type="var">m</span>) <span
style="font-family: arial;">∧</span>\
                 <span class="id" type="var">st</span> <span class="id"
type="var">X</span> = <span class="id" type="var">aeval</span> (<span
class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> <span
class="id" type="var">m</span>) <span class="id" type="var">a</span>
<span style="letter-spacing:-.4em;">}</span>}.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">functional\_extensionality</span> <span class="id"
type="var">a</span> <span class="id" type="var">P</span>.\
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

### Consequence {.section}

<div class="paragraph">

</div>

Sometimes the preconditions and postconditions we get from the Hoare
rules won't quite be the ones we want in the particular situation at
hand — they may be logically equivalent but have a different syntactic
form that fails to unify with the goal we are trying to prove, or they
actually may be logically weaker (for preconditions) or stronger (for
postconditions) than what we need.
<div class="paragraph">

</div>

For instance, while
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{(<span class="id"
type="var">X</span> = 3) [<span class="id" type="var">X</span> <span
style="font-family: arial;">↦</span> 3]<span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">X</span> ::= 3 <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = 3<span style="letter-spacing:-.4em;">}</span>},
<div class="paragraph">

</div>

</div>

follows directly from the assignment rule,
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">True</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">X</span> ::= 3 <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> = 3<span style="letter-spacing:-.4em;">}</span>}.
<div class="paragraph">

</div>

</div>

does not. This triple is valid, but it is not an instance of <span
class="inlinecode"><span class="id" type="var">hoare\_asgn</span></span>
because <span class="inlinecode"><span class="id"
type="var">True</span></span> and <span class="inlinecode">(<span
class="id" type="var">X</span></span> <span class="inlinecode">=</span>
<span class="inlinecode">3)</span> <span class="inlinecode">[<span
class="id" type="var">X</span></span> <span class="inlinecode"><span
style="font-family: arial;">↦</span></span> <span
class="inlinecode">3]</span> are not syntactically equal assertions.
However, they are logically equivalent, so if one triple is valid, then
the other must certainly be as well. We might capture this observation
with the following rule:
<span style="letter-spacing:-.4em;">{</span>{P'<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
P <span style="font-family: arial;">⇿</span> P'
(hoare\_consequence\_pre\_equiv)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
Taking this line of thought a bit further, we can see that strengthening
the precondition or weakening the postcondition of a valid triple always
produces another valid triple. This observation is captured by two
*Rules of Consequence*.
<span style="letter-spacing:-.4em;">{</span>{P'<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
P <span style="font-family: arial;">⇾</span> P'
(hoare\_consequence\_pre)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{Q'<span
style="letter-spacing:-.4em;">}</span>}
Q' <span style="font-family: arial;">⇾</span> Q
(hoare\_consequence\_post)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

Here are the formal versions:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_consequence\_pre</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">P'</span> <span
class="id" type="var">Q</span> : <span class="id"
type="var">Assertion</span>) <span class="id" type="var">c</span>,\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P'</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">P'</span> <span style="font-family: arial;">→</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol4" class="togglescript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')">

<span class="show"></span>

</div>

<div id="proof4" class="proofscript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">P'</span> <span
class="id" type="var">Q</span> <span class="id" type="var">c</span>
<span class="id" type="var">Hhoare</span> <span class="id"
type="var">Himp</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">Hc</span> <span class="id" type="var">HP</span>.
<span class="id" type="tactic">apply</span> (<span class="id"
type="var">Hhoare</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span>).\
   <span class="id" type="tactic">assumption</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">Himp</span>.
<span class="id" type="tactic">assumption</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_consequence\_post</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">Q'</span> : <span class="id"
type="var">Assertion</span>) <span class="id" type="var">c</span>,\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q'</span><span style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">Q'</span> <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol5" class="togglescript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')">

<span class="show"></span>

</div>

<div id="proof5" class="proofscript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">Q'</span> <span class="id" type="var">c</span>
<span class="id" type="var">Hhoare</span> <span class="id"
type="var">Himp</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">Hc</span> <span class="id" type="var">HP</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">Himp</span>.\
   <span class="id" type="tactic">apply</span> (<span class="id"
type="var">Hhoare</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span>).\
   <span class="id" type="tactic">assumption</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

For example, we might use the first consequence rule like this:
<div class="paragraph">

</div>

<div class="code code-tight">

                <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
                 <span
style="letter-spacing:-.4em;">{</span>{ 1 = 1 <span
style="letter-spacing:-.4em;">}</span>} \
     <span class="id" type="var">X</span> ::= 1\
                 <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">X</span> = 1 <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

Or, formally...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">hoare\_asgn\_example1</span> :\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">True</span><span
style="letter-spacing:-.4em;">}</span>} (<span class="id"
type="var">X</span> ::= (<span class="id" type="var">ANum</span> 1))
<span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> =
1<span style="letter-spacing:-.4em;">}</span>}.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>\
     <span class="id" type="keyword">with</span> (<span class="id"
type="var">P'</span> := (<span class="id" type="keyword">fun</span>
<span class="id" type="var">st</span> ⇒ <span class="id"
type="var">st</span> <span class="id" type="var">X</span> = 1) [<span
class="id" type="var">X</span> <span
style="font-family: arial;">↦</span> <span class="id"
type="var">ANum</span> 1]).\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_asgn</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">assn\_sub</span>, <span class="id" type="var">update</span>.
<span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Finally, for convenience in some proofs, we can state a "combined" rule
of consequence that allows us to vary both the precondition and the
postcondition.
<span style="letter-spacing:-.4em;">{</span>{P'<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{Q'<span
style="letter-spacing:-.4em;">}</span>}
P <span style="font-family: arial;">⇾</span> P'
Q' <span style="font-family: arial;">⇾</span> Q
(hoare\_consequence)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_consequence</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">P'</span> <span
class="id" type="var">Q</span> <span class="id" type="var">Q'</span> :
<span class="id" type="var">Assertion</span>) <span class="id"
type="var">c</span>,\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P'</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q'</span><span style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">P'</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">Q'</span> <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol6" class="togglescript"
onclick="toggleDisplay('proof6');toggleDisplay('proofcontrol6')">

<span class="show"></span>

</div>

<div id="proof6" class="proofscript"
onclick="toggleDisplay('proof6');toggleDisplay('proofcontrol6')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">P'</span> <span
class="id" type="var">Q</span> <span class="id" type="var">Q'</span>
<span class="id" type="var">c</span> <span class="id"
type="var">Hht</span> <span class="id" type="var">HPP'</span> <span
class="id" type="var">HQ'Q</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_consequence\_pre</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">P'</span> :=
<span class="id" type="var">P'</span>).\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_consequence\_post</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">Q'</span> :=
<span class="id" type="var">Q'</span>).\
   <span class="id" type="tactic">assumption</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

### Digression: The <span class="inlinecode"><span class="id" type="tactic">eapply</span></span> Tactic {.section}

<div class="paragraph">

</div>

This is a good moment to introduce another convenient feature of Coq. We
had to write "<span class="inlinecode"><span class="id"
type="keyword">with</span></span> <span class="inlinecode">(<span
class="id" type="var">P'</span></span> <span
class="inlinecode">:=</span> <span class="inlinecode">...)</span>"
explicitly in the proof of <span class="inlinecode"><span class="id"
type="var">hoare\_asgn\_example1</span></span> and <span
class="inlinecode"><span class="id"
type="var">hoare\_consequence</span></span> above, to make sure that all
of the metavariables in the premises to the <span
class="inlinecode"><span class="id"
type="var">hoare\_consequence\_pre</span></span> rule would be set to
specific values. (Since <span class="inlinecode"><span class="id"
type="var">P'</span></span> doesn't appear in the conclusion of <span
class="inlinecode"><span class="id"
type="var">hoare\_consequence\_pre</span></span>, the process of
unifying the conclusion with the current goal doesn't constrain <span
class="inlinecode"><span class="id" type="var">P'</span></span> to a
specific assertion.)
<div class="paragraph">

</div>

This is a little annoying, both because the assertion is a bit long and
also because for <span class="inlinecode"><span class="id"
type="var">hoare\_asgn\_example1</span></span> the very next thing we
are going to do — applying the <span class="inlinecode"><span class="id"
type="var">hoare\_asgn</span></span> rule — will tell us exactly what it
should be! We can use <span class="inlinecode"><span class="id"
type="tactic">eapply</span></span> instead of <span
class="inlinecode"><span class="id" type="tactic">apply</span></span> to
tell Coq, essentially, "Be patient: The missing part is going to be
filled in soon."

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">hoare\_asgn\_example1'</span> :\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">True</span><span
style="letter-spacing:-.4em;">}</span>}\
   (<span class="id" type="var">X</span> ::= (<span class="id"
type="var">ANum</span> 1))\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> =
1<span style="letter-spacing:-.4em;">}</span>}.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_asgn</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

In general, <span class="inlinecode"><span class="id"
type="tactic">eapply</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> tactic works just like <span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
<span class="inlinecode"><span class="id" type="var">H</span></span>
except that, instead of failing if unifying the goal with the conclusion
of <span class="inlinecode"><span class="id" type="var">H</span></span>
does not determine how to instantiate all of the variables appearing in
the premises of <span class="inlinecode"><span class="id"
type="var">H</span></span>, <span class="inlinecode"><span class="id"
type="tactic">eapply</span></span> <span class="inlinecode"><span
class="id" type="var">H</span></span> will replace these variables with
so-called *existential variables* (written <span
class="inlinecode">?<span class="id" type="var">nnn</span></span>) as
placeholders for expressions that will be determined (by further
unification) later in the proof.
<div class="paragraph">

</div>

In order for <span class="inlinecode"><span class="id"
type="keyword">Qed</span></span> to succeed, all existential variables
need to be determined by the end of the proof. Otherwise Coq will
(rightly) refuse to accept the proof. Remember that the Coq tactics
build proof objects, and proof objects containing existential variables
are not complete.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">silly1</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>) (<span class="id"
type="var">Q</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span> <span class="id" type="var">y</span> : <span
class="id" type="var">nat</span>, <span class="id" type="var">P</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y</span>) <span style="font-family: arial;">→</span>\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span> <span class="id" type="var">y</span> : <span
class="id" type="var">nat</span>, <span class="id" type="var">P</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span> <span class="id" type="var">x</span>)
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">Q</span> 42.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">HP</span> <span class="id" type="var">HQ</span>.
<span class="id" type="tactic">eapply</span> <span class="id"
type="var">HQ</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">HP</span>.\
\

</div>

<div class="doc">

Coq gives a warning after <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">HP</span></span>:
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">No</span> <span class="id"
type="var">more</span> <span class="id" type="var">subgoals</span> <span
class="id" type="var">but</span> <span class="id"
type="var">non</span>-<span class="id"
type="var">instantiated</span> <span class="id"
type="var">existential</span> <span class="id"
type="var">variables</span>:\
      <span class="id" type="var">Existential</span> 1 =\
      ?171 : [<span class="id" type="var">P</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>\
              <span class="id" type="var">Q</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>\
              <span class="id" type="var">HP</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span> <span class="id" type="var">y</span> : <span
class="id" type="var">nat</span>, <span class="id"
type="var">P</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>\
              <span class="id" type="var">HQ</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span> <span class="id" type="var">y</span> : <span
class="id" type="var">nat</span>, <span class="id"
type="var">P</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span> <span class="id" type="var">x</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">nat</span>] \
   \
      (<span class="id" type="tactic">dependent</span> <span class="id"
type="var">evars</span>: ?171 <span class="id" type="var">open</span>,)\
\
      <span class="id" type="var">You</span> <span class="id"
type="var">can</span> <span class="id" type="var">use</span> <span
class="id" type="var">Grab</span> <span class="id"
type="var">Existential</span> <span class="id"
type="keyword">Variables</span>.
<div class="paragraph">

</div>

</div>

Trying to finish the proof with <span class="inlinecode"><span
class="id" type="keyword">Qed</span></span> gives an error:
        Error: Attempt to save a proof with existential variables still
        non-instantiated

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

An additional constraint is that existential variables cannot be
instantiated with terms containing (ordinary) variables that did not
exist at the time the existential variable was created.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">silly2</span> :\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>) (<span class="id"
type="var">Q</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∃</span><span class="id"
type="var">y</span>, <span class="id" type="var">P</span> 42 <span
class="id" type="var">y</span>) <span
style="font-family: arial;">→</span>\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span> <span class="id" type="var">y</span> : <span
class="id" type="var">nat</span>, <span class="id" type="var">P</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span> <span class="id" type="var">x</span>)
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">Q</span> 42.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">HP</span> <span class="id" type="var">HQ</span>.
<span class="id" type="tactic">eapply</span> <span class="id"
type="var">HQ</span>. <span class="id" type="tactic">destruct</span>
<span class="id" type="var">HP</span> <span class="id"
type="keyword">as</span> [<span class="id" type="var">y</span> <span
class="id" type="var">HP'</span>].\

</div>

<div class="doc">

Doing <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">HP'</span></span> above fails with the following
error:
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">Error</span>: <span class="id"
type="var">Impossible</span> <span class="id" type="var">to</span> <span
class="id" type="var">unify</span> "?175" <span class="id"
type="keyword">with</span> "y".
<div class="paragraph">

</div>

</div>

In this case there is an easy fix: doing <span class="inlinecode"><span
class="id" type="tactic">destruct</span></span> <span
class="inlinecode"><span class="id" type="var">HP</span></span> *before*
doing <span class="inlinecode"><span class="id"
type="tactic">eapply</span></span> <span class="inlinecode"><span
class="id" type="var">HQ</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Abort</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">silly2\_fixed</span> :\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>) (<span class="id"
type="var">Q</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∃</span><span class="id"
type="var">y</span>, <span class="id" type="var">P</span> 42 <span
class="id" type="var">y</span>) <span
style="font-family: arial;">→</span>\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span> <span class="id" type="var">y</span> : <span
class="id" type="var">nat</span>, <span class="id" type="var">P</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span> <span class="id" type="var">x</span>)
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">Q</span> 42.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">HP</span> <span class="id" type="var">HQ</span>.
<span class="id" type="tactic">destruct</span> <span class="id"
type="var">HP</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">y</span> <span class="id" type="var">HP'</span>].\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">HQ</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">HP'</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

In the last step we did <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> <span class="inlinecode"><span
class="id" type="var">HP'</span></span> which unifies the existential
variable in the goal with the variable <span class="inlinecode"><span
class="id" type="var">y</span></span>. The <span
class="inlinecode"><span class="id"
type="tactic">assumption</span></span> tactic doesn't work in this case,
since it cannot handle existential variables. However, Coq also provides
an <span class="inlinecode"><span class="id"
type="var">eassumption</span></span> tactic that solves the goal if one
of the premises matches the goal up to instantiations of existential
variables. We can use it instead of <span class="inlinecode"><span
class="id" type="tactic">apply</span></span> <span
class="inlinecode"><span class="id" type="var">HP'</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">silly2\_eassumption</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span>) (<span class="id"
type="var">Q</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>),\
   (<span style="font-family: arial;">∃</span><span class="id"
type="var">y</span>, <span class="id" type="var">P</span> 42 <span
class="id" type="var">y</span>) <span
style="font-family: arial;">→</span>\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">x</span> <span class="id" type="var">y</span> : <span
class="id" type="var">nat</span>, <span class="id" type="var">P</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span> <span class="id" type="var">x</span>)
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">Q</span> 42.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">HP</span> <span class="id" type="var">HQ</span>.
<span class="id" type="tactic">destruct</span> <span class="id"
type="var">HP</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">y</span> <span class="id" type="var">HP'</span>].
<span class="id" type="tactic">eapply</span> <span class="id"
type="var">HQ</span>. <span class="id" type="var">eassumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
\

</div>

<div class="doc">

#### Exercise: 2 stars (hoare\_asgn\_examples\_2) {.section}

Translate these informal Hoare triples...
<div class="paragraph">

</div>

<div class="code code-tight">

       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> + 1 ≤ 5 <span
style="letter-spacing:-.4em;">}</span>}  <span class="id"
type="var">X</span> ::= <span class="id" type="var">X</span> + 1  <span
style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> ≤ 5 <span style="letter-spacing:-.4em;">}</span>}\
        <span style="letter-spacing:-.4em;">{</span>{ 0 ≤ 3 <span
style="font-family: arial;">∧</span> 3 ≤ 5 <span
style="letter-spacing:-.4em;">}</span>}  <span class="id"
type="var">X</span> ::= 3  <span
style="letter-spacing:-.4em;">{</span>{ 0 ≤ <span class="id"
type="var">X</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">X</span> ≤ 5 <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

...into formal statements <span class="inlinecode"><span class="id"
type="var">assn\_sub\_ex1'</span>,</span> <span class="inlinecode"><span
class="id" type="var">assn\_sub\_ex2'</span></span> and use <span
class="inlinecode"><span class="id" type="var">hoare\_asgn</span></span>
and <span class="inlinecode"><span class="id"
type="var">hoare\_consequence\_pre</span></span> to prove them.

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

### Skip {.section}

<div class="paragraph">

</div>

Since <span class="inlinecode"><span class="id"
type="var">SKIP</span></span> doesn't change the state, it preserves any
property P:
  
(hoare\_skip)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} SKIP <span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>}

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_skip</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">P</span>,\
      <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">SKIP</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol7" class="togglescript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')">

<span class="show"></span>

</div>

<div id="proof7" class="proofscript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span> <span class="id" type="var">H</span>
<span class="id" type="var">HP</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>.
<span class="id" type="tactic">subst</span>.\
   <span class="id" type="tactic">assumption</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

### Sequencing {.section}

<div class="paragraph">

</div>

More interestingly, if the command <span class="inlinecode"><span
class="id" type="var">c1</span></span> takes any state where <span
class="inlinecode"><span class="id" type="var">P</span></span> holds to
a state where <span class="inlinecode"><span class="id"
type="var">Q</span></span> holds, and if <span class="inlinecode"><span
class="id" type="var">c2</span></span> takes any state where <span
class="inlinecode"><span class="id" type="var">Q</span></span> holds to
one where <span class="inlinecode"><span class="id"
type="var">R</span></span> holds, then doing <span
class="inlinecode"><span class="id" type="var">c1</span></span> followed
by <span class="inlinecode"><span class="id" type="var">c2</span></span>
will take any state where <span class="inlinecode"><span class="id"
type="var">P</span></span> holds to one where <span
class="inlinecode"><span class="id" type="var">R</span></span> holds:
<span style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} c1 <span
style="letter-spacing:-.4em;">{</span>{ Q <span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{ Q <span
style="letter-spacing:-.4em;">}</span>} c2 <span
style="letter-spacing:-.4em;">{</span>{ R <span
style="letter-spacing:-.4em;">}</span>}
(hoare\_seq)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} c1;;c2 <span
style="letter-spacing:-.4em;">{</span>{ R <span
style="letter-spacing:-.4em;">}</span>}

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_seq</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> <span class="id"
type="var">R</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c2</span>,\
      <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c2</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">R</span><span style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">→</span>\
      <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c1</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">→</span>\
      <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c1</span>;;<span class="id" type="var">c2</span>
<span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">R</span><span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol8" class="togglescript"
onclick="toggleDisplay('proof8');toggleDisplay('proofcontrol8')">

<span class="show"></span>

</div>

<div id="proof8" class="proofscript"
onclick="toggleDisplay('proof8');toggleDisplay('proofcontrol8')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">R</span> <span class="id" type="var">c1</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">H1</span> <span class="id" type="var">H2</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>
<span class="id" type="var">H12</span> <span class="id"
type="var">Pre</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H12</span>; <span class="id" type="tactic">subst</span>.\
   <span class="id" type="tactic">apply</span> (<span class="id"
type="var">H1</span> <span class="id" type="var">st'0</span> <span
class="id" type="var">st'</span>); <span class="id"
type="tactic">try</span> <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="tactic">apply</span> (<span class="id"
type="var">H2</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'0</span>); <span class="id"
type="tactic">assumption</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Note that, in the formal rule <span class="inlinecode"><span class="id"
type="var">hoare\_seq</span></span>, the premises are given in
"backwards" order (<span class="inlinecode"><span class="id"
type="var">c2</span></span> before <span class="inlinecode"><span
class="id" type="var">c1</span></span>). This matches the natural flow
of information in many of the situations where we'll use the rule: the
natural way to construct a Hoare-logic proof is to begin at the end of
the program (with the final postcondition) and push postconditions
backwards through commands until we reach the beginning.
<div class="paragraph">

</div>

Informally, a nice way of recording a proof using the sequencing rule is
as a "decorated program" where the intermediate assertion <span
class="inlinecode"><span class="id" type="var">Q</span></span> is
written between <span class="inlinecode"><span class="id"
type="var">c1</span></span> and <span class="inlinecode"><span
class="id" type="var">c2</span></span>:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">a</span> = <span class="id" type="var">n</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">a</span>;;\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">n</span> <span
style="letter-spacing:-.4em;">}</span>}      \<---- <span class="id"
type="var">decoration</span> <span class="id"
type="keyword">for</span> <span class="id" type="var">Q</span>\
     <span class="id" type="var">SKIP</span>\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">n</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">hoare\_asgn\_example3</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">a</span>
<span class="id" type="var">n</span>,\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">aeval</span> <span class="id" type="var">st</span>
<span class="id" type="var">a</span> = <span class="id"
type="var">n</span><span style="letter-spacing:-.4em;">}</span>}\
   (<span class="id" type="var">X</span> ::= <span class="id"
type="var">a</span>;; <span class="id" type="var">SKIP</span>)\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> =
<span class="id" type="var">n</span><span
style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol9" class="togglescript"
onclick="toggleDisplay('proof9');toggleDisplay('proofcontrol9')">

<span class="show"></span>

</div>

<div id="proof9" class="proofscript"
onclick="toggleDisplay('proof9');toggleDisplay('proofcontrol9')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">a</span> <span class="id" type="var">n</span>. <span
class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_seq</span>.\
   <span class="id" type="var">Case</span> "right part of seq".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_skip</span>.\
   <span class="id" type="var">Case</span> "left part of seq".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">hoare\_asgn</span>.\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">subst</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

You will most often use <span class="inlinecode"><span class="id"
type="var">hoare\_seq</span></span> and <span class="inlinecode"><span
class="id" type="var">hoare\_consequence\_pre</span></span> in
conjunction with the <span class="inlinecode"><span class="id"
type="tactic">eapply</span></span> tactic, as done above.
<div class="paragraph">

</div>

#### Exercise: 2 stars (hoare\_asgn\_example4) {.section}

Translate this "decorated program" into a formal proof:
<div class="paragraph">

</div>

<div class="code code-tight">

                   <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
                    <span
style="letter-spacing:-.4em;">{</span>{ 1 = 1 <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">X</span> ::= 1;;\
                    <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">X</span> = 1 <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
                    <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">X</span> = 1 <span
style="font-family: arial;">∧</span> 2 = 2 <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Y</span> ::= 2\
                    <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">X</span> = 1 <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Y</span> = 2 <span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">hoare\_asgn\_example4</span> :\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">True</span><span
style="letter-spacing:-.4em;">}</span>} (<span class="id"
type="var">X</span> ::= (<span class="id" type="var">ANum</span> 1);;
<span class="id" type="var">Y</span> ::= (<span class="id"
type="var">ANum</span> 2))\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> = 1
<span style="font-family: arial;">∧</span> <span class="id"
type="var">st</span> <span class="id" type="var">Y</span> = 2<span
style="letter-spacing:-.4em;">}</span>}.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (swap\_exercise) {.section}

Write an Imp program <span class="inlinecode"><span class="id"
type="var">c</span></span> that swaps the values of <span
class="inlinecode"><span class="id" type="var">X</span></span> and <span
class="inlinecode"><span class="id" type="var">Y</span></span> and show
(in Coq) that it satisfies the following specification:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">X</span> ≤ <span class="id" type="var">Y</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">c</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">Y</span> ≤ <span class="id"
type="var">X</span><span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">swap\_program</span> : <span class="id" type="var">com</span>
:=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">swap\_exercise</span> :\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> ≤
<span class="id" type="var">st</span> <span class="id"
type="var">Y</span><span style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">swap\_program</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">Y</span> ≤
<span class="id" type="var">st</span> <span class="id"
type="var">X</span><span style="letter-spacing:-.4em;">}</span>}.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (hoarestate1) {.section}

Explain why the following proposition can't be proven:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="font-family: arial;">∀</span>(<span class="id"
type="var">a</span> : <span class="id" type="var">aexp</span>) (<span
class="id" type="var">n</span> : <span class="id"
type="var">nat</span>),\
          <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">aeval</span> <span class="id"
type="var">st</span> <span class="id" type="var">a</span> = <span
class="id" type="var">n</span><span
style="letter-spacing:-.4em;">}</span>}\
          (<span class="id" type="var">X</span> ::= (<span class="id"
type="var">ANum</span> 3);; <span class="id"
type="var">Y</span> ::= <span class="id" type="var">a</span>)\
          <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id"
type="var">Y</span> = <span class="id" type="var">n</span><span
style="letter-spacing:-.4em;">}</span>}.
<div class="paragraph">

</div>

</div>

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

### Conditionals {.section}

<div class="paragraph">

</div>

What sort of rule do we want for reasoning about conditional commands?
Certainly, if the same assertion <span class="inlinecode"><span
class="id" type="var">Q</span></span> holds after executing either
branch, then it holds after the whole conditional. So we might be
tempted to write:
<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} c1 <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} c2 <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
 

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} IFB b THEN c1 ELSE c2 <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
However, this is rather weak. For example, using this rule, we cannot
show that:
<div class="paragraph">

</div>

<div class="code code-tight">

     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">True</span> <span style="letter-spacing:-.4em;">}</span>} \
      <span class="id" type="var">IFB</span> <span class="id"
type="var">X</span> == 0\
      <span class="id" type="var">THEN</span> <span class="id"
type="var">Y</span> ::= 2\
      <span class="id" type="var">ELSE</span> <span class="id"
type="var">Y</span> ::= <span class="id" type="var">X</span> + 1 \
      <span class="id" type="var">FI</span>\
      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> ≤ <span class="id" type="var">Y</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

since the rule tells us nothing about the state in which the assignments
take place in the "then" and "else" branches.
<div class="paragraph">

</div>

But we can actually say something more precise. In the "then" branch, we
know that the boolean expression <span class="inlinecode"><span
class="id" type="var">b</span></span> evaluates to <span
class="inlinecode"><span class="id" type="var">true</span></span>, and
in the "else" branch, we know it evaluates to <span
class="inlinecode"><span class="id" type="var">false</span></span>.
Making this information available in the premises of the rule gives us
more information to work with when reasoning about the behavior of <span
class="inlinecode"><span class="id" type="var">c1</span></span> and
<span class="inlinecode"><span class="id" type="var">c2</span></span>
(i.e., the reasons why they establish the postcondition <span
class="inlinecode"><span class="id" type="var">Q</span></span>).
<div class="paragraph">

</div>

<span style="letter-spacing:-.4em;">{</span>{P <span
style="font-family: arial;">∧</span>  b<span
style="letter-spacing:-.4em;">}</span>} c1 <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{P <span
style="font-family: arial;">∧</span> \~b<span
style="letter-spacing:-.4em;">}</span>} c2 <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
(hoare\_if)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} IFB b THEN c1 ELSE c2 FI <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

To interpret this rule formally, we need to do a little work. Strictly
speaking, the assertion we've written, <span class="inlinecode"><span
class="id" type="var">P</span></span> <span class="inlinecode"><span
style="font-family: arial;">∧</span></span> <span
class="inlinecode"><span class="id" type="var">b</span></span>, is the
conjunction of an assertion and a boolean expression — i.e., it doesn't
typecheck. To fix this, we need a way of formally "lifting" any bexp
<span class="inlinecode"><span class="id" type="var">b</span></span> to
an assertion. We'll write <span class="inlinecode"><span class="id"
type="var">bassn</span></span> <span class="inlinecode"><span class="id"
type="var">b</span></span> for the assertion "the boolean expression
<span class="inlinecode"><span class="id" type="var">b</span></span>
evaluates to <span class="inlinecode"><span class="id"
type="var">true</span></span> (in the given state)."

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> : <span
class="id" type="var">Assertion</span> :=\
   <span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ (<span class="id" type="var">beval</span> <span
class="id" type="var">st</span> <span class="id" type="var">b</span> =
<span class="id" type="var">true</span>).\
\

</div>

<div class="doc">

A couple of useful facts about <span class="inlinecode"><span class="id"
type="var">bassn</span></span>:

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
<div id="proofcontrol10" class="togglescript"
onclick="toggleDisplay('proof10');toggleDisplay('proofcontrol10')">

<span class="show"></span>

</div>

<div id="proof10" class="proofscript"
onclick="toggleDisplay('proof10');toggleDisplay('proofcontrol10')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">st</span> <span
class="id" type="var">Hbe</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bassn</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">bexp\_eval\_false</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">st</span>,\
   <span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span> ¬ ((<span class="id"
type="var">bassn</span> <span class="id" type="var">b</span>) <span
class="id" type="var">st</span>).\
<div id="proofcontrol11" class="togglescript"
onclick="toggleDisplay('proof11');toggleDisplay('proofcontrol11')">

<span class="show"></span>

</div>

<div id="proof11" class="proofscript"
onclick="toggleDisplay('proof11');toggleDisplay('proofcontrol11')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">st</span> <span
class="id" type="var">Hbe</span> <span class="id"
type="var">contra</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bassn</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">contra</span>.\
   <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">contra</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hbe</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hbe</span>.
<span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Now we can formalize the Hoare proof rule for conditionals and prove it
correct.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_if</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> <span class="id"
type="var">b</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c2</span>,\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">P</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">c1</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">Q</span><span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">→</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">P</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">∧</span> \~(<span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span>)<span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">c2</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">Q</span><span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">→</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} (<span
class="id" type="var">IFB</span> <span class="id" type="var">b</span>
<span class="id" type="var">THEN</span> <span class="id"
type="var">c1</span> <span class="id" type="var">ELSE</span> <span
class="id" type="var">c2</span> <span class="id" type="var">FI</span>)
<span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol12" class="togglescript"
onclick="toggleDisplay('proof12');toggleDisplay('proofcontrol12')">

<span class="show"></span>

</div>

<div id="proof12" class="proofscript"
onclick="toggleDisplay('proof12');toggleDisplay('proofcontrol12')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">b</span> <span class="id" type="var">c1</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">HTrue</span> <span class="id" type="var">HFalse</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>
<span class="id" type="var">HE</span> <span class="id"
type="var">HP</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>; <span class="id" type="tactic">subst</span>.\
   <span class="id" type="var">Case</span> "b is true".\
     <span class="id" type="tactic">apply</span> (<span class="id"
type="var">HTrue</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span>).\
       <span class="id" type="tactic">assumption</span>.\
       <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">assumption</span>.\
              <span class="id" type="tactic">apply</span> <span
class="id" type="var">bexp\_eval\_true</span>. <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "b is false".\
     <span class="id" type="tactic">apply</span> (<span class="id"
type="var">HFalse</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span>).\
       <span class="id" type="tactic">assumption</span>.\
       <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">assumption</span>.\
              <span class="id" type="tactic">apply</span> <span
class="id" type="var">bexp\_eval\_false</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\
\

</div>

<div class="doc">

Hoare Logic: So Far {.section}
===================

<div class="paragraph">

</div>

<div class="paragraph">

</div>

Idea: create a *domain specific logic* for reasoning about properties of
Imp programs.
<div class="paragraph">

</div>

-   This hides the low-level details of the semantics of the program
-   Leads to a compositional reasoning process

<div class="paragraph">

</div>

The basic structure is given by *Hoare triples* of the form:
<div class="paragraph">

</div>

<div class="code code-tight">

  <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">P</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">Q</span></span> are predicates about the state of the Imp
    program
-   "If command <span class="inlinecode"><span class="id"
    type="var">c</span></span> is started in a state satisfying
    assertion <span class="inlinecode"><span class="id"
    type="var">P</span></span>, and if <span class="inlinecode"><span
    class="id" type="var">c</span></span> eventually terminates in some
    final state, then this final state will satisfy the assertion <span
    class="inlinecode"><span class="id" type="var">Q</span></span>."

<div class="paragraph">

</div>

Hoare Logic Rules (so far) {.section}
--------------------------

<div class="paragraph">

</div>

<div class="paragraph">

</div>

  
(hoare\_asgn)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{Q [X <span
style="font-family: arial;">↦</span> a]<span
style="letter-spacing:-.4em;">}</span>} X::=a <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
  
(hoare\_skip)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} SKIP <span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} c1 <span
style="letter-spacing:-.4em;">{</span>{ Q <span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{ Q <span
style="letter-spacing:-.4em;">}</span>} c2 <span
style="letter-spacing:-.4em;">{</span>{ R <span
style="letter-spacing:-.4em;">}</span>}
(hoare\_seq)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} c1;;c2 <span
style="letter-spacing:-.4em;">{</span>{ R <span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{P <span
style="font-family: arial;">∧</span>  b<span
style="letter-spacing:-.4em;">}</span>} c1 <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{P <span
style="font-family: arial;">∧</span> \~b<span
style="letter-spacing:-.4em;">}</span>} c2 <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
(hoare\_if)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} IFB b THEN c1 ELSE c2 FI <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{P'<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{Q'<span
style="letter-spacing:-.4em;">}</span>}
P <span style="font-family: arial;">⇾</span> P'
Q' <span style="font-family: arial;">⇾</span> Q
(hoare\_consequence)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

### Example {.section}

Here is a formal proof that the program we used to motivate the rule
satisfies the specification we gave.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">if\_example</span> :\
     <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">True</span><span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">IFB</span> (<span class="id"
type="var">BEq</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
0))\
     <span class="id" type="var">THEN</span> (<span class="id"
type="var">Y</span> ::= (<span class="id" type="var">ANum</span> 2))\
     <span class="id" type="var">ELSE</span> (<span class="id"
type="var">Y</span> ::= <span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 1))\
   <span class="id" type="var">FI</span>\
     <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> ≤
<span class="id" type="var">st</span> <span class="id"
type="var">Y</span><span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol13" class="togglescript"
onclick="toggleDisplay('proof13');toggleDisplay('proofcontrol13')">

<span class="show"></span>

</div>

<div id="proof13" class="proofscript"
onclick="toggleDisplay('proof13');toggleDisplay('proofcontrol13')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_if</span>.\
   <span class="id" type="var">Case</span> "Then".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">hoare\_asgn</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bassn</span>, <span class="id" type="var">assn\_sub</span>,
<span class="id" type="var">update</span>, <span class="id"
type="var">assert\_implies</span>.\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">st</span> [<span
class="id" type="var">\_</span> <span class="id" type="var">H</span>].\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">beq\_nat\_true</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">omega</span>.\
   <span class="id" type="var">Case</span> "Else".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">hoare\_asgn</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">assn\_sub</span>, <span class="id" type="var">update</span>,
<span class="id" type="var">assert\_implies</span>.\
     <span class="id" type="tactic">simpl</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">st</span> <span
class="id" type="var">\_</span>. <span class="id"
type="tactic">omega</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 2 stars (if\_minus\_plus) {.section}

Prove the following hoare triple using <span class="inlinecode"><span
class="id" type="var">hoare\_if</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">if\_minus\_plus</span> :\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">True</span><span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">IFB</span> (<span class="id"
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
   <span class="id" type="var">FI</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">Y</span> =
<span class="id" type="var">st</span> <span class="id"
type="var">X</span> + <span class="id" type="var">st</span> <span
class="id" type="var">Z</span><span
style="letter-spacing:-.4em;">}</span>}.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

### Exercise: One-sided conditionals {.section}

<div class="paragraph">

</div>

#### Exercise: 4 stars (if1\_hoare) {.section}

<div class="paragraph">

</div>

In this exercise we consider extending Imp with "one-sided conditionals"
of the form <span class="inlinecode"><span class="id"
type="var">IF1</span></span> <span class="inlinecode"><span class="id"
type="var">b</span></span> <span class="inlinecode"><span class="id"
type="var">THEN</span></span> <span class="inlinecode"><span class="id"
type="var">c</span></span> <span class="inlinecode"><span class="id"
type="var">FI</span></span>. Here <span class="inlinecode"><span
class="id" type="var">b</span></span> is a boolean expression, and <span
class="inlinecode"><span class="id" type="var">c</span></span> is a
command. If <span class="inlinecode"><span class="id"
type="var">b</span></span> evaluates to <span class="inlinecode"><span
class="id" type="var">true</span></span>, then command <span
class="inlinecode"><span class="id" type="var">c</span></span> is
evaluated. If <span class="inlinecode"><span class="id"
type="var">b</span></span> evaluates to <span class="inlinecode"><span
class="id" type="var">false</span></span>, then <span
class="inlinecode"><span class="id" type="var">IF1</span></span> <span
class="inlinecode"><span class="id" type="var">b</span></span> <span
class="inlinecode"><span class="id" type="var">THEN</span></span> <span
class="inlinecode"><span class="id" type="var">c</span></span> <span
class="inlinecode"><span class="id" type="var">FI</span></span> does
nothing.
<div class="paragraph">

</div>

We recommend that you do this exercise before the ones that follow, as
it should help solidify your understanding of the material.
<div class="paragraph">

</div>

The first step is to extend the syntax of commands and introduce the
usual notations. (We've done this for you. We use a separate module to
prevent polluting the global name space.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">If1</span>.\
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
   | <span class="id" type="var">CIf1</span> : <span class="id"
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
type="var">c</span> ";"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "IFB" | <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">c</span> "WHILE" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "CIF1"
].\
\
 <span class="id" type="keyword">Notation</span> "'SKIP'" :=\
   <span class="id" type="var">CSkip</span>.\
 <span class="id" type="keyword">Notation</span> "c1 ;; c2" :=\
   (<span class="id" type="var">CSeq</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c2</span>) (<span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 80, <span class="id" type="var">right</span>
<span class="id" type="var">associativity</span>).\
 <span class="id" type="keyword">Notation</span> "X '::=' a" :=\
   (<span class="id" type="var">CAss</span> <span class="id"
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
 <span class="id" type="keyword">Notation</span> "'IF1' b 'THEN' c 'FI'"
:=\
   (<span class="id" type="var">CIf1</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span>) (<span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 80, <span class="id" type="var">right</span>
<span class="id" type="var">associativity</span>).\
\

</div>

<div class="doc">

Next we need to extend the evaluation relation to accommodate <span
class="inlinecode"><span class="id" type="var">IF1</span></span>
branches. This is for you to do... What rule(s) need to be added to
<span class="inlinecode"><span class="id" type="var">ceval</span></span>
to evaluate one-sided conditionals?

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

Now we repeat (verbatim) the definition and notation of Hoare triples.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">hoare\_triple</span> (<span class="id"
type="var">P</span>:<span class="id" type="var">Assertion</span>) (<span
class="id" type="var">c</span>:<span class="id" type="var">com</span>)
(<span class="id" type="var">Q</span>:<span class="id"
type="var">Assertion</span>) : <span class="id"
type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span>,\
        <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
        <span class="id" type="var">P</span> <span class="id"
type="var">st</span> <span style="font-family: arial;">→</span>\
        <span class="id" type="var">Q</span> <span class="id"
type="var">st'</span>.\
\
 <span class="id" type="keyword">Notation</span> "<span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{ Q <span
style="letter-spacing:-.4em;">}</span>}" := (<span class="id"
type="var">hoare\_triple</span> <span class="id" type="var">P</span>
<span class="id" type="var">c</span> <span class="id"
type="var">Q</span>)\
                                   (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 90,
<span class="id" type="var">c</span> <span class="id"
type="tactic">at</span> <span class="id" type="var">next</span> <span
class="id" type="var">level</span>)\
                                   : <span class="id"
type="var">hoare\_spec\_scope</span>.\
\

</div>

<div class="doc">

Finally, we (i.e., you) need to state and prove a theorem, <span
class="inlinecode"><span class="id" type="var">hoare\_if1</span></span>,
that expresses an appropriate Hoare logic proof rule for one-sided
conditionals. Try to come up with a rule that is both sound and as
precise as possible.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\

</div>

<div class="doc">

For full credit, prove formally <span class="inlinecode"><span
class="id" type="var">hoare\_if1\_good</span></span> that your rule is
precise enough to show the following valid Hoare triple:
<div class="paragraph">

</div>

<div class="code code-tight">

  <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> + <span class="id" type="var">Y</span> = <span
class="id" type="var">Z</span> <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">IF1</span> <span class="id"
type="var">Y</span> ≠ 0 <span class="id" type="var">THEN</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> + <span class="id" type="var">Y</span>\
   <span class="id" type="var">FI</span>\
   <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">Z</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Hint: Your proof of this triple may need to use the other proof rules
also. Because we're working in a separate module, you'll need to copy
here the rules you find necessary.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">hoare\_if1\_good</span> :\
   <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> +
<span class="id" type="var">st</span> <span class="id"
type="var">Y</span> = <span class="id" type="var">st</span> <span
class="id" type="var">Z</span> <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">IF1</span> <span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">Y</span>)
(<span class="id" type="var">ANum</span> 0)) <span class="id"
type="var">THEN</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">AId</span>
<span class="id" type="var">Y</span>)\
   <span class="id" type="var">FI</span>\
   <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> =
<span class="id" type="var">st</span> <span class="id"
type="var">Z</span> <span style="letter-spacing:-.4em;">}</span>}.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">If1</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Loops {.section}

<div class="paragraph">

</div>

Finally, we need a rule for reasoning about while loops.
<div class="paragraph">

</div>

Suppose we have a loop
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id" type="var">END</span>
<div class="paragraph">

</div>

</div>

and we want to find a pre-condition <span class="inlinecode"><span
class="id" type="var">P</span></span> and a post-condition <span
class="inlinecode"><span class="id" type="var">Q</span></span> such that
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id"
type="var">END</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">Q</span><span
style="letter-spacing:-.4em;">}</span>} 
<div class="paragraph">

</div>

</div>

is a valid triple.
<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

First of all, let's think about the case where <span
class="inlinecode"><span class="id" type="var">b</span></span> is false
at the beginning — i.e., let's assume that the loop body never executes
at all. In this case, the loop behaves like <span
class="inlinecode"><span class="id" type="var">SKIP</span></span>, so we
might be tempted to write:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id"
type="var">END</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">P</span><span
style="letter-spacing:-.4em;">}</span>}.
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

<div class="paragraph">

</div>

But, as we remarked above for the conditional, we know a little more at
the end — not just <span class="inlinecode"><span class="id"
type="var">P</span></span>, but also the fact that <span
class="inlinecode"><span class="id" type="var">b</span></span> is false
in the current state. So we can enrich the postcondition a little:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c</span> <span class="id"
type="var">END</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> ¬<span class="id"
type="var">b</span><span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

<div class="paragraph">

</div>

What about the case where the loop body *does* get executed? In order to
ensure that <span class="inlinecode"><span class="id"
type="var">P</span></span> holds when the loop finally exits, we
certainly need to make sure that the command <span
class="inlinecode"><span class="id" type="var">c</span></span>
guarantees that <span class="inlinecode"><span class="id"
type="var">P</span></span> holds whenever <span class="inlinecode"><span
class="id" type="var">c</span></span> is finished. Moreover, since <span
class="inlinecode"><span class="id" type="var">P</span></span> holds at
the beginning of the first execution of <span class="inlinecode"><span
class="id" type="var">c</span></span>, and since each execution of <span
class="inlinecode"><span class="id" type="var">c</span></span>
re-establishes <span class="inlinecode"><span class="id"
type="var">P</span></span> when it finishes, we can always assume that
<span class="inlinecode"><span class="id" type="var">P</span></span>
holds at the beginning of <span class="inlinecode"><span class="id"
type="var">c</span></span>. This leads us to the following rule:
<div class="paragraph">

</div>

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>}
 

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} WHILE b DO c END <span
style="letter-spacing:-.4em;">{</span>{P <span
style="font-family: arial;">∧</span> \~b<span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

This is almost the rule we want, but again it can be improved a little:
at the beginning of the loop body, we know not only that <span
class="inlinecode"><span class="id" type="var">P</span></span> holds,
but also that the guard <span class="inlinecode"><span class="id"
type="var">b</span></span> is true in the current state. This gives us a
little more information to use in reasoning about <span
class="inlinecode"><span class="id" type="var">c</span></span> (showing
that it establishes the invariant by the time it finishes). This gives
us the final version of the rule:
<div class="paragraph">

</div>

<span style="letter-spacing:-.4em;">{</span>{P <span
style="font-family: arial;">∧</span> b<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>}
(hoare\_while)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} WHILE b DO c END <span
style="letter-spacing:-.4em;">{</span>{P <span
style="font-family: arial;">∧</span> \~b<span
style="letter-spacing:-.4em;">}</span>}
The proposition <span class="inlinecode"><span class="id"
type="var">P</span></span> is called an *invariant* of the loop.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">hoare\_while</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">b</span> <span class="id"
type="var">c</span>,\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">P</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">c</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">P</span><span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">→</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">WHILE</span> <span class="id" type="var">b</span>
<span class="id" type="var">DO</span> <span class="id"
type="var">c</span> <span class="id" type="var">END</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">P</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">∧</span> ¬ (<span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span>)<span
style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol14" class="togglescript"
onclick="toggleDisplay('proof14');toggleDisplay('proofcontrol14')">

<span class="show"></span>

</div>

<div id="proof14" class="proofscript"
onclick="toggleDisplay('proof14');toggleDisplay('proofcontrol14')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span> <span class="id" type="var">Hhoare</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span> <span class="id" type="var">He</span> <span
class="id" type="var">HP</span>.\
   <span
class="comment">(\* Like we've seen before, we need to reason by induction \
      on <span class="inlinecode"><span class="id"
type="var">He</span></span>, because, in the "keep looping" case, its hypotheses \
      talk about the whole loop instead of just <span
class="inlinecode"><span class="id"
type="var">c</span></span>. \*)</span>\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">WHILE</span> <span class="id" type="var">b</span> <span
class="id" type="var">DO</span> <span class="id" type="var">c</span>
<span class="id" type="var">END</span>) <span class="id"
type="keyword">as</span> <span class="id" type="var">wcom</span> <span
class="id" type="var">eqn</span>:<span class="id"
type="var">Heqwcom</span>.\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">He</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">try</span> (<span class="id"
type="tactic">inversion</span> <span class="id"
type="var">Heqwcom</span>); <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">clear</span> <span class="id"
type="var">Heqwcom</span>.\
   <span class="id" type="var">Case</span> "E\_WhileEnd".\
     <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">bexp\_eval\_false</span>. <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "E\_WhileLoop".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHHe2</span>. <span class="id"
type="tactic">reflexivity</span>.\
     <span class="id" type="tactic">apply</span> (<span class="id"
type="var">Hhoare</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span>). <span class="id"
type="tactic">assumption</span>.\
       <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">assumption</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">bexp\_eval\_true</span>. <span class="id"
type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

One subtlety in the terminology is that calling some assertion <span
class="inlinecode"><span class="id" type="var">P</span></span> a "loop
invariant" doesn't just mean that it is preserved by the body of the
loop in question (i.e., <span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>}</span>
<span class="inlinecode"><span class="id" type="var">c</span></span>
<span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>}</span>,
where <span class="inlinecode"><span class="id"
type="var">c</span></span> is the loop body), but rather that <span
class="inlinecode"><span class="id" type="var">P</span></span> *together
with the fact that the loop's guard is true* is a sufficient
precondition for <span class="inlinecode"><span class="id"
type="var">c</span></span> to ensure <span class="inlinecode"><span
class="id" type="var">P</span></span> as a postcondition.
<div class="paragraph">

</div>

This is a slightly (but significantly) weaker requirement. For example,
if <span class="inlinecode"><span class="id" type="var">P</span></span>
is the assertion <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode">=</span> <span
class="inlinecode">0</span>, then <span class="inlinecode"><span
class="id" type="var">P</span></span> *is* an invariant of the loop
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> = 2 <span class="id" type="var">DO</span> <span
class="id" type="var">X</span> := 1 <span class="id"
type="var">END</span>
<div class="paragraph">

</div>

</div>

although it is clearly *not* preserved by the body of the loop.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">while\_example</span> :\
     <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> ≤
3<span style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">WHILE</span> (<span class="id"
type="var">BLe</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
2))\
   <span class="id" type="var">DO</span> <span class="id"
type="var">X</span> ::= <span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 1) <span class="id"
type="var">END</span>\
     <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> =
3<span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol15" class="togglescript"
onclick="toggleDisplay('proof15');toggleDisplay('proofcontrol15')">

<span class="show"></span>

</div>

<div id="proof15" class="proofscript"
onclick="toggleDisplay('proof15');toggleDisplay('proofcontrol15')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_post</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_while</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_asgn</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bassn</span>, <span class="id" type="var">assn\_sub</span>,
<span class="id" type="var">assert\_implies</span>, <span class="id"
type="var">update</span>. <span class="id" type="tactic">simpl</span>.\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> [<span class="id" type="var">H1</span> <span
class="id" type="var">H2</span>]. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">ble\_nat\_true</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H2</span>. <span
class="id" type="tactic">omega</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bassn</span>, <span class="id"
type="var">assert\_implies</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">st</span> [<span
class="id" type="var">Hle</span> <span class="id"
type="var">Hb</span>].\
     <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hb</span>. <span
class="id" type="tactic">destruct</span> (<span class="id"
type="var">ble\_nat</span> (<span class="id" type="var">st</span> <span
class="id" type="var">X</span>) 2) <span class="id"
type="var">eqn</span> : <span class="id" type="var">Heqle</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ex\_falso\_quodlibet</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">Hb</span>; <span
class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ble\_nat\_false</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Heqle</span>. <span
class="id" type="tactic">omega</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

###  {.section}

We can use the while rule to prove the following Hoare triple, which may
seem surprising at first...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">always\_loop\_hoare</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span>,\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">WHILE</span> <span class="id"
type="var">BTrue</span> <span class="id" type="var">DO</span> <span
class="id" type="var">SKIP</span> <span class="id" type="var">END</span>
<span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol16" class="togglescript"
onclick="toggleDisplay('proof16');toggleDisplay('proofcontrol16')">

<span class="show"></span>

</div>

<div id="proof16" class="proofscript"
onclick="toggleDisplay('proof16');toggleDisplay('proofcontrol16')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_consequence\_pre</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">P'</span> :=
<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> : <span class="id" type="var">state</span> ⇒ <span
class="id" type="var">True</span>).\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_post</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_while</span>.\
   <span class="id" type="var">Case</span> "Loop body preserves
invariant".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_post\_true</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">st</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">I</span>.\
   <span class="id" type="var">Case</span> "Loop invariant and negated
guard imply postcondition".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">st</span> [<span
class="id" type="var">Hinv</span> <span class="id"
type="var">Hguard</span>].\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ex\_falso\_quodlibet</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">Hguard</span>.
<span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "Precondition implies
invariant".\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> <span class="id" type="var">H</span>. <span
class="id" type="var">constructor</span>. <span class="id"
type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Of course, this result is not surprising if we remember that the
definition of <span class="inlinecode"><span class="id"
type="var">hoare\_triple</span></span> asserts that the postcondition
must hold *only* when the command terminates. If the command doesn't
terminate, we can prove anything we like about the post-condition.
<div class="paragraph">

</div>

Hoare rules that only talk about terminating commands are often said to
describe a logic of "partial" correctness. It is also possible to give
Hoare rules for "total" correctness, which build in the fact that the
commands terminate. However, in this course we will only talk about
partial correctness.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Exercise: <span class="inlinecode"><span class="id" type="var">REPEAT</span></span> {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">RepeatExercise</span>.\
\

</div>

<div class="doc">

#### Exercise: 4 stars, advanced (hoare\_repeat) {.section}

In this exercise, we'll add a new command to our language of commands:
<span class="inlinecode"><span class="id"
type="var">REPEAT</span></span> c <span class="inlinecode"><span
class="id" type="var">UNTIL</span></span> a <span
class="inlinecode"><span class="id" type="var">END</span></span>. You
will write the evaluation rule for <span class="inlinecode"><span
class="id" type="tactic">repeat</span></span> and add a new Hoare rule
to the language for programs involving it.

</div>

<div class="code code-tight">

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
 <span class="id" type="keyword">Notation</span> "c1 ;; c2" :=\
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

</div>

<div class="doc">

Add new rules for <span class="inlinecode"><span class="id"
type="var">REPEAT</span></span> to <span class="inlinecode"><span
class="id" type="var">ceval</span></span> below. You can use the rules
for <span class="inlinecode"><span class="id"
type="var">WHILE</span></span> as a guide, but remember that the body of
a <span class="inlinecode"><span class="id"
type="var">REPEAT</span></span> should always execute at least once, and
that the loop ends when the guard becomes true. Then update the <span
class="inlinecode"><span class="id"
type="var">ceval\_cases</span></span> tactic to handle these added
cases.

</div>

<div class="code code-tight">

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
type="var">st</span> (<span class="id" type="var">c1</span> ;; <span
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
 <span class="comment">(\* FILL IN HERE \*)</span>\
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
 <span class="comment">(\* FILL IN HERE \*)</span>\
 ].\
\

</div>

<div class="doc">

A couple of definitions from above, copied here so they use the new
<span class="inlinecode"><span class="id"
type="var">ceval</span></span>.

</div>

<div class="code code-tight">

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
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">hoare\_triple</span> (<span class="id"
type="var">P</span>:<span class="id" type="var">Assertion</span>) (<span
class="id" type="var">c</span>:<span class="id" type="var">com</span>)
(<span class="id" type="var">Q</span>:<span class="id"
type="var">Assertion</span>)\
                         : <span class="id" type="keyword">Prop</span>
:=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span>, (<span
class="id" type="var">c</span> / <span class="id" type="var">st</span>
<span style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">Q</span> <span class="id" type="var">st'</span>.\
\
 <span class="id" type="keyword">Notation</span> "<span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{ Q <span
style="letter-spacing:-.4em;">}</span>}" :=\
   (<span class="id" type="var">hoare\_triple</span> <span class="id"
type="var">P</span> <span class="id" type="var">c</span> <span
class="id" type="var">Q</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 90,
<span class="id" type="var">c</span> <span class="id"
type="tactic">at</span> <span class="id" type="var">next</span> <span
class="id" type="var">level</span>).\
\

</div>

<div class="doc">

To make sure you've got the evaluation rules for <span
class="inlinecode"><span class="id" type="var">REPEAT</span></span>
right, prove that <span class="inlinecode"><span class="id"
type="var">ex1\_repeat</span></span> <span class="inlinecode"><span
class="id" type="var">evaluates</span></span> <span
class="inlinecode"><span class="id" type="var">correctly</span>.</span>
<span class="inlinecode"></span>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">ex1\_repeat</span> :=\
   <span class="id" type="var">REPEAT</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">ANum</span> 1;;\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">Y</span>) (<span class="id" type="var">ANum</span>
1)\
   <span class="id" type="var">UNTIL</span> (<span class="id"
type="var">BEq</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1)) <span class="id" type="var">END</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ex1\_repeat\_works</span> :\
   <span class="id" type="var">ex1\_repeat</span> / <span class="id"
type="var">empty\_state</span> <span
style="font-family: arial;">⇓</span>\
                <span class="id" type="var">update</span> (<span
class="id" type="var">update</span> <span class="id"
type="var">empty\_state</span> <span class="id" type="var">X</span> 1)
<span class="id" type="var">Y</span> 1.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Now state and prove a theorem, <span class="inlinecode"><span class="id"
type="var">hoare\_repeat</span></span>, that expresses an appropriate
proof rule for <span class="inlinecode"><span class="id"
type="tactic">repeat</span></span> commands. Use <span
class="inlinecode"><span class="id"
type="var">hoare\_while</span></span> as a model, and try to make your
rule as precise as possible.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\

</div>

<div class="doc">

For full credit, make sure (informally) that your rule can be used to
prove the following valid Hoare triple:
<div class="paragraph">

</div>

<div class="code code-tight">

  <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> \> 0 <span style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">REPEAT</span>\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">X</span>;;\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 1\
   <span class="id" type="var">UNTIL</span> <span class="id"
type="var">X</span> = 0 <span class="id" type="var">END</span>\
   <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = 0 <span style="font-family: arial;">∧</span> <span
class="id" type="var">Y</span> \> 0 <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">RepeatExercise</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Exercise: <span class="inlinecode"><span class="id" type="var">HAVOC</span></span> {.section}
----------------------------------------------------------------------------------

<div class="paragraph">

</div>

#### Exercise: 3 stars (himp\_hoare) {.section}

<div class="paragraph">

</div>

In this exercise, we will derive proof rules for the <span
class="inlinecode"><span class="id" type="var">HAVOC</span></span>
command which we studied in the last chapter. First, we enclose this
work in a separate module, and recall the syntax and big-step semantics
of Himp commands.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Himp</span>.\
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
   | <span class="id" type="var">CHavoc</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">com</span>.\
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
type="var">Case\_aux</span> <span class="id" type="var">c</span> "HAVOC"
].\
\
 <span class="id" type="keyword">Notation</span> "'SKIP'" :=\
   <span class="id" type="var">CSkip</span>.\
 <span class="id" type="keyword">Notation</span> "X '::=' a" :=\
   (<span class="id" type="var">CAsgn</span> <span class="id"
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
 <span class="id" type="keyword">Notation</span> "'HAVOC' X" := (<span
class="id" type="var">CHavoc</span> <span class="id"
type="var">X</span>) (<span class="id" type="tactic">at</span> <span
class="id" type="var">level</span> 60).\
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
   | <span class="id" type="var">E\_Havoc</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">st</span> : <span class="id" type="var">state</span>) (<span
class="id" type="var">X</span> : <span class="id" type="var">id</span>)
(<span class="id" type="var">n</span> : <span class="id"
type="var">nat</span>),\
               (<span class="id" type="var">HAVOC</span> <span
class="id" type="var">X</span>) / <span class="id" type="var">st</span>
<span style="font-family: arial;">⇓</span> <span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">X</span> <span class="id" type="var">n</span>\
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
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "E\_Havoc" ].\
\

</div>

<div class="doc">

The definition of Hoare triples is exactly as before. Unlike our notion
of program equivalence, which had subtle consequences with occassionally
nonterminating commands (exercise <span class="inlinecode"><span
class="id" type="var">havoc\_diverge</span></span>), this definition is
still fully satisfactory. Convince yourself of this before proceeding.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">hoare\_triple</span> (<span class="id"
type="var">P</span>:<span class="id" type="var">Assertion</span>) (<span
class="id" type="var">c</span>:<span class="id" type="var">com</span>)
(<span class="id" type="var">Q</span>:<span class="id"
type="var">Assertion</span>) : <span class="id"
type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">st'</span>, <span
class="id" type="var">c</span> / <span class="id" type="var">st</span>
<span style="font-family: arial;">⇓</span> <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">Q</span> <span class="id" type="var">st'</span>.\
\
 <span class="id" type="keyword">Notation</span> "<span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{ Q <span
style="letter-spacing:-.4em;">}</span>}" := (<span class="id"
type="var">hoare\_triple</span> <span class="id" type="var">P</span>
<span class="id" type="var">c</span> <span class="id"
type="var">Q</span>)\
                                   (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 90,
<span class="id" type="var">c</span> <span class="id"
type="tactic">at</span> <span class="id" type="var">next</span> <span
class="id" type="var">level</span>)\
                                   : <span class="id"
type="var">hoare\_spec\_scope</span>.\
\

</div>

<div class="doc">

Complete the Hoare rule for <span class="inlinecode"><span class="id"
type="var">HAVOC</span></span> commands below by defining <span
class="inlinecode"><span class="id" type="var">havoc\_pre</span></span>
and prove that the resulting rule is correct.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">havoc\_pre</span> (<span class="id" type="var">X</span> :
<span class="id" type="var">id</span>) (<span class="id"
type="var">Q</span> : <span class="id" type="var">Assertion</span>) :
<span class="id" type="var">Assertion</span> :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_havoc</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">Q</span> : <span class="id" type="var">Assertion</span>)
(<span class="id" type="var">X</span> : <span class="id"
type="var">id</span>),\
   <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">havoc\_pre</span> <span class="id" type="var">X</span> <span
class="id" type="var">Q</span> <span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">HAVOC</span> <span class="id" type="var">X</span> <span
style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Q</span> <span style="letter-spacing:-.4em;">}</span>}.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Himp</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Complete List of Hoare Logic Rules {.section}
----------------------------------

<div class="paragraph">

</div>

Above, we've introduced Hoare Logic as a tool to reasoning about Imp
programs. In the reminder of this chapter we will explore a systematic
way to use Hoare Logic to prove properties about programs. The rules of
Hoare Logic are the following:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

  
(hoare\_asgn)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{Q [X <span
style="font-family: arial;">↦</span> a]<span
style="letter-spacing:-.4em;">}</span>} X::=a <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
  
(hoare\_skip)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} SKIP <span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} c1 <span
style="letter-spacing:-.4em;">{</span>{ Q <span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{ Q <span
style="letter-spacing:-.4em;">}</span>} c2 <span
style="letter-spacing:-.4em;">{</span>{ R <span
style="letter-spacing:-.4em;">}</span>}
(hoare\_seq)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} c1;;c2 <span
style="letter-spacing:-.4em;">{</span>{ R <span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{P <span
style="font-family: arial;">∧</span>  b<span
style="letter-spacing:-.4em;">}</span>} c1 <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{P <span
style="font-family: arial;">∧</span> \~b<span
style="letter-spacing:-.4em;">}</span>} c2 <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
(hoare\_if)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} IFB b THEN c1 ELSE c2 FI <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{P <span
style="font-family: arial;">∧</span> b<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>}
(hoare\_while)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} WHILE b DO c END <span
style="letter-spacing:-.4em;">{</span>{P <span
style="font-family: arial;">∧</span> \~b<span
style="letter-spacing:-.4em;">}</span>}
<span style="letter-spacing:-.4em;">{</span>{P'<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{Q'<span
style="letter-spacing:-.4em;">}</span>}
P <span style="font-family: arial;">⇾</span> P'
Q' <span style="font-family: arial;">⇾</span> Q
(hoare\_consequence)  

------------------------------------------------------------------------

<span style="letter-spacing:-.4em;">{</span>{P<span
style="letter-spacing:-.4em;">}</span>} c <span
style="letter-spacing:-.4em;">{</span>{Q<span
style="letter-spacing:-.4em;">}</span>}
In the next chapter, we'll see how these rules are used to prove that
programs satisfy specifications of their behavior.
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
