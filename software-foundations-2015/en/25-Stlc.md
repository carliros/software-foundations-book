<div id="page">

<div id="header">

</div>

<div id="main">

Stlc<span class="subtitle">The Simply Typed Lambda-Calculus</span> {.libtitle}
==================================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id"
type="keyword">Types</span>.\
\

</div>

<div class="doc">

The Simply Typed Lambda-Calculus {.section}
================================

<div class="paragraph">

</div>

The simply typed lambda-calculus (STLC) is a tiny core calculus
embodying the key concept of *functional abstraction*, which shows up in
pretty much every real-world programming language in some form
(functions, procedures, methods, etc.).
<div class="paragraph">

</div>

We will follow exactly the same pattern as in the previous chapter when
formalizing this calculus (syntax, small-step semantics, typing rules)
and its main properties (progress and preservation). The new technical
challenges (which will take some work to deal with) all arise from the
mechanisms of *variable binding* and *substitution*.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Overview {.section}
--------

<div class="paragraph">

</div>

The STLC is built on some collection of *base types* — booleans,
numbers, strings, etc. The exact choice of base types doesn't matter —
the construction of the language and its theoretical properties work out
pretty much the same — so for the sake of brevity let's take just <span
class="inlinecode"><span class="id" type="var">Bool</span></span> for
the moment. At the end of the chapter we'll see how to add more base
types, and in later chapters we'll enrich the pure STLC with other
useful constructs like pairs, records, subtyping, and mutable state.
<div class="paragraph">

</div>

Starting from the booleans, we add three things:
<div class="paragraph">

</div>

-   variables
-   function abstractions
-   application

<div class="paragraph">

</div>

This gives us the following collection of abstract syntax constructors
(written out here in informal BNF notation — we'll formalize it below).
<div class="paragraph">

</div>

<div class="paragraph">

</div>

Informal concrete syntax:
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="var">t</span> ::= <span class="id"
type="var">x</span>                       <span class="id"
type="var">variable</span>\
            | \\<span class="id" type="var">x</span>:<span class="id"
type="var">T~1~.t~2~</span>                <span class="id"
type="var">abstraction</span>\
            | <span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>                   <span class="id"
type="var">application</span>\
            | <span class="id"
type="var">true</span>                    <span class="id"
type="var">constant</span> <span class="id" type="var">true</span>\
            | <span class="id"
type="var">false</span>                   <span class="id"
type="var">constant</span> <span class="id" type="var">false</span>\
            | <span class="id" type="keyword">if</span> <span class="id"
type="var">t~1~</span> <span class="id" type="keyword">then</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="keyword">else</span> <span class="id"
type="var">t~3~</span>   <span class="id" type="var">conditional</span>
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

The <span class="inlinecode">\\</span> symbol (backslash, in ascii) in a
function abstraction <span class="inlinecode">\\<span class="id"
type="var">x</span>:<span class="id" type="var">T~1~.t~2~</span></span>
is generally written as a greek letter "lambda" (hence the name of the
calculus). The variable <span class="inlinecode"><span class="id"
type="var">x</span></span> is called the *parameter* to the function;
the term <span class="inlinecode"><span class="id"
type="var">t~2~</span></span> is its *body*. The annotation <span
class="inlinecode">:<span class="id" type="var">T</span></span>
specifies the type of arguments that the function can be applied to.
<div class="paragraph">

</div>

Some examples:
<div class="paragraph">

</div>

-   <span class="inlinecode">\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id" type="var">x</span></span>
    <div class="paragraph">

    </div>

    The identity function for booleans.
    <div class="paragraph">

    </div>

-   <span class="inlinecode">(\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id"
    type="var">x</span>)</span> <span class="inlinecode"><span
    class="id" type="var">true</span></span>
    <div class="paragraph">

    </div>

    The identity function for booleans, applied to the boolean <span
    class="inlinecode"><span class="id" type="var">true</span></span>.
    <div class="paragraph">

    </div>

-   <span class="inlinecode">\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id"
    type="keyword">if</span></span> <span class="inlinecode"><span
    class="id" type="var">x</span></span> <span class="inlinecode"><span
    class="id" type="keyword">then</span></span> <span
    class="inlinecode"><span class="id" type="var">false</span></span>
    <span class="inlinecode"><span class="id"
    type="keyword">else</span></span> <span class="inlinecode"><span
    class="id" type="var">true</span></span>
    <div class="paragraph">

    </div>

    The boolean "not" function.
    <div class="paragraph">

    </div>

-   <span class="inlinecode">\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id"
    type="var">true</span></span>
    <div class="paragraph">

    </div>

    The constant function that takes every (boolean) argument to <span
    class="inlinecode"><span class="id" type="var">true</span></span>.

<div class="paragraph">

</div>

-   <span class="inlinecode">\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode">\\<span class="id"
    type="var">y</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id" type="var">x</span></span>
    <div class="paragraph">

    </div>

    A two-argument function that takes two booleans and returns the
    first one. (Note that, as in Coq, a two-argument function is really
    a one-argument function whose body is also a one-argument function.)
    <div class="paragraph">

    </div>

-   <span class="inlinecode">(\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode">\\<span class="id"
    type="var">y</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id"
    type="var">x</span>)</span> <span class="inlinecode"><span
    class="id" type="var">false</span></span> <span
    class="inlinecode"><span class="id" type="var">true</span></span>
    <div class="paragraph">

    </div>

    A two-argument function that takes two booleans and returns the
    first one, applied to the booleans <span class="inlinecode"><span
    class="id" type="var">false</span></span> and <span
    class="inlinecode"><span class="id" type="var">true</span></span>.
    <div class="paragraph">

    </div>

    Note that, as in Coq, application associates to the left — i.e.,
    this expression is parsed as <span class="inlinecode">((\\<span
    class="id" type="var">x</span>:<span class="id"
    type="var">Bool</span>.</span> <span class="inlinecode">\\<span
    class="id" type="var">y</span>:<span class="id"
    type="var">Bool</span>.</span> <span class="inlinecode"><span
    class="id" type="var">x</span>)</span> <span
    class="inlinecode"><span class="id" type="var">false</span>)</span>
    <span class="inlinecode"><span class="id"
    type="var">true</span></span>.
    <div class="paragraph">

    </div>

-   <span class="inlinecode">\\<span class="id"
    type="var">f</span>:<span class="id" type="var">Bool</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">Bool</span>.</span> <span class="inlinecode"><span
    class="id" type="var">f</span></span> <span
    class="inlinecode">(<span class="id" type="var">f</span></span>
    <span class="inlinecode"><span class="id"
    type="var">true</span>)</span>
    <div class="paragraph">

    </div>

    A higher-order function that takes a *function* <span
    class="inlinecode"><span class="id" type="var">f</span></span> (from
    booleans to booleans) as an argument, applies <span
    class="inlinecode"><span class="id" type="var">f</span></span> to
    <span class="inlinecode"><span class="id"
    type="var">true</span></span>, and applies <span
    class="inlinecode"><span class="id" type="var">f</span></span> again
    to the result.
    <div class="paragraph">

    </div>

-   <span class="inlinecode">(\\<span class="id"
    type="var">f</span>:<span class="id" type="var">Bool</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">Bool</span>.</span> <span class="inlinecode"><span
    class="id" type="var">f</span></span> <span
    class="inlinecode">(<span class="id" type="var">f</span></span>
    <span class="inlinecode"><span class="id"
    type="var">true</span>))</span> <span class="inlinecode">(\\<span
    class="id" type="var">x</span>:<span class="id"
    type="var">Bool</span>.</span> <span class="inlinecode"><span
    class="id" type="var">false</span>)</span>
    <div class="paragraph">

    </div>

    The same higher-order function, applied to the constantly <span
    class="inlinecode"><span class="id" type="var">false</span></span>
    function.

<div class="paragraph">

</div>

As the last several examples show, the STLC is a language of
*higher-order* functions: we can write down functions that take other
functions as arguments and/or return other functions as results.
<div class="paragraph">

</div>

Another point to note is that the STLC doesn't provide any primitive
syntax for defining *named* functions — all functions are "anonymous."
We'll see in chapter <span class="inlinecode"><span class="id"
type="var">MoreStlc</span></span> that it is easy to add named functions
to what we've got — indeed, the fundamental naming and binding
mechanisms are exactly the same.
<div class="paragraph">

</div>

The *types* of the STLC include <span class="inlinecode"><span
class="id" type="var">Bool</span></span>, which classifies the boolean
constants <span class="inlinecode"><span class="id"
type="var">true</span></span> and <span class="inlinecode"><span
class="id" type="var">false</span></span> as well as more complex
computations that yield booleans, plus *arrow types* that classify
functions.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">T</span> ::= <span class="id"
type="var">Bool</span>\
           | <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">T~2~</span>
<div class="paragraph">

</div>

</div>

For example:
<div class="paragraph">

</div>

-   <span class="inlinecode">\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id"
    type="var">false</span></span> has type <span
    class="inlinecode"><span class="id" type="var">Bool</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">Bool</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id" type="var">x</span></span>
    has type <span class="inlinecode"><span class="id"
    type="var">Bool</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">Bool</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">(\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id"
    type="var">x</span>)</span> <span class="inlinecode"><span
    class="id" type="var">true</span></span> has type <span
    class="inlinecode"><span class="id" type="var">Bool</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode">\\<span class="id"
    type="var">y</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id" type="var">x</span></span>
    has type <span class="inlinecode"><span class="id"
    type="var">Bool</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">Bool</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">Bool</span></span> (i.e. <span class="inlinecode"><span
    class="id" type="var">Bool</span></span> <span
    class="inlinecode"><span style="font-family: arial;">→</span></span>
    <span class="inlinecode">(<span class="id"
    type="var">Bool</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">Bool</span>)</span>)
    <div class="paragraph">

    </div>

-   <span class="inlinecode">(\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode">\\<span class="id"
    type="var">y</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id"
    type="var">x</span>)</span> <span class="inlinecode"><span
    class="id" type="var">false</span></span> has type <span
    class="inlinecode"><span class="id" type="var">Bool</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">Bool</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">(\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode">\\<span class="id"
    type="var">y</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id"
    type="var">x</span>)</span> <span class="inlinecode"><span
    class="id" type="var">false</span></span> <span
    class="inlinecode"><span class="id" type="var">true</span></span>
    has type <span class="inlinecode"><span class="id"
    type="var">Bool</span></span>

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
type="var">STLC</span>.\
\

</div>

<div class="doc">

### Types {.section}

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
type="var">ty</span>.\
\

</div>

<div class="doc">

### Terms {.section}

</div>

<div class="code code-space">

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
<div id="proofcontrol1" class="togglescript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')">

<span class="show"></span>

</div>

<div id="proof1" class="proofscript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')"
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
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ttrue"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tfalse" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tif"
].\

</div>

\

</div>

<div class="doc">

Note that an abstraction <span class="inlinecode">\\<span class="id"
type="var">x</span>:<span class="id" type="var">T.t</span></span>
(formally, <span class="inlinecode"><span class="id"
type="var">tabs</span></span> <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode"><span class="id"
type="var">T</span></span> <span class="inlinecode"><span class="id"
type="var">t</span></span>) is always annotated with the type <span
class="inlinecode"><span class="id" type="var">T</span></span> of its
parameter, in contrast to Coq (and other functional languages like ML,
Haskell, etc.), which use *type inference* to fill in missing
annotations. We're not considering type inference here, to keep things
simple.
<div class="paragraph">

</div>

Some examples...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">x</span> := (<span class="id" type="var">Id</span> 0).\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">y</span> := (<span class="id" type="var">Id</span> 1).\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">z</span> := (<span class="id" type="var">Id</span> 2).\
<div id="proofcontrol2" class="togglescript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')">

<span class="show"></span>

</div>

<div id="proof2" class="proofscript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')"
style="display: none;">

<span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Unfold</span> <span class="id" type="var">x</span>.\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Unfold</span> <span class="id" type="var">y</span>.\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Unfold</span> <span class="id" type="var">z</span>.\

</div>

\

</div>

<div class="doc">

<span class="inlinecode"><span class="id" type="var">idB</span></span>
<span class="inlinecode">=</span> <span class="inlinecode">\\<span
class="id" type="var">x</span>:<span class="id"
type="var">Bool</span>.</span> <span class="inlinecode"><span class="id"
type="var">x</span></span>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">idB</span> :=\
   (<span class="id" type="var">tabs</span> <span class="id"
type="var">x</span> <span class="id" type="var">TBool</span> (<span
class="id" type="var">tvar</span> <span class="id"
type="var">x</span>)).\
\

</div>

<div class="doc">

<span class="inlinecode"><span class="id" type="var">idBB</span></span>
<span class="inlinecode">=</span> <span class="inlinecode">\\<span
class="id" type="var">x</span>:<span class="id"
type="var">Bool</span><span style="font-family: arial;">→</span><span
class="id" type="var">Bool</span>.</span> <span class="inlinecode"><span
class="id" type="var">x</span></span>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">idBB</span> :=\
   (<span class="id" type="var">tabs</span> <span class="id"
type="var">x</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">TBool</span> <span class="id"
type="var">TBool</span>) (<span class="id" type="var">tvar</span> <span
class="id" type="var">x</span>)).\
\

</div>

<div class="doc">

<span class="inlinecode"><span class="id"
type="var">idBBBB</span></span> <span class="inlinecode">=</span> <span
class="inlinecode">\\<span class="id" type="var">x</span>:(<span
class="id" type="var">Bool</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Bool</span>)</span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode">(<span class="id" type="var">Bool</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Bool</span>).</span> <span class="inlinecode"><span
class="id" type="var">x</span></span>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">idBBBB</span> :=\
   (<span class="id" type="var">tabs</span> <span class="id"
type="var">x</span> (<span class="id" type="var">TArrow</span> (<span
class="id" type="var">TArrow</span> <span class="id"
type="var">TBool</span> <span class="id" type="var">TBool</span>)\
                       (<span class="id" type="var">TArrow</span> <span
class="id" type="var">TBool</span> <span class="id"
type="var">TBool</span>))\
     (<span class="id" type="var">tvar</span> <span class="id"
type="var">x</span>)).\
\

</div>

<div class="doc">

<span class="inlinecode"><span class="id" type="var">k</span></span>
<span class="inlinecode">=</span> <span class="inlinecode">\\<span
class="id" type="var">x</span>:<span class="id"
type="var">Bool</span>.</span> <span class="inlinecode">\\<span
class="id" type="var">y</span>:<span class="id"
type="var">Bool</span>.</span> <span class="inlinecode"><span class="id"
type="var">x</span></span>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">k</span> := (<span class="id" type="var">tabs</span> <span
class="id" type="var">x</span> <span class="id" type="var">TBool</span>
(<span class="id" type="var">tabs</span> <span class="id"
type="var">y</span> <span class="id" type="var">TBool</span> (<span
class="id" type="var">tvar</span> <span class="id"
type="var">x</span>))).\
\

</div>

<div class="doc">

<span class="inlinecode"><span class="id" type="var">notB</span></span>
<span class="inlinecode">=</span> <span class="inlinecode">\\<span
class="id" type="var">x</span>:<span class="id"
type="var">Bool</span>.</span> <span class="inlinecode"><span class="id"
type="keyword">if</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="keyword">then</span></span> <span
class="inlinecode"><span class="id" type="var">false</span></span> <span
class="inlinecode"><span class="id" type="keyword">else</span></span>
<span class="inlinecode"><span class="id" type="var">true</span></span>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">notB</span> := (<span class="id" type="var">tabs</span> <span
class="id" type="var">x</span> <span class="id" type="var">TBool</span>
(<span class="id" type="var">tif</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) <span
class="id" type="var">tfalse</span> <span class="id"
type="var">ttrue</span>)).\
\

</div>

<div class="doc">

(We write these as <span class="inlinecode"><span class="id"
type="keyword">Notation</span></span>s rather than <span
class="inlinecode"><span class="id"
type="keyword">Definition</span></span>s to make things easier for <span
class="inlinecode"><span class="id" type="tactic">auto</span></span>.)

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Operational Semantics {.section}
---------------------

<div class="paragraph">

</div>

To define the small-step semantics of STLC terms, we begin — as always —
by defining the set of values. Next, we define the critical notions of
*free variables* and *substitution*, which are used in the reduction
rule for application expressions. And finally we give the small-step
relation itself.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Values {.section}

<div class="paragraph">

</div>

To define the values of the STLC, we have a few cases to consider.
<div class="paragraph">

</div>

First, for the boolean part of the language, the situation is clear:
<span class="inlinecode"><span class="id" type="var">true</span></span>
and <span class="inlinecode"><span class="id"
type="var">false</span></span> are the only values. An <span
class="inlinecode"><span class="id" type="keyword">if</span></span>
expression is never a value.
<div class="paragraph">

</div>

Second, an application is clearly not a value: It represents a function
being invoked on some argument, which clearly still has work left to do.
<div class="paragraph">

</div>

Third, for abstractions, we have a choice:
<div class="paragraph">

</div>

-   We can say that <span class="inlinecode">\\<span class="id"
    type="var">x</span>:<span class="id" type="var">T.t~1~</span></span>
    is a value only when <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> is a value — i.e., only if the
    function's body has been reduced (as much as it can be without
    knowing what argument it is going to be applied to).
    <div class="paragraph">

    </div>

-   Or we can say that <span class="inlinecode">\\<span class="id"
    type="var">x</span>:<span class="id" type="var">T.t~1~</span></span>
    is always a value, no matter whether <span class="inlinecode"><span
    class="id" type="var">t~1~</span></span> is one or not — in other
    words, we can say that reduction stops at abstractions.

<div class="paragraph">

</div>

Coq, in its built-in functional programming langauge, makes the first
choice — for example,
<div class="paragraph">

</div>

<div class="code code-tight">

         <span class="id" type="keyword">Eval</span> <span class="id"
type="tactic">simpl</span> <span class="id"
type="keyword">in</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">x</span>:<span
class="id" type="var">bool</span> ⇒ 3 + 4)
<div class="paragraph">

</div>

</div>

yields <span class="inlinecode"><span class="id"
type="keyword">fun</span></span> <span class="inlinecode"><span
class="id" type="var">x</span>:<span class="id"
type="var">bool</span></span> <span class="inlinecode">⇒</span> <span
class="inlinecode">7</span>.
<div class="paragraph">

</div>

Most real-world functional programming languages make the second choice
— reduction of a function's body only begins when the function is
actually applied to an argument. We also make the second choice here.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">value</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">v\_abs</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">T</span> <span class="id"
type="var">t</span>,\
       <span class="id" type="var">value</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T</span> <span class="id" type="var">t</span>)\
   | <span class="id" type="var">v\_true</span> :\
       <span class="id" type="var">value</span> <span class="id"
type="var">ttrue</span>\
   | <span class="id" type="var">v\_false</span> :\
       <span class="id" type="var">value</span> <span class="id"
type="var">tfalse</span>.\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">value</span>.\
\

</div>

<div class="doc">

Finally, we must consider what constitutes a *complete* program.
<div class="paragraph">

</div>

Intuitively, a "complete" program must not refer to any undefined
variables. We'll see shortly how to define the "free" variables in a
STLC term. A program is "closed", that is, it contains no free
variables.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

Having made the choice not to reduce under abstractions, we don't need
to worry about whether variables are values, since we'll always be
reducing programs "from the outside in," and that means the <span
class="inlinecode"><span class="id" type="var">step</span></span>
relation will always be working with closed terms (ones with no free
variables).

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Substitution {.section}

<div class="paragraph">

</div>

Now we come to the heart of the STLC: the operation of substituting one
term for a variable in another term.
<div class="paragraph">

</div>

This operation will be used below to define the operational semantics of
function application, where we will need to substitute the argument term
for the function parameter in the function's body. For example, we
reduce
<div class="paragraph">

</div>

<div class="code code-tight">

       (\\<span class="id" type="var">x</span>:<span class="id"
type="var">Bool</span>. <span class="id" type="keyword">if</span> <span
class="id" type="var">x</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">true</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">x</span>) <span class="id" type="var">false</span>
<div class="paragraph">

</div>

</div>

to
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="keyword">if</span> <span class="id"
type="var">false</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">true</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">false</span>
<div class="paragraph">

</div>

</div>

by substituting <span class="inlinecode"><span class="id"
type="var">false</span></span> for the parameter <span
class="inlinecode"><span class="id" type="var">x</span></span> in the
body of the function.
<div class="paragraph">

</div>

In general, we need to be able to substitute some given term <span
class="inlinecode"><span class="id" type="var">s</span></span> for
occurrences of some variable <span class="inlinecode"><span class="id"
type="var">x</span></span> in another term <span
class="inlinecode"><span class="id" type="var">t</span></span>. In
informal discussions, this is usually written <span
class="inlinecode"></span> <span class="inlinecode">[<span class="id"
type="var">x</span>:=<span class="id" type="var">s</span>]<span
class="id" type="var">t</span></span> <span class="inlinecode"></span>
and pronounced "substitute <span class="inlinecode"><span class="id"
type="var">x</span></span> with <span class="inlinecode"><span
class="id" type="var">s</span></span> in <span class="inlinecode"><span
class="id" type="var">t</span></span>."
<div class="paragraph">

</div>

Here are some examples:
<div class="paragraph">

</div>

-   <span class="inlinecode">[<span class="id"
    type="var">x</span>:=<span class="id" type="var">true</span>]</span>
    <span class="inlinecode">(<span class="id"
    type="keyword">if</span></span> <span class="inlinecode"><span
    class="id" type="var">x</span></span> <span class="inlinecode"><span
    class="id" type="keyword">then</span></span> <span
    class="inlinecode"><span class="id" type="var">x</span></span> <span
    class="inlinecode"><span class="id"
    type="keyword">else</span></span> <span class="inlinecode"><span
    class="id" type="var">false</span>)</span> yields <span
    class="inlinecode"><span class="id" type="keyword">if</span></span>
    <span class="inlinecode"><span class="id"
    type="var">true</span></span> <span class="inlinecode"><span
    class="id" type="keyword">then</span></span> <span
    class="inlinecode"><span class="id" type="var">true</span></span>
    <span class="inlinecode"><span class="id"
    type="keyword">else</span></span> <span class="inlinecode"><span
    class="id" type="var">false</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">[<span class="id"
    type="var">x</span>:=<span class="id" type="var">true</span>]</span>
    <span class="inlinecode"><span class="id" type="var">x</span></span>
    yields <span class="inlinecode"><span class="id"
    type="var">true</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">[<span class="id"
    type="var">x</span>:=<span class="id" type="var">true</span>]</span>
    <span class="inlinecode">(<span class="id"
    type="keyword">if</span></span> <span class="inlinecode"><span
    class="id" type="var">x</span></span> <span class="inlinecode"><span
    class="id" type="keyword">then</span></span> <span
    class="inlinecode"><span class="id" type="var">x</span></span> <span
    class="inlinecode"><span class="id"
    type="keyword">else</span></span> <span class="inlinecode"><span
    class="id" type="var">y</span>)</span> yields <span
    class="inlinecode"><span class="id" type="keyword">if</span></span>
    <span class="inlinecode"><span class="id"
    type="var">true</span></span> <span class="inlinecode"><span
    class="id" type="keyword">then</span></span> <span
    class="inlinecode"><span class="id" type="var">true</span></span>
    <span class="inlinecode"><span class="id"
    type="keyword">else</span></span> <span class="inlinecode"><span
    class="id" type="var">y</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">[<span class="id"
    type="var">x</span>:=<span class="id" type="var">true</span>]</span>
    <span class="inlinecode"><span class="id" type="var">y</span></span>
    yields <span class="inlinecode"><span class="id"
    type="var">y</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">[<span class="id"
    type="var">x</span>:=<span class="id" type="var">true</span>]</span>
    <span class="inlinecode"><span class="id"
    type="var">false</span></span> yields <span class="inlinecode"><span
    class="id" type="var">false</span></span> (vacuous substitution)
    <div class="paragraph">

    </div>

-   <span class="inlinecode">[<span class="id"
    type="var">x</span>:=<span class="id" type="var">true</span>]</span>
    <span class="inlinecode">(\\<span class="id"
    type="var">y</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id"
    type="keyword">if</span></span> <span class="inlinecode"><span
    class="id" type="var">y</span></span> <span class="inlinecode"><span
    class="id" type="keyword">then</span></span> <span
    class="inlinecode"><span class="id" type="var">x</span></span> <span
    class="inlinecode"><span class="id"
    type="keyword">else</span></span> <span class="inlinecode"><span
    class="id" type="var">false</span>)</span> yields <span
    class="inlinecode">\\<span class="id" type="var">y</span>:<span
    class="id" type="var">Bool</span>.</span> <span
    class="inlinecode"><span class="id" type="keyword">if</span></span>
    <span class="inlinecode"><span class="id" type="var">y</span></span>
    <span class="inlinecode"><span class="id"
    type="keyword">then</span></span> <span class="inlinecode"><span
    class="id" type="var">true</span></span> <span
    class="inlinecode"><span class="id"
    type="keyword">else</span></span> <span class="inlinecode"><span
    class="id" type="var">false</span></span>
-   <span class="inlinecode">[<span class="id"
    type="var">x</span>:=<span class="id" type="var">true</span>]</span>
    <span class="inlinecode">(\\<span class="id"
    type="var">y</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id"
    type="var">x</span>)</span> yields <span class="inlinecode">\\<span
    class="id" type="var">y</span>:<span class="id"
    type="var">Bool</span>.</span> <span class="inlinecode"><span
    class="id" type="var">true</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">[<span class="id"
    type="var">x</span>:=<span class="id" type="var">true</span>]</span>
    <span class="inlinecode">(\\<span class="id"
    type="var">y</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id"
    type="var">y</span>)</span> yields <span class="inlinecode">\\<span
    class="id" type="var">y</span>:<span class="id"
    type="var">Bool</span>.</span> <span class="inlinecode"><span
    class="id" type="var">y</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">[<span class="id"
    type="var">x</span>:=<span class="id" type="var">true</span>]</span>
    <span class="inlinecode">(\\<span class="id"
    type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
    <span class="inlinecode"><span class="id"
    type="var">x</span>)</span> yields <span class="inlinecode">\\<span
    class="id" type="var">x</span>:<span class="id"
    type="var">Bool</span>.</span> <span class="inlinecode"><span
    class="id" type="var">x</span></span>

<div class="paragraph">

</div>

The last example is very important: substituting <span
class="inlinecode"><span class="id" type="var">x</span></span> with
<span class="inlinecode"><span class="id" type="var">true</span></span>
in <span class="inlinecode">\\<span class="id" type="var">x</span>:<span
class="id" type="var">Bool</span>.</span> <span class="inlinecode"><span
class="id" type="var">x</span></span> does *not* yield <span
class="inlinecode">\\<span class="id" type="var">x</span>:<span
class="id" type="var">Bool</span>.</span> <span class="inlinecode"><span
class="id" type="var">true</span></span>! The reason for this is that
the <span class="inlinecode"><span class="id" type="var">x</span></span>
in the body of <span class="inlinecode">\\<span class="id"
type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
<span class="inlinecode"><span class="id" type="var">x</span></span> is
*bound* by the abstraction: it is a new, local name that just happens to
be spelled the same as some global name <span class="inlinecode"><span
class="id" type="var">x</span></span>.
<div class="paragraph">

</div>

Here is the definition, informally...
<div class="paragraph">

</div>

<div class="code code-tight">

   [<span class="id" type="var">x</span>:=<span class="id"
type="var">s</span>]<span class="id" type="var">x</span> = <span
class="id" type="var">s</span>\
    [<span class="id" type="var">x</span>:=<span class="id"
type="var">s</span>]<span class="id" type="var">y</span> = <span
class="id" type="var">y</span>                                   <span
class="id" type="keyword">if</span> <span class="id"
type="var">x</span> ≠ <span class="id" type="var">y</span>\
    [<span class="id" type="var">x</span>:=<span class="id"
type="var">s</span>](\\<span class="id" type="var">x</span>:<span
class="id" type="var">T~11~.t~12~</span>)   = \\<span class="id"
type="var">x</span>:<span class="id" type="var">T~11~</span>. <span
class="id" type="var">t~12~</span>      \
    [<span class="id" type="var">x</span>:=<span class="id"
type="var">s</span>](\\<span class="id" type="var">y</span>:<span
class="id" type="var">T~11~.t~12~</span>)   = \\<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span>. [<span
class="id" type="var">x</span>:=<span class="id"
type="var">s</span>]<span class="id" type="var">t~12~</span>      <span
class="id" type="keyword">if</span> <span class="id"
type="var">x</span> ≠ <span class="id" type="var">y</span>\
    [<span class="id" type="var">x</span>:=<span class="id"
type="var">s</span>](<span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>)        = ([<span class="id"
type="var">x</span>:=<span class="id" type="var">s</span>]<span
class="id" type="var">t~1~</span>) ([<span class="id"
type="var">x</span>:=<span class="id" type="var">s</span>]<span
class="id" type="var">t~2~</span>)       \
    [<span class="id" type="var">x</span>:=<span class="id"
type="var">s</span>]<span class="id"
type="var">true</span>           = <span class="id"
type="var">true</span>\
    [<span class="id" type="var">x</span>:=<span class="id"
type="var">s</span>]<span class="id"
type="var">false</span>          = <span class="id"
type="var">false</span>\
    [<span class="id" type="var">x</span>:=<span class="id"
type="var">s</span>](<span class="id" type="keyword">if</span> <span
class="id" type="var">t~1~</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">t~2~</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">t~3~</span>) = \
                    <span class="id" type="keyword">if</span> [<span
class="id" type="var">x</span>:=<span class="id"
type="var">s</span>]<span class="id" type="var">t~1~</span> <span
class="id" type="keyword">then</span> [<span class="id"
type="var">x</span>:=<span class="id" type="var">s</span>]<span
class="id" type="var">t~2~</span> <span class="id"
type="keyword">else</span> [<span class="id" type="var">x</span>:=<span
class="id" type="var">s</span>]<span class="id" type="var">t~3~</span>
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

... and formally:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> "'[' x ':=' s
']' t" (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 20).\
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
type="var">x'</span> ⇒\
       <span class="id" type="keyword">if</span> <span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x'</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">s</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">t</span>\
   | <span class="id" type="var">tabs</span> <span class="id"
type="var">x'</span> <span class="id" type="var">T</span> <span
class="id" type="var">t~1~</span> ⇒\
       <span class="id" type="var">tabs</span> <span class="id"
type="var">x'</span> <span class="id" type="var">T</span> (<span
class="id" type="keyword">if</span> <span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x'</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">t~1~</span> <span
class="id" type="keyword">else</span> ([<span class="id"
type="var">x</span>:=<span class="id" type="var">s</span>] <span
class="id" type="var">t~1~</span>))\
   | <span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒\
       <span class="id" type="var">tapp</span> ([<span class="id"
type="var">x</span>:=<span class="id" type="var">s</span>] <span
class="id" type="var">t~1~</span>) ([<span class="id"
type="var">x</span>:=<span class="id" type="var">s</span>] <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">ttrue</span> ⇒\
       <span class="id" type="var">ttrue</span>\
   | <span class="id" type="var">tfalse</span> ⇒\
       <span class="id" type="var">tfalse</span>\
   | <span class="id" type="var">tif</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> ⇒\
       <span class="id" type="var">tif</span> ([<span class="id"
type="var">x</span>:=<span class="id" type="var">s</span>] <span
class="id" type="var">t~1~</span>) ([<span class="id"
type="var">x</span>:=<span class="id" type="var">s</span>] <span
class="id" type="var">t~2~</span>) ([<span class="id"
type="var">x</span>:=<span class="id" type="var">s</span>] <span
class="id" type="var">t~3~</span>)\
   <span class="id" type="keyword">end</span>\
\
 <span class="id" type="keyword">where</span> "'[' x ':=' s ']' t" :=
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t</span>).\
\

</div>

<div class="doc">

*Technical note*: Substitution becomes trickier to define if we consider
the case where <span class="inlinecode"><span class="id"
type="var">s</span></span>, the term being substituted for a variable in
some other term, may itself contain free variables. Since we are only
interested here in defining the <span class="inlinecode"><span
class="id" type="var">step</span></span> relation on closed terms (i.e.,
terms like <span class="inlinecode">\\<span class="id"
type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
<span class="inlinecode"><span class="id" type="var">x</span></span>,
that do not mention variables are not bound by some enclosing lambda),
we can skip this extra complexity here, but it must be dealt with when
formalizing richer languages.
<div class="paragraph">

</div>

###  {.section}

#### Exercise: 3 stars (substi) {.section}

<div class="paragraph">

</div>

The definition that we gave above uses Coq's <span
class="inlinecode"><span class="id"
type="keyword">Fixpoint</span></span> facility to define substitution as
a *function*. Suppose, instead, we wanted to define substitution as an
inductive *relation* <span class="inlinecode"><span class="id"
type="var">substi</span></span>. We've begun the definition by providing
the <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> header and one of the
constructors; your job is to fill in the rest of the constructors.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">substi</span> (<span class="id" type="var">s</span>:<span
class="id" type="var">tm</span>) (<span class="id"
type="var">x</span>:<span class="id" type="var">id</span>) : <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">s\_var1</span> :\
       <span class="id" type="var">substi</span> <span class="id"
type="var">s</span> <span class="id" type="var">x</span> (<span
class="id" type="var">tvar</span> <span class="id" type="var">x</span>)
<span class="id" type="var">s</span>\
   <span class="comment">(\* FILL IN HERE \*)</span>\
 .\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">substi</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">substi\_correct</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">s</span>
<span class="id" type="var">x</span> <span class="id"
type="var">t</span> <span class="id" type="var">t'</span>,\
   [<span class="id" type="var">x</span>:=<span class="id"
type="var">s</span>]<span class="id" type="var">t</span> = <span
class="id" type="var">t'</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">substi</span> <span class="id" type="var">s</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span class="id" type="var">t'</span>.\
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

### Reduction {.section}

<div class="paragraph">

</div>

The small-step reduction relation for STLC now follows the same pattern
as the ones we have seen before. Intuitively, to reduce a function
application, we first reduce its left-hand side until it becomes a
literal function; then we reduce its right-hand side (the argument)
until it is also a value; and finally we substitute the argument for the
bound variable in the body of the function. This last rule, written
informally as
<div class="paragraph">

</div>

<div class="code code-tight">

      (\\<span class="id" type="var">x</span>:<span class="id"
type="var">T.t~12~</span>) <span class="id" type="var">v~2~</span> <span
style="font-family: arial;">⇒</span> [<span class="id"
type="var">x</span>:=<span class="id" type="var">v~2~</span>]<span
class="id" type="var">t~12~</span>
<div class="paragraph">

</div>

</div>

is traditionally called "beta-reduction".
<div class="paragraph">

</div>

value v~2~
(ST\_AppAbs)  

------------------------------------------------------------------------

(\\x:T.t~12~) v~2~ <span
style="font-family: arial;">⇒</span> [x:=v~2~]t~12~
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_App1)  

------------------------------------------------------------------------

t~1~ t~2~ <span style="font-family: arial;">⇒</span> t~1~' t~2~
value v~1~
t~2~ <span style="font-family: arial;">⇒</span> t~2~'
(ST\_App2)  

------------------------------------------------------------------------

v~1~ t~2~ <span style="font-family: arial;">⇒</span> v~1~ t~2~'
... plus the usual rules for booleans:
  
(ST\_IfTrue)  

------------------------------------------------------------------------

(if true then t~1~ else t~2~) <span
style="font-family: arial;">⇒</span> t~1~
  
(ST\_IfFalse)  

------------------------------------------------------------------------

(if false then t~1~ else t~2~) <span
style="font-family: arial;">⇒</span> t~2~
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_If)  

------------------------------------------------------------------------

(if t~1~ then t~2~ else t~3~) <span
style="font-family: arial;">⇒</span> (if t~1~' then t~2~ else t~3~)

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
   | <span class="id" type="var">ST\_AppAbs</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">T</span> <span class="id"
type="var">t~12~</span> <span class="id" type="var">v~2~</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~2~</span> <span style="font-family: arial;">→</span>\
          (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T</span> <span class="id" type="var">t~12~</span>)
<span class="id" type="var">v~2~</span>) <span
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
          <span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>\
   | <span class="id" type="var">ST\_App2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tapp</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tapp</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>\
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
"ST\_App1"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_App2" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_IfTrue"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_IfFalse" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_If" ].\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id" type="var">step</span>.\
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
\

</div>

<div class="doc">

### Examples {.section}

<div class="paragraph">

</div>

Example:
<div class="paragraph">

</div>

<div class="code code-tight">

    ((\\<span class="id" type="var">x</span>:<span class="id"
type="var">Bool</span><span style="font-family: arial;">→</span><span
class="id" type="var">Bool</span>. <span class="id"
type="var">x</span>) (\\<span class="id" type="var">x</span>:<span
class="id" type="var">Bool</span>. <span class="id"
type="var">x</span>)) <span
style="font-family: arial;">⇒\*</span> (\\<span class="id"
type="var">x</span>:<span class="id" type="var">Bool</span>. <span
class="id" type="var">x</span>)
<div class="paragraph">

</div>

</div>

i.e.
<div class="paragraph">

</div>

<div class="code code-tight">

    (<span class="id" type="var">idBB</span> <span class="id"
type="var">idB</span>) <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">idB</span>
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_example1</span> :\
   (<span class="id" type="var">tapp</span> <span class="id"
type="var">idBB</span> <span class="id" type="var">idB</span>) <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">idB</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_AppAbs</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">v\_abs</span>.\
   <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Example:
<div class="paragraph">

</div>

<div class="code code-tight">

((\\<span class="id" type="var">x</span>:<span class="id"
type="var">Bool</span><span style="font-family: arial;">→</span><span
class="id" type="var">Bool</span>. <span class="id"
type="var">x</span>) ((\\<span class="id" type="var">x</span>:<span
class="id" type="var">Bool</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Bool</span>. <span class="id" type="var">x</span>) (\\<span
class="id" type="var">x</span>:<span class="id" type="var">Bool</span>.
<span class="id" type="var">x</span>))) \
       <span style="font-family: arial;">⇒\*</span> (\\<span class="id"
type="var">x</span>:<span class="id" type="var">Bool</span>. <span
class="id" type="var">x</span>)
<div class="paragraph">

</div>

</div>

i.e.
<div class="paragraph">

</div>

<div class="code code-tight">

  (<span class="id" type="var">idBB</span> (<span class="id"
type="var">idBB</span> <span class="id" type="var">idB</span>)) <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">idB</span>.
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_example2</span> :\
   (<span class="id" type="var">tapp</span> <span class="id"
type="var">idBB</span> (<span class="id" type="var">tapp</span> <span
class="id" type="var">idBB</span> <span class="id"
type="var">idB</span>)) <span style="font-family: arial;">⇒\*</span>
<span class="id" type="var">idB</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_App2</span>. <span class="id" type="tactic">auto</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_AppAbs</span>. <span class="id"
type="tactic">auto</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_AppAbs</span>. <span class="id"
type="tactic">simpl</span>. <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Example:
<div class="paragraph">

</div>

<div class="code code-tight">

((\\<span class="id" type="var">x</span>:<span class="id"
type="var">Bool</span><span style="font-family: arial;">→</span><span
class="id" type="var">Bool</span>. <span class="id"
type="var">x</span>) (\\<span class="id" type="var">x</span>:<span
class="id" type="var">Bool</span>. <span class="id"
type="keyword">if</span> <span class="id" type="var">x</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">false</span>\
                               <span class="id"
type="keyword">else</span> <span class="id"
type="var">true</span>)) <span class="id" type="var">true</span>)\
       <span style="font-family: arial;">⇒\*</span> <span class="id"
type="var">false</span>
<div class="paragraph">

</div>

</div>

i.e.
<div class="paragraph">

</div>

<div class="code code-tight">

  ((<span class="id" type="var">idBB</span> <span class="id"
type="var">notB</span>) <span class="id" type="var">ttrue</span>) <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">tfalse</span>.
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_example3</span> :\
   <span class="id" type="var">tapp</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">idBB</span> <span
class="id" type="var">notB</span>) <span class="id"
type="var">ttrue</span> <span style="font-family: arial;">⇒\*</span>
<span class="id" type="var">tfalse</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_App1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">ST\_AppAbs</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_AppAbs</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_IfTrue</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Example:
<div class="paragraph">

</div>

<div class="code code-tight">

((\\<span class="id" type="var">x</span>:<span class="id"
type="var">Bool</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Bool</span>. <span class="id"
type="var">x</span>) ((\\<span class="id" type="var">x</span>:<span
class="id" type="var">Bool</span>. <span class="id"
type="keyword">if</span> <span class="id" type="var">x</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">false</span>\
                                <span class="id"
type="keyword">else</span> <span class="id"
type="var">true</span>) <span class="id" type="var">true</span>))\
       <span style="font-family: arial;">⇒\*</span> <span class="id"
type="var">false</span>
<div class="paragraph">

</div>

</div>

i.e.
<div class="paragraph">

</div>

<div class="code code-tight">

  (<span class="id" type="var">idBB</span> (<span class="id"
type="var">notB</span> <span class="id" type="var">ttrue</span>)) <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">tfalse</span>.
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_example4</span> :\
   <span class="id" type="var">tapp</span> <span class="id"
type="var">idBB</span> (<span class="id" type="var">tapp</span> <span
class="id" type="var">notB</span> <span class="id"
type="var">ttrue</span>) <span style="font-family: arial;">⇒\*</span>
<span class="id" type="var">tfalse</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_App2</span>. <span class="id" type="tactic">auto</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_AppAbs</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_App2</span>. <span class="id" type="tactic">auto</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_IfTrue</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ST\_AppAbs</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="tactic">simpl</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_refl</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

A more automatic proof

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_example1'</span> :\
   (<span class="id" type="var">tapp</span> <span class="id"
type="var">idBB</span> <span class="id" type="var">idB</span>) <span
style="font-family: arial;">⇒\*</span> <span class="id"
type="var">idB</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="var">normalize</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Again, we can use the <span class="inlinecode"><span class="id"
type="var">normalize</span></span> tactic from above to simplify the
proof.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_example2'</span> :\
   (<span class="id" type="var">tapp</span> <span class="id"
type="var">idBB</span> (<span class="id" type="var">tapp</span> <span
class="id" type="var">idBB</span> <span class="id"
type="var">idB</span>)) <span style="font-family: arial;">⇒\*</span>
<span class="id" type="var">idB</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">normalize</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_example3'</span> :\
   <span class="id" type="var">tapp</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">idBB</span> <span
class="id" type="var">notB</span>) <span class="id"
type="var">ttrue</span> <span style="font-family: arial;">⇒\*</span>
<span class="id" type="var">tfalse</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="var">normalize</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_example4'</span> :\
   <span class="id" type="var">tapp</span> <span class="id"
type="var">idBB</span> (<span class="id" type="var">tapp</span> <span
class="id" type="var">notB</span> <span class="id"
type="var">ttrue</span>) <span style="font-family: arial;">⇒\*</span>
<span class="id" type="var">tfalse</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="var">normalize</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (step\_example3) {.section}

Try to do this one both with and without <span class="inlinecode"><span
class="id" type="var">normalize</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_example5</span> :\
        (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">idBBBB</span> <span
class="id" type="var">idBB</span>) <span class="id"
type="var">idB</span>)\
   <span style="font-family: arial;">⇒\*</span> <span class="id"
type="var">idB</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
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

Typing {.section}
------

</div>

<div class="code code-space">

\

</div>

<div class="doc">

### Contexts {.section}

<div class="paragraph">

</div>

*Question*: What is the type of the term "<span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="var">y</span></span>"?
<div class="paragraph">

</div>

*Answer*: It depends on the types of <span class="inlinecode"><span
class="id" type="var">x</span></span> and <span class="inlinecode"><span
class="id" type="var">y</span></span>!
<div class="paragraph">

</div>

I.e., in order to assign a type to a term, we need to know what
assumptions we should make about the types of its free variables.
<div class="paragraph">

</div>

This leads us to a three-place "typing judgment", informally written
<span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">∈</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>, where <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> is a "typing
context" — a mapping from variables to their types.
<div class="paragraph">

</div>

We hide the definition of partial maps in a module since it is actually
defined in <span class="inlinecode"><span class="id"
type="var">SfLib</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">PartialMap</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">partial\_map</span> (<span class="id"
type="var">A</span>:<span class="id" type="keyword">Type</span>) :=
<span class="id" type="var">id</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">option</span> <span class="id" type="var">A</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">empty</span> {<span class="id" type="var">A</span>:<span
class="id" type="keyword">Type</span>} : <span class="id"
type="var">partial\_map</span> <span class="id" type="var">A</span> :=
(<span class="id" type="keyword">fun</span> <span class="id"
type="var">\_</span> ⇒ <span class="id" type="var">None</span>).\
\

</div>

<div class="doc">

Informally, we'll write <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,</span> <span
class="inlinecode"><span class="id" type="var">x</span>:<span class="id"
type="var">T</span></span> for "extend the partial function <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> to also map
<span class="inlinecode"><span class="id" type="var">x</span></span> to
<span class="inlinecode"><span class="id" type="var">T</span></span>."
Formally, we use the function <span class="inlinecode"><span class="id"
type="var">extend</span></span> to add a binding to a partial map.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">extend</span> {<span class="id" type="var">A</span>:<span
class="id" type="keyword">Type</span>} (<span
style="font-family: serif; font-size:85%;">Γ</span> : <span class="id"
type="var">partial\_map</span> <span class="id" type="var">A</span>)
(<span class="id" type="var">x</span>:<span class="id"
type="var">id</span>) (<span class="id" type="var">T</span> : <span
class="id" type="var">A</span>) :=\
   <span class="id" type="keyword">fun</span> <span class="id"
type="var">x'</span> ⇒ <span class="id" type="keyword">if</span> <span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">x'</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">Some</span> <span class="id" type="var">T</span> <span
class="id" type="keyword">else</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x'</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">extend\_eq</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">A</span>
(<span class="id" type="var">ctxt</span>: <span class="id"
type="var">partial\_map</span> <span class="id" type="var">A</span>)
<span class="id" type="var">x</span> <span class="id"
type="var">T</span>,\
   (<span class="id" type="var">extend</span> <span class="id"
type="var">ctxt</span> <span class="id" type="var">x</span> <span
class="id" type="var">T</span>) <span class="id" type="var">x</span> =
<span class="id" type="var">Some</span> <span class="id"
type="var">T</span>.\
<div id="proofcontrol3" class="togglescript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')">

<span class="show"></span>

</div>

<div id="proof3" class="proofscript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">extend</span>.
<span class="id" type="tactic">rewrite</span> <span class="id"
type="var">eq\_id</span>. <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">extend\_neq</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">A</span>
(<span class="id" type="var">ctxt</span>: <span class="id"
type="var">partial\_map</span> <span class="id" type="var">A</span>)
<span class="id" type="var">x1</span> <span class="id"
type="var">T</span> <span class="id" type="var">x2</span>,\
   <span class="id" type="var">x2</span> ≠ <span class="id"
type="var">x1</span> <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">extend</span> <span class="id"
type="var">ctxt</span> <span class="id" type="var">x2</span> <span
class="id" type="var">T</span>) <span class="id" type="var">x1</span> =
<span class="id" type="var">ctxt</span> <span class="id"
type="var">x1</span>.\
<div id="proofcontrol4" class="togglescript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')">

<span class="show"></span>

</div>

<div id="proof4" class="proofscript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">extend</span>.
<span class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>; <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">PartialMap</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">context</span> := <span class="id"
type="var">partial\_map</span> <span class="id" type="var">ty</span>.\
\

</div>

<div class="doc">

### Typing Relation {.section}

<div class="paragraph">

</div>

<span style="font-family: serif; font-size:85%;">Γ</span> x = T
(T\_Var)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> x ∈ T
<span
style="font-family: serif; font-size:85%;">Γ</span> , x:T~11~ <span
style="font-family: arial;">⊢</span> t~12~ ∈ T~12~
(T\_Abs)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> \\x:T~11~.t~12~ ∈ T~11~-\>T~12~
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ ∈ T~11~-\>T~12~
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~2~ ∈ T~11~
(T\_App)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ t~2~ ∈ T~12~
  
(T\_True)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> true ∈ Bool
  
(T\_False)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> false ∈ Bool
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ ∈ Bool    <span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~2~ ∈ T    <span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~3~ ∈ T
(T\_If)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> if t~1~ then t~2~ else t~3~ ∈ T
<div class="paragraph">

</div>

We can read the three-place relation <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">∈</span> <span class="inlinecode"><span
class="id" type="var">T</span></span> as: "to the term <span
class="inlinecode"><span class="id" type="var">t</span></span> we can
assign the type <span class="inlinecode"><span class="id"
type="var">T</span></span> using as types for the free variables of
<span class="inlinecode"><span class="id" type="var">t</span></span> the
ones specified in the context <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span>."

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> "Gamma '<span
style="font-family: arial;">⊢</span>' t '∈' T" (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">has\_type</span> : <span class="id" type="var">context</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">T\_Var</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
class="id" type="var">x</span> = <span class="id" type="var">Some</span>
<span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tvar</span> <span class="id" type="var">x</span> ∈ <span
class="id" type="var">T</span>\
   | <span class="id" type="var">T\_Abs</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T~11~</span> <span
class="id" type="var">T~12~</span> <span class="id"
type="var">t~12~</span>,\
       <span class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T~11~</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~12~</span> ∈ <span class="id" type="var">T~12~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span> ∈ <span class="id" type="var">TArrow</span>
<span class="id" type="var">T~11~</span> <span class="id"
type="var">T~12~</span>\
   | <span class="id" type="var">T\_App</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T~11~</span> <span class="id" type="var">T~12~</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TArrow</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">T~12~</span> <span style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T~11~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> ∈ <span class="id"
type="var">T~12~</span>\
   | <span class="id" type="var">T\_True</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span>,\
        <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">ttrue</span> ∈ <span class="id" type="var">TBool</span>\
   | <span class="id" type="var">T\_False</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span>,\
        <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tfalse</span> ∈ <span class="id" type="var">TBool</span>\
   | <span class="id" type="var">T\_If</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> <span class="id" type="var">T</span>
<span style="font-family: serif; font-size:85%;">Γ</span>,\
        <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TBool</span> <span
style="font-family: arial;">→</span>\
        <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
        <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~3~</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
        <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tif</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span> ∈ <span class="id" type="var">T</span>\
\
 <span class="id" type="keyword">where</span> "Gamma '<span
style="font-family: arial;">⊢</span>' t '∈' T" := (<span class="id"
type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span>).\
<div id="proofcontrol5" class="togglescript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')">

<span class="show"></span>

</div>

<div id="proof5" class="proofscript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')"
style="display: none;">

\
 <span class="id" type="keyword">Tactic Notation</span>
"has\_type\_cases" <span class="id" type="var">tactic</span>(<span
class="id" type="var">first</span>) <span class="id"
type="var">ident</span>(<span class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Var" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_Abs"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_App" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_True"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_False" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "T\_If"
].\

</div>

\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">has\_type</span>.\
\

</div>

<div class="doc">

### Examples {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_example\_1</span> :\
   <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">TBool</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) ∈ <span
class="id" type="var">TArrow</span> <span class="id"
type="var">TBool</span> <span class="id" type="var">TBool</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">T\_Var</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Note that since we added the <span class="inlinecode"><span class="id"
type="var">has\_type</span></span> constructors to the hints database,
auto can actually solve this one immediately.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_example\_1'</span> :\
   <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">TBool</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) ∈ <span
class="id" type="var">TArrow</span> <span class="id"
type="var">TBool</span> <span class="id" type="var">TBool</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">auto</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Another example:
<div class="paragraph">

</div>

<div class="code code-tight">

     <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> \\<span class="id"
type="var">x</span>:<span class="id" type="var">A</span>. λ<span
class="id" type="var">y</span>:<span class="id" type="var">A</span><span
style="font-family: arial;">→</span><span class="id"
type="var">A</span>. <span class="id" type="var">y</span> (<span
class="id" type="var">y</span> <span class="id" type="var">x</span>)) \
            ∈ <span class="id" type="var">A</span> <span
style="font-family: arial;">→</span> (<span class="id"
type="var">A</span><span style="font-family: arial;">→</span><span
class="id" type="var">A</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">A</span>.
<div class="paragraph">

</div>

</div>

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

<span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_example\_2</span> :\
   <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span>\
     (<span class="id" type="var">tabs</span> <span class="id"
type="var">x</span> <span class="id" type="var">TBool</span>\
        (<span class="id" type="var">tabs</span> <span class="id"
type="var">y</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">TBool</span> <span class="id"
type="var">TBool</span>)\
           (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">y</span>) (<span
class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">y</span>) (<span
class="id" type="var">tvar</span> <span class="id"
type="var">x</span>))))) ∈\
     (<span class="id" type="var">TArrow</span> <span class="id"
type="var">TBool</span> (<span class="id" type="var">TArrow</span>
(<span class="id" type="var">TArrow</span> <span class="id"
type="var">TBool</span> <span class="id" type="var">TBool</span>) <span
class="id" type="var">TBool</span>)).\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>
<span class="id" type="keyword">using</span> <span class="id"
type="var">extend\_eq</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_App</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">T\_Var</span>...\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_App</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">T\_Var</span>...\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Var</span>...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (typing\_example\_2\_full) {.section}

Prove the same result without using <span class="inlinecode"><span
class="id" type="tactic">auto</span></span>, <span
class="inlinecode"><span class="id" type="tactic">eauto</span></span>,
or <span class="inlinecode"><span class="id"
type="tactic">eapply</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_example\_2\_full</span> :\
   <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span>\
     (<span class="id" type="var">tabs</span> <span class="id"
type="var">x</span> <span class="id" type="var">TBool</span>\
        (<span class="id" type="var">tabs</span> <span class="id"
type="var">y</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">TBool</span> <span class="id"
type="var">TBool</span>)\
           (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">y</span>) (<span
class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">y</span>) (<span
class="id" type="var">tvar</span> <span class="id"
type="var">x</span>))))) ∈\
     (<span class="id" type="var">TArrow</span> <span class="id"
type="var">TBool</span> (<span class="id" type="var">TArrow</span>
(<span class="id" type="var">TArrow</span> <span class="id"
type="var">TBool</span> <span class="id" type="var">TBool</span>) <span
class="id" type="var">TBool</span>)).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (typing\_example\_3) {.section}

Formally prove the following typing derivation holds:
<div class="paragraph">

</div>

<div class="code code-tight">

   <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> \\<span class="id"
type="var">x</span>:<span class="id" type="var">Bool</span><span
style="font-family: arial;">→</span><span class="id"
type="var">B</span>. λ<span class="id" type="var">y</span>:<span
class="id" type="var">Bool</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Bool</span>. λ<span class="id" type="var">z</span>:<span
class="id" type="var">Bool</span>.\
                <span class="id" type="var">y</span> (<span class="id"
type="var">x</span> <span class="id" type="var">z</span>) \
          ∈ <span class="id" type="var">T</span>.
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_example\_3</span> :\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">T</span>,\
     <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span>\
       (<span class="id" type="var">tabs</span> <span class="id"
type="var">x</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">TBool</span> <span class="id"
type="var">TBool</span>)\
          (<span class="id" type="var">tabs</span> <span class="id"
type="var">y</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">TBool</span> <span class="id"
type="var">TBool</span>)\
             (<span class="id" type="var">tabs</span> <span class="id"
type="var">z</span> <span class="id" type="var">TBool</span>\
                (<span class="id" type="var">tapp</span> (<span
class="id" type="var">tvar</span> <span class="id" type="var">y</span>)
(<span class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) (<span
class="id" type="var">tvar</span> <span class="id"
type="var">z</span>)))))) ∈\
       <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

We can also show that terms are *not* typable. For example, let's
formally check that there is no typing derivation assigning a type to
the term <span class="inlinecode">\\<span class="id"
type="var">x</span>:<span class="id" type="var">Bool</span>.</span>
<span class="inlinecode">\\<span class="id" type="var">y</span>:<span
class="id" type="var">Bool</span>,</span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="var">y</span></span> — i.e.,
<div class="paragraph">

</div>

<div class="code code-tight">

    ¬ <span style="font-family: arial;">∃</span><span class="id"
type="var">T</span>,\
         <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> \\<span class="id"
type="var">x</span>:<span class="id" type="var">Bool</span>. λ<span
class="id" type="var">y</span>:<span class="id"
type="var">Bool</span>, <span class="id" type="var">x</span> <span
class="id" type="var">y</span> : <span class="id" type="var">T</span>.
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
<div id="proofcontrol7" class="togglescript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')">

<span class="show"></span>

</div>

<div id="proof7" class="proofscript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')"
style="display: none;">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_nonexample\_1</span> :\
   ¬ <span style="font-family: arial;">∃</span><span class="id"
type="var">T</span>,\
       <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span>\
         (<span class="id" type="var">tabs</span> <span class="id"
type="var">x</span> <span class="id" type="var">TBool</span>\
             (<span class="id" type="var">tabs</span> <span class="id"
type="var">y</span> <span class="id" type="var">TBool</span>\
                (<span class="id" type="var">tapp</span> (<span
class="id" type="var">tvar</span> <span class="id" type="var">x</span>)
(<span class="id" type="var">tvar</span> <span class="id"
type="var">y</span>)))) ∈\
         <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">Hc</span>. <span class="id" type="tactic">inversion</span>
<span class="id" type="var">Hc</span>.\
   <span class="comment">(\* The <span class="inlinecode"><span
class="id"
type="tactic">clear</span></span> tactic is useful here for tidying away bits of\
      the context that we're not going to need again. \*)</span>\
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
   <span
class="comment">(\* rewrite extend\_neq in H1. rewrite extend\_eq in H1. \*)</span>\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H1</span>. <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

#### Exercise: 3 stars, optional (typing\_nonexample\_3) {.section}

Another nonexample:
<div class="paragraph">

</div>

<div class="code code-tight">

    ¬ (<span style="font-family: arial;">∃</span><span class="id"
type="var">S</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">T</span>,\
           <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> \\<span class="id"
type="var">x</span>:<span class="id" type="var">S</span>. <span
class="id" type="var">x</span> <span class="id"
type="var">x</span> : <span class="id" type="var">T</span>).
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_nonexample\_3</span> :\
   ¬ (<span style="font-family: arial;">∃</span><span class="id"
type="var">S</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">T</span>,\
         <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span>\
           (<span class="id" type="var">tabs</span> <span class="id"
type="var">x</span> <span class="id" type="var">S</span>\
              (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) (<span
class="id" type="var">tvar</span> <span class="id"
type="var">x</span>))) ∈\
           <span class="id" type="var">T</span>).\
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
type="var">STLC</span>.\
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
