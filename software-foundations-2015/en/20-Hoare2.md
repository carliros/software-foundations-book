<div id="page">

<div id="header">

</div>

<div id="main">

Hoare2<span class="subtitle">Hoare Logic, Part II</span> {.libtitle}
========================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">Hoare</span>.\
\

</div>

<div class="doc">

Decorated Programs {.section}
==================

<div class="paragraph">

</div>

The beauty of Hoare Logic is that it is *compositional* — the structure
of proofs exactly follows the structure of programs. This suggests that
we can record the essential ideas of a proof informally (leaving out
some low-level calculational details) by decorating programs with
appropriate assertions around each statement. Such a *decorated program*
carries with it an (informal) proof of its own correctness.
<div class="paragraph">

</div>

For example, here is a complete decorated program:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">m</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">m</span>;;\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">p</span> = <span class="id" type="var">p</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Z</span> ::= <span class="id"
type="var">p</span>;\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Z</span> = <span class="id" type="var">p</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> - <span class="id" type="var">X</span> = <span
class="id" type="var">p</span> - <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ 0 <span class="id" type="var">DO</span>\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> - <span class="id" type="var">X</span> = <span
class="id" type="var">p</span> - <span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">X</span> ≠ 0 <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
         <span style="letter-spacing:-.4em;">{</span>{ (<span class="id"
type="var">Z</span> - 1) - (<span class="id"
type="var">X</span> - 1) = <span class="id" type="var">p</span> - <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span> - 1;;\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> - (<span class="id" type="var">X</span> - 1) = <span
class="id" type="var">p</span> - <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 1\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> - <span class="id" type="var">X</span> = <span
class="id" type="var">p</span> - <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">END</span>;\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> - <span class="id" type="var">X</span> = <span
class="id" type="var">p</span> - <span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> ¬ (<span
class="id" type="var">X</span> ≠ 0) <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">p</span> - <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>} 
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Concretely, a decorated program consists of the program text interleaved
with assertions. To check that a decorated program represents a valid
proof, we check that each individual command is *locally consistent*
with its accompanying assertions in the following sense:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">SKIP</span></span> is locally consistent if its
    precondition and postcondition are the same:
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">P</span> <span style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">SKIP</span>\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">P</span> <span style="letter-spacing:-.4em;">}</span>}
    <div class="paragraph">

    </div>

    </div>

<div class="paragraph">

</div>

<div class="paragraph">

</div>

-   The sequential composition of <span class="inlinecode"><span
    class="id" type="var">c1</span></span> and <span
    class="inlinecode"><span class="id" type="var">c2</span></span> is
    locally consistent (with respect to assertions <span
    class="inlinecode"><span class="id" type="var">P</span></span> and
    <span class="inlinecode"><span class="id"
    type="var">R</span></span>) if <span class="inlinecode"><span
    class="id" type="var">c1</span></span> is locally consistent (with
    respect to <span class="inlinecode"><span class="id"
    type="var">P</span></span> and <span class="inlinecode"><span
    class="id" type="var">Q</span></span>) and <span
    class="inlinecode"><span class="id" type="var">c2</span></span> is
    locally consistent (with respect to <span class="inlinecode"><span
    class="id" type="var">Q</span></span> and <span
    class="inlinecode"><span class="id" type="var">R</span></span>):
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">P</span> <span style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">c1</span>;;\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">Q</span> <span style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">c2</span>\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">R</span> <span style="letter-spacing:-.4em;">}</span>}
    <div class="paragraph">

    </div>

    </div>

<div class="paragraph">

</div>

<div class="paragraph">

</div>

-   An assignment is locally consistent if its precondition is the
    appropriate substitution of its postcondition:
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">P</span> [<span class="id" type="var">X</span> <span
    style="font-family: arial;">↦</span> <span class="id"
    type="var">a</span>] <span style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">X</span> ::= <span class="id"
    type="var">a</span>\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">P</span> <span style="letter-spacing:-.4em;">}</span>}
    <div class="paragraph">

    </div>

    </div>

<div class="paragraph">

</div>

<div class="paragraph">

</div>

-   A conditional is locally consistent (with respect to assertions
    <span class="inlinecode"><span class="id" type="var">P</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">Q</span></span>) if the assertions at the top of its
    "then" and "else" branches are exactly <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode"><span style="font-family: arial;">∧</span></span>
    <span class="inlinecode"><span class="id" type="var">b</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">P</span></span> <span class="inlinecode"><span
    style="font-family: arial;">∧</span></span> <span
    class="inlinecode">¬<span class="id" type="var">b</span></span> and
    if its "then" branch is locally consistent (with respect to <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode"><span style="font-family: arial;">∧</span></span>
    <span class="inlinecode"><span class="id" type="var">b</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">Q</span></span>) and its "else" branch is locally
    consistent (with respect to <span class="inlinecode"><span
    class="id" type="var">P</span></span> <span class="inlinecode"><span
    style="font-family: arial;">∧</span></span> <span
    class="inlinecode">¬<span class="id" type="var">b</span></span> and
    <span class="inlinecode"><span class="id"
    type="var">Q</span></span>):
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">P</span> <span style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">IFB</span> <span class="id"
    type="var">b</span> <span class="id" type="var">THEN</span>\
           <span style="letter-spacing:-.4em;">{</span>{ <span
    class="id" type="var">P</span> <span
    style="font-family: arial;">∧</span> <span class="id"
    type="var">b</span> <span style="letter-spacing:-.4em;">}</span>}\
           <span class="id" type="var">c1</span>\
           <span style="letter-spacing:-.4em;">{</span>{ <span
    class="id" type="var">Q</span> <span
    style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">ELSE</span>\
           <span style="letter-spacing:-.4em;">{</span>{ <span
    class="id" type="var">P</span> <span
    style="font-family: arial;">∧</span> ¬<span class="id"
    type="var">b</span> <span style="letter-spacing:-.4em;">}</span>}\
           <span class="id" type="var">c2</span>\
           <span style="letter-spacing:-.4em;">{</span>{ <span
    class="id" type="var">Q</span> <span
    style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">FI</span>\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">Q</span> <span style="letter-spacing:-.4em;">}</span>}
    <div class="paragraph">

    </div>

    </div>

<div class="paragraph">

</div>

<div class="paragraph">

</div>

-   A while loop with precondition <span class="inlinecode"><span
    class="id" type="var">P</span></span> is locally consistent if its
    postcondition is <span class="inlinecode"><span class="id"
    type="var">P</span></span> <span class="inlinecode"><span
    style="font-family: arial;">∧</span></span> <span
    class="inlinecode">¬<span class="id" type="var">b</span></span> and
    if the pre- and postconditions of its body are exactly <span
    class="inlinecode"><span class="id" type="var">P</span></span> <span
    class="inlinecode"><span style="font-family: arial;">∧</span></span>
    <span class="inlinecode"><span class="id" type="var">b</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">P</span></span>:
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">P</span> <span style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">WHILE</span> <span class="id"
    type="var">b</span> <span class="id" type="var">DO</span>\
           <span style="letter-spacing:-.4em;">{</span>{ <span
    class="id" type="var">P</span> <span
    style="font-family: arial;">∧</span> <span class="id"
    type="var">b</span> <span style="letter-spacing:-.4em;">}</span>}\
           <span class="id" type="var">c1</span>\
           <span style="letter-spacing:-.4em;">{</span>{ <span
    class="id" type="var">P</span> <span
    style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">END</span>\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">P</span> <span
    style="font-family: arial;">∧</span> ¬<span class="id"
    type="var">b</span> <span style="letter-spacing:-.4em;">}</span>}
    <div class="paragraph">

    </div>

    </div>

<div class="paragraph">

</div>

<div class="paragraph">

</div>

-   A pair of assertions separated by <span class="inlinecode"><span
    style="font-family: arial;">⇾</span></span> is locally consistent if
    the first implies the second (in all states):
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">P</span> <span
    style="letter-spacing:-.4em;">}</span>} <span
    style="font-family: arial;">⇾</span>\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
    type="var">P'</span> <span style="letter-spacing:-.4em;">}</span>}
    <div class="paragraph">

    </div>

    </div>

    <div class="paragraph">

    </div>

    This corresponds to the application of <span
    class="inlinecode"><span class="id"
    type="var">hoare\_consequence</span></span> and is the only place in
    a decorated program where checking if decorations are correct is not
    fully mechanical and syntactic, but involves logical and/or
    arithmetic reasoning.

<div class="paragraph">

</div>

We have seen above how *verifying* the correctness of a given proof
involves checking that every single command is locally consistent with
the accompanying assertions. If we are instead interested in *finding* a
proof for a given specification we need to discover the right
assertions. This can be done in an almost automatic way, with the
exception of finding loop invariants, which is the subject of in the
next section. In the reminder of this section we explain in detail how
to construct decorations for several simple programs that don't involve
non-trivial loop invariants.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Example: Swapping Using Addition and Subtraction {.section}
------------------------------------------------

<div class="paragraph">

</div>

Here is a program that swaps the values of two variables using addition
and subtraction (instead of by assigning to a temporary variable).
<div class="paragraph">

</div>

<div class="code code-tight">

  <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> + <span class="id" type="var">Y</span>;;\
   <span class="id" type="var">Y</span> ::= <span class="id"
type="var">X</span> - <span class="id" type="var">Y</span>;;\
   <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - <span class="id" type="var">Y</span>
<div class="paragraph">

</div>

</div>

We can prove using decorations that this program is correct — i.e., it
always swaps the values of variables <span class="inlinecode"><span
class="id" type="var">X</span></span> and <span class="inlinecode"><span
class="id" type="var">Y</span></span>.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

 (1)     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Y</span> = <span class="id" type="var">n</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
  (2)     <span style="letter-spacing:-.4em;">{</span>{ (<span
class="id" type="var">X</span> + <span class="id"
type="var">Y</span>) - ((<span class="id" type="var">X</span> + <span
class="id" type="var">Y</span>) - <span class="id"
type="var">Y</span>) = <span class="id" type="var">n</span> <span
style="font-family: arial;">∧</span> (<span class="id"
type="var">X</span> + <span class="id" type="var">Y</span>) - <span
class="id" type="var">Y</span> = <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> + <span class="id" type="var">Y</span>;;\
  (3)     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> - (<span class="id" type="var">X</span> - <span
class="id" type="var">Y</span>) = <span class="id"
type="var">n</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">X</span> - <span class="id"
type="var">Y</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">Y</span> ::= <span class="id"
type="var">X</span> - <span class="id" type="var">Y</span>;;\
  (4)     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> - <span class="id" type="var">Y</span> = <span
class="id" type="var">n</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Y</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - <span class="id" type="var">Y</span>\
  (5)     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">n</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Y</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

The decorations were constructed as follows:
<div class="paragraph">

</div>

-   We begin with the undecorated program (the unnumbered lines).
-   We then add the specification — i.e., the outer precondition (1) and
    postcondition (5). In the precondition we use auxiliary variables
    (parameters) <span class="inlinecode"><span class="id"
    type="var">m</span></span> and <span class="inlinecode"><span
    class="id" type="var">n</span></span> to remember the initial values
    of variables <span class="inlinecode"><span class="id"
    type="var">X</span></span> and respectively <span
    class="inlinecode"><span class="id" type="var">Y</span></span>, so
    that we can refer to them in the postcondition (5).
-   We work backwards mechanically starting from (5) all the way to (2).
    At each step, we obtain the precondition of the assignment from its
    postcondition by substituting the assigned variable with the
    right-hand-side of the assignment. For instance, we obtain (4) by
    substituting <span class="inlinecode"><span class="id"
    type="var">X</span></span> with <span class="inlinecode"><span
    class="id" type="var">X</span></span> <span
    class="inlinecode">-</span> <span class="inlinecode"><span
    class="id" type="var">Y</span></span> in (5), and (3) by
    substituting <span class="inlinecode"><span class="id"
    type="var">Y</span></span> with <span class="inlinecode"><span
    class="id" type="var">X</span></span> <span
    class="inlinecode">-</span> <span class="inlinecode"><span
    class="id" type="var">Y</span></span> in (4).
-   Finally, we verify that (1) logically implies (2) — i.e., that the
    step from (1) to (2) is a valid use of the law of consequence. For
    this we substitute <span class="inlinecode"><span class="id"
    type="var">X</span></span> by <span class="inlinecode"><span
    class="id" type="var">m</span></span> and <span
    class="inlinecode"><span class="id" type="var">Y</span></span> by
    <span class="inlinecode"><span class="id" type="var">n</span></span>
    and calculate as follows:
    <div class="paragraph">

    </div>

    <div class="code code-tight">

        (<span class="id" type="var">m</span> + <span class="id"
    type="var">n</span>) - ((<span class="id"
    type="var">m</span> + <span class="id" type="var">n</span>) - <span
    class="id" type="var">n</span>) = <span class="id"
    type="var">n</span> <span
    style="font-family: arial;">∧</span> (<span class="id"
    type="var">m</span> + <span class="id" type="var">n</span>) - <span
    class="id" type="var">n</span> = <span class="id"
    type="var">m</span>\
         (<span class="id" type="var">m</span> + <span class="id"
    type="var">n</span>) - <span class="id" type="var">m</span> = <span
    class="id" type="var">n</span> <span
    style="font-family: arial;">∧</span> <span class="id"
    type="var">m</span> = <span class="id" type="var">m</span>\
         <span class="id" type="var">n</span> = <span class="id"
    type="var">n</span> <span style="font-family: arial;">∧</span> <span
    class="id" type="var">m</span> = <span class="id"
    type="var">m</span>
    <div class="paragraph">

    </div>

    </div>

<div class="paragraph">

</div>

(Note that, since we are working with natural numbers, not fixed-size
machine integers, we don't need to worry about the possibility of
arithmetic overflow anywhere in this argument.)

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Example: Simple Conditionals {.section}
----------------------------

<div class="paragraph">

</div>

Here is a simple decorated program using conditionals:
<div class="paragraph">

</div>

<div class="code code-tight">

 (1)     <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">True</span><span style="letter-spacing:-.4em;">}</span>}\
        <span class="id" type="var">IFB</span> <span class="id"
type="var">X</span> ≤ <span class="id" type="var">Y</span> <span
class="id" type="var">THEN</span>\
  (2)       <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> ≤ <span class="id" type="var">Y</span><span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
  (3)       <span style="letter-spacing:-.4em;">{</span>{(<span
class="id" type="var">Y</span> - <span class="id"
type="var">X</span>) + <span class="id" type="var">X</span> = <span
class="id" type="var">Y</span> <span
style="font-family: arial;">∨</span> (<span class="id"
type="var">Y</span> - <span class="id" type="var">X</span>) + <span
class="id" type="var">Y</span> = <span class="id"
type="var">X</span><span style="letter-spacing:-.4em;">}</span>}\
          <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Y</span> - <span class="id" type="var">X</span>\
  (4)       <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">Z</span> + <span class="id"
type="var">X</span> = <span class="id" type="var">Y</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">Z</span> + <span class="id" type="var">Y</span> = <span
class="id" type="var">X</span><span
style="letter-spacing:-.4em;">}</span>}\
        <span class="id" type="var">ELSE</span>\
  (5)       <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> \~(<span class="id"
type="var">X</span> ≤ <span class="id" type="var">Y</span>) <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
  (6)       <span style="letter-spacing:-.4em;">{</span>{(<span
class="id" type="var">X</span> - <span class="id"
type="var">Y</span>) + <span class="id" type="var">X</span> = <span
class="id" type="var">Y</span> <span
style="font-family: arial;">∨</span> (<span class="id"
type="var">X</span> - <span class="id" type="var">Y</span>) + <span
class="id" type="var">Y</span> = <span class="id"
type="var">X</span><span style="letter-spacing:-.4em;">}</span>}\
          <span class="id" type="var">Z</span> ::= <span class="id"
type="var">X</span> - <span class="id" type="var">Y</span>\
  (7)       <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">Z</span> + <span class="id"
type="var">X</span> = <span class="id" type="var">Y</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">Z</span> + <span class="id" type="var">Y</span> = <span
class="id" type="var">X</span><span
style="letter-spacing:-.4em;">}</span>}\
        <span class="id" type="var">FI</span>\
  (8)     <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Z</span> + <span class="id" type="var">X</span> = <span
class="id" type="var">Y</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">Z</span> + <span class="id" type="var">Y</span> = <span
class="id" type="var">X</span><span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

These decorations were constructed as follows:
<div class="paragraph">

</div>

-   We start with the outer precondition (1) and postcondition (8).
-   We follow the format dictated by the <span class="inlinecode"><span
    class="id" type="var">hoare\_if</span></span> rule and copy the
    postcondition (8) to (4) and (7). We conjoin the precondition (1)
    with the guard of the conditional to obtain (2). We conjoin (1) with
    the negated guard of the conditional to obtain (5).
-   In order to use the assignment rule and obtain (3), we substitute
    <span class="inlinecode"><span class="id" type="var">Z</span></span>
    by <span class="inlinecode"><span class="id"
    type="var">Y</span></span> <span class="inlinecode">-</span> <span
    class="inlinecode"><span class="id" type="var">X</span></span> in
    (4). To obtain (6) we substitute <span class="inlinecode"><span
    class="id" type="var">Z</span></span> by <span
    class="inlinecode"><span class="id" type="var">X</span></span> <span
    class="inlinecode">-</span> <span class="inlinecode"><span
    class="id" type="var">Y</span></span> in (7).
-   Finally, we verify that (2) implies (3) and (5) implies (6). Both of
    these implications crucially depend on the ordering of <span
    class="inlinecode"><span class="id" type="var">X</span></span> and
    <span class="inlinecode"><span class="id" type="var">Y</span></span>
    obtained from the guard. For instance, knowing that <span
    class="inlinecode"><span class="id" type="var">X</span></span> <span
    class="inlinecode">≤</span> <span class="inlinecode"><span
    class="id" type="var">Y</span></span> ensures that subtracting <span
    class="inlinecode"><span class="id" type="var">X</span></span> from
    <span class="inlinecode"><span class="id" type="var">Y</span></span>
    and then adding back <span class="inlinecode"><span class="id"
    type="var">X</span></span> produces <span class="inlinecode"><span
    class="id" type="var">Y</span></span>, as required by the first
    disjunct of (3). Similarly, knowing that <span
    class="inlinecode">\~(<span class="id" type="var">X</span></span>
    <span class="inlinecode">≤</span> <span class="inlinecode"><span
    class="id" type="var">Y</span>)</span> ensures that subtracting
    <span class="inlinecode"><span class="id" type="var">Y</span></span>
    from <span class="inlinecode"><span class="id"
    type="var">X</span></span> and then adding back <span
    class="inlinecode"><span class="id" type="var">Y</span></span>
    produces <span class="inlinecode"><span class="id"
    type="var">X</span></span>, as needed by the second disjunct of (6).
    Note that <span class="inlinecode"><span class="id"
    type="var">n</span></span> <span class="inlinecode">-</span> <span
    class="inlinecode"><span class="id" type="var">m</span></span> <span
    class="inlinecode">+</span> <span class="inlinecode"><span
    class="id" type="var">m</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> does *not* hold for arbitrary
    natural numbers <span class="inlinecode"><span class="id"
    type="var">n</span></span> and <span class="inlinecode"><span
    class="id" type="var">m</span></span> (for example, <span
    class="inlinecode">3</span> <span class="inlinecode">-</span> <span
    class="inlinecode">5</span> <span class="inlinecode">+</span> <span
    class="inlinecode">5</span> <span class="inlinecode">=</span> <span
    class="inlinecode">5</span>).

<div class="paragraph">

</div>

#### Exercise: 2 stars (if\_minus\_plus\_reloaded) {.section}

Fill in valid decorations for the following program:
<div class="paragraph">

</div>

<div class="code code-tight">

   <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">True</span> <span style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">IFB</span> <span class="id"
type="var">X</span> ≤ <span class="id" type="var">Y</span> <span
class="id" type="var">THEN</span>\
       <span
style="letter-spacing:-.4em;">{</span>{                         <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
       <span
style="letter-spacing:-.4em;">{</span>{                         <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Y</span> - <span class="id" type="var">X</span>\
       <span
style="letter-spacing:-.4em;">{</span>{                         <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">ELSE</span>\
       <span
style="letter-spacing:-.4em;">{</span>{                         <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
       <span
style="letter-spacing:-.4em;">{</span>{                         <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">X</span> + <span class="id" type="var">Z</span>\
       <span
style="letter-spacing:-.4em;">{</span>{                         <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">FI</span>\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Y</span> = <span class="id" type="var">X</span> + <span
class="id" type="var">Z</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Example: Reduce to Zero (Trivial Loop) {.section}
--------------------------------------

<div class="paragraph">

</div>

Here is a <span class="inlinecode"><span class="id"
type="var">WHILE</span></span> loop that is so simple it needs no
invariant (i.e., the invariant <span class="inlinecode"><span class="id"
type="var">True</span></span> will do the job).
<div class="paragraph">

</div>

<div class="code code-tight">

 (1)      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">True</span> <span style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ 0 <span class="id" type="var">DO</span>\
  (2)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> ≠ 0 <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
  (3)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>}\
           <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 1\
  (4)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">END</span>\
  (5)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = 0 <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
  (6)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">X</span> = 0 <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

The decorations can be constructed as follows:
<div class="paragraph">

</div>

-   Start with the outer precondition (1) and postcondition (6).
-   Following the format dictated by the <span class="inlinecode"><span
    class="id" type="var">hoare\_while</span></span> rule, we copy (1)
    to (4). We conjoin (1) with the guard to obtain (2) and with the
    negation of the guard to obtain (5). Note that, because the outer
    postcondition (6) does not syntactically match (5), we need a
    trivial use of the consequence rule from (5) to (6).
-   Assertion (3) is the same as (4), because <span
    class="inlinecode"><span class="id" type="var">X</span></span> does
    not appear in <span class="inlinecode">4</span>, so the substitution
    in the assignment rule is trivial.
-   Finally, the implication between (2) and (3) is also trivial.

<div class="paragraph">

</div>

From this informal proof, it is easy to read off a formal proof using
the Coq versions of the Hoare rules. Note that we do *not* unfold the
definition of <span class="inlinecode"><span class="id"
type="var">hoare\_triple</span></span> anywhere in this proof — the idea
is to use the Hoare rules as a "self-contained" logic for reasoning
about programs.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">reduce\_to\_zero'</span> : <span class="id"
type="var">com</span> :=\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 0)) <span class="id"
type="var">DO</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1)\
   <span class="id" type="var">END</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">reduce\_to\_zero\_correct'</span> :\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">True</span><span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">reduce\_to\_zero'</span>\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> =
0<span style="letter-spacing:-.4em;">}</span>}.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">reduce\_to\_zero'</span>.\
   <span
class="comment">(\* First we need to transform the postcondition so\
      that hoare\_while will apply. \*)</span>\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_post</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_while</span>.\
   <span class="id" type="var">Case</span> "Loop body preserves
invariant".\
     <span class="comment">(\* Need to massage precondition before <span
class="inlinecode"><span class="id"
type="var">hoare\_asgn</span></span> applies \*)</span>\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">hoare\_asgn</span>.\
     <span
class="comment">(\* Proving trivial implication (2) -\>\> (3) \*)</span>\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> [<span class="id" type="var">HT</span> <span
class="id" type="var">Hbp</span>]. <span class="id"
type="tactic">unfold</span> <span class="id"
type="var">assn\_sub</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">I</span>.\
   <span class="id" type="var">Case</span> "Invariant and negated guard
imply postcondition".\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> [<span class="id" type="var">Inv</span> <span
class="id" type="var">GuardFalse</span>].\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bassn</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">GuardFalse</span>. <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">GuardFalse</span>.\
     <span
class="comment">(\* SearchAbout helps to find the right lemmas \*)</span>\
     <span class="id" type="var">Search</span><span class="id"
type="var">About</span> [<span class="id" type="var">not</span> <span
class="id" type="var">true</span>].\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">not\_true\_iff\_false</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">GuardFalse</span>.\
     <span class="id" type="var">Search</span><span class="id"
type="var">About</span> [<span class="id" type="var">negb</span> <span
class="id" type="var">false</span>].\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">negb\_false\_iff</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">GuardFalse</span>.\
     <span class="id" type="var">Search</span><span class="id"
type="var">About</span> [<span class="id" type="var">beq\_nat</span>
<span class="id" type="var">true</span>].\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">beq\_nat\_true</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">GuardFalse</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">GuardFalse</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Example: Division {.section}
-----------------

<div class="paragraph">

</div>

The following Imp program calculates the integer division and remainder
of two numbers <span class="inlinecode"><span class="id"
type="var">m</span></span> and <span class="inlinecode"><span class="id"
type="var">n</span></span> that are arbitrary constants in the program.
<div class="paragraph">

</div>

<div class="code code-tight">

  <span class="id" type="var">X</span> ::= <span class="id"
type="var">m</span>;;\
   <span class="id" type="var">Y</span> ::= 0;;\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">n</span> ≤ <span class="id" type="var">X</span> <span
class="id" type="var">DO</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - <span class="id" type="var">n</span>;;\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> + 1\
   <span class="id" type="var">END</span>;
<div class="paragraph">

</div>

</div>

In other words, if we replace <span class="inlinecode"><span class="id"
type="var">m</span></span> and <span class="inlinecode"><span class="id"
type="var">n</span></span> by concrete numbers and execute the program,
it will terminate with the variable <span class="inlinecode"><span
class="id" type="var">X</span></span> set to the remainder when <span
class="inlinecode"><span class="id" type="var">m</span></span> is
divided by <span class="inlinecode"><span class="id"
type="var">n</span></span> and <span class="inlinecode"><span class="id"
type="var">Y</span></span> set to the quotient.
<div class="paragraph">

</div>

In order to give a specification to this program we need to remember
that dividing <span class="inlinecode"><span class="id"
type="var">m</span></span> by <span class="inlinecode"><span class="id"
type="var">n</span></span> produces a reminder <span
class="inlinecode"><span class="id" type="var">X</span></span> and a
quotient <span class="inlinecode"><span class="id"
type="var">Y</span></span> so that <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">×</span>
<span class="inlinecode"><span class="id" type="var">Y</span></span>
<span class="inlinecode">+</span> <span class="inlinecode"><span
class="id" type="var">X</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">m</span></span>
<span class="inlinecode"><span
style="font-family: arial;">∧</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">\<</span> <span class="inlinecode"><span class="id"
type="var">n</span></span>.
<div class="paragraph">

</div>

It turns out that we get lucky with this program and don't have to think
very hard about the loop invariant: the invariant is the just first
conjunct <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode">×</span> <span
class="inlinecode"><span class="id" type="var">Y</span></span> <span
class="inlinecode">+</span> <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">m</span></span>, so we
use that to decorate the program.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

 (1)    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
  (2)    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">n</span> × 0 + <span class="id" type="var">m</span> = <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">X</span> ::= <span class="id"
type="var">m</span>;;\
  (3)    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">n</span> × 0 + <span class="id" type="var">X</span> = <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">Y</span> ::= 0;;\
  (4)    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">n</span> × <span class="id" type="var">Y</span> + <span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">WHILE</span> <span class="id"
type="var">n</span> ≤ <span class="id" type="var">X</span> <span
class="id" type="var">DO</span>\
  (5)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">n</span> × <span class="id"
type="var">Y</span> + <span class="id" type="var">X</span> = <span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">n</span> ≤ <span class="id" type="var">X</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
  (6)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">n</span> × (<span class="id"
type="var">Y</span> + 1) + (<span class="id" type="var">X</span> - <span
class="id" type="var">n</span>) = <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - <span class="id" type="var">n</span>;;\
  (7)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">n</span> × (<span class="id"
type="var">Y</span> + 1) + <span class="id" type="var">X</span> = <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
         <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> + 1\
  (8)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">n</span> × <span class="id"
type="var">Y</span> + <span class="id" type="var">X</span> = <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">END</span>\
  (9)    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">n</span> × <span class="id" type="var">Y</span> + <span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">X</span> \< <span class="id"
type="var">n</span> <span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Assertions (4), (5), (8), and (9) are derived mechanically from the
invariant and the loop's guard. Assertions (8), (7), and (6) are derived
using the assignment rule going backwards from (8) to (6). Assertions
(4), (3), and (2) are again backwards applications of the assignment
rule.
<div class="paragraph">

</div>

Now that we've decorated the program it only remains to check that the
two uses of the consequence rule are correct — i.e., that (1) implies
(2) and that (5) implies (6). This is indeed the case, so we have a
valid decorated program.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Finding Loop Invariants {.section}
=======================

<div class="paragraph">

</div>

Once the outermost precondition and postcondition are chosen, the only
creative part in verifying programs with Hoare Logic is finding the
right loop invariants. The reason this is difficult is the same as the
reason that doing inductive mathematical proofs requires creativity:
strengthening the loop invariant (or the induction hypothesis) means
that you have a stronger assumption to work with when trying to
establish the postcondition of the loop body (complete the induction
step of the proof), but it also means that the loop body postcondition
itself is harder to prove!
<div class="paragraph">

</div>

This section is dedicated to teaching you how to approach the challenge
of finding loop invariants using a series of examples and exercises.
<div class="paragraph">

</div>

Example: Slow Subtraction {.section}
-------------------------

<div class="paragraph">

</div>

The following program subtracts the value of <span
class="inlinecode"><span class="id" type="var">X</span></span> from the
value of <span class="inlinecode"><span class="id"
type="var">Y</span></span> by repeatedly decrementing both <span
class="inlinecode"><span class="id" type="var">X</span></span> and <span
class="inlinecode"><span class="id" type="var">Y</span></span>. We want
to verify its correctness with respect to the following specification:
<div class="paragraph">

</div>

<div class="code code-tight">

             <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> <span style="letter-spacing:-.4em;">}</span>}\
            <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ 0 <span class="id" type="var">DO</span>\
              <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> - 1;;\
              <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 1\
            <span class="id" type="var">END</span>\
              <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> - <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

To verify this program we need to find an invariant <span
class="inlinecode"><span class="id" type="var">I</span></span> for the
loop. As a first step we can leave <span class="inlinecode"><span
class="id" type="var">I</span></span> as an unknown and build a
*skeleton* for the proof by applying backward the rules for local
consistency. This process leads to the following skeleton:
<div class="paragraph">

</div>

<div class="code code-tight">

    (1)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> <span style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>     (<span class="id"
type="var">a</span>)\
     (2)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">I</span> <span
style="letter-spacing:-.4em;">}</span>}\
            <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ 0 <span class="id" type="var">DO</span>\
     (3)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">I</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> ≠ 0 <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>      (<span class="id"
type="var">c</span>)\
     (4)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">I</span>[<span class="id"
type="var">X</span> <span style="font-family: arial;">↦</span> <span
class="id" type="var">X</span>-1][<span class="id"
type="var">Y</span> <span style="font-family: arial;">↦</span> <span
class="id" type="var">Y</span>-1] <span
style="letter-spacing:-.4em;">}</span>}\
              <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> - 1;;\
     (5)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">I</span>[<span class="id"
type="var">X</span> <span style="font-family: arial;">↦</span> <span
class="id" type="var">X</span>-1] <span
style="letter-spacing:-.4em;">}</span>}\
              <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 1\
     (6)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">I</span> <span
style="letter-spacing:-.4em;">}</span>}\
            <span class="id" type="var">END</span>\
     (7)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">I</span> <span
style="font-family: arial;">∧</span> \~(<span class="id"
type="var">X</span> ≠ 0) <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>         (<span class="id"
type="var">b</span>)\
     (8)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> - <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

By examining this skeleton, we can see that any valid <span
class="inlinecode"><span class="id" type="var">I</span></span> will have
to respect three conditions:
<div class="paragraph">

</div>

-   \(a) it must be weak enough to be implied by the loop's precondition,
    i.e. (1) must imply (2);
-   \(b) it must be strong enough to imply the loop's postcondition, i.e. (7)
    must imply (8);
-   \(c) it must be preserved by one iteration of the loop, i.e. (3) must
    imply (4).

<div class="paragraph">

</div>

These conditions are actually independent of the particular program and
specification we are considering. Indeed, every loop invariant has to
satisfy them. One way to find an invariant that simultaneously satisfies
these three conditions is by using an iterative process: start with a
"candidate" invariant (e.g. a guess or a heuristic choice) and check the
three conditions above; if any of the checks fails, try to use the
information that we get from the failure to produce another (hopefully
better) candidate invariant, and repeat the process.
<div class="paragraph">

</div>

For instance, in the reduce-to-zero example above, we saw that, for a
very simple loop, choosing <span class="inlinecode"><span class="id"
type="var">True</span></span> as an invariant did the job. So let's try
it again here! I.e., let's instantiate <span class="inlinecode"><span
class="id" type="var">I</span></span> with <span
class="inlinecode"><span class="id" type="var">True</span></span> in the
skeleton above see what we get...
<div class="paragraph">

</div>

<div class="code code-tight">

    (1)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> <span style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>       (<span class="id"
type="var">a</span> - <span class="id" type="var">OK</span>)\
     (2)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>}\
            <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ 0 <span class="id" type="var">DO</span>\
     (3)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> ≠ 0 <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>    (<span class="id"
type="var">c</span> - <span class="id" type="var">OK</span>)\
     (4)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>}\
              <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> - 1;;\
     (5)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>}\
              <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 1\
     (6)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>}\
            <span class="id" type="var">END</span>\
     (7)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = 0 <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>       (<span class="id"
type="var">b</span> - <span class="id" type="var">WRONG</span>!)\
     (8)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> - <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

While conditions (a) and (c) are trivially satisfied, condition (b) is
wrong, i.e. it is not the case that (7) <span class="inlinecode"><span
class="id" type="var">True</span></span> <span class="inlinecode"><span
style="font-family: arial;">∧</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">=</span> <span class="inlinecode">0</span> implies
(8) <span class="inlinecode"><span class="id" type="var">Y</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">-</span>
<span class="inlinecode"><span class="id" type="var">m</span></span>. In
fact, the two assertions are completely unrelated and it is easy to find
a counterexample (say, <span class="inlinecode"><span class="id"
type="var">Y</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">m</span></span> <span class="inlinecode">=</span> <span
class="inlinecode">0</span> and <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">=</span>
<span class="inlinecode">1</span>).
<div class="paragraph">

</div>

If we want (b) to hold, we need to strengthen the invariant so that it
implies the postcondition (8). One very simple way to do this is to let
the invariant *be* the postcondition. So let's return to our skeleton,
instantiate <span class="inlinecode"><span class="id"
type="var">I</span></span> with <span class="inlinecode"><span
class="id" type="var">Y</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">n</span></span>
<span class="inlinecode">-</span> <span class="inlinecode"><span
class="id" type="var">m</span></span>, and check conditions (a) to (c)
again.
<div class="paragraph">

</div>

<div class="code code-tight">

    (1)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> <span style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>          (<span class="id"
type="var">a</span> - <span class="id" type="var">WRONG</span>!)\
     (2)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> - <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
            <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ 0 <span class="id" type="var">DO</span>\
     (3)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> - <span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> ≠ 0 <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>   (<span class="id"
type="var">c</span> - <span class="id" type="var">WRONG</span>!)\
     (4)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> - 1 = <span class="id"
type="var">n</span> - <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
              <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> - 1;;\
     (5)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> - <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
              <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 1\
     (6)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> - <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
            <span class="id" type="var">END</span>\
     (7)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> - <span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = 0 <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>      (<span class="id"
type="var">b</span> - <span class="id" type="var">OK</span>)\
     (8)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> - <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

This time, condition (b) holds trivially, but (a) and (c) are broken.
Condition (a) requires that (1) <span class="inlinecode"><span
class="id" type="var">X</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">m</span></span>
<span class="inlinecode"><span
style="font-family: arial;">∧</span></span> <span
class="inlinecode"><span class="id" type="var">Y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">n</span></span> implies (2) <span class="inlinecode"><span
class="id" type="var">Y</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">n</span></span>
<span class="inlinecode">-</span> <span class="inlinecode"><span
class="id" type="var">m</span></span>. If we substitute <span
class="inlinecode"><span class="id" type="var">Y</span></span> by <span
class="inlinecode"><span class="id" type="var">n</span></span> we have
to show that <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">-</span> <span class="inlinecode"><span class="id"
type="var">m</span></span> for arbitrary <span class="inlinecode"><span
class="id" type="var">m</span></span> and <span class="inlinecode"><span
class="id" type="var">n</span></span>, which does not hold (for
instance, when <span class="inlinecode"><span class="id"
type="var">m</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">n</span></span> <span
class="inlinecode">=</span> <span class="inlinecode">1</span>).
Condition (c) requires that <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode">-</span> <span
class="inlinecode"><span class="id" type="var">m</span></span> <span
class="inlinecode">-</span> <span class="inlinecode">1</span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode">-</span> <span
class="inlinecode"><span class="id" type="var">m</span></span>, which
fails, for instance, for <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode">=</span> <span
class="inlinecode">1</span> and <span class="inlinecode"><span
class="id" type="var">m</span></span> <span class="inlinecode">=</span>
<span class="inlinecode">0</span>. So, although <span
class="inlinecode"><span class="id" type="var">Y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode">-</span> <span
class="inlinecode"><span class="id" type="var">m</span></span> holds at
the end of the loop, it does not hold from the start, and it doesn't
hold on each iteration; it is not a correct invariant.
<div class="paragraph">

</div>

This failure is not very surprising: the variable <span
class="inlinecode"><span class="id" type="var">Y</span></span> changes
during the loop, while <span class="inlinecode"><span class="id"
type="var">m</span></span> and <span class="inlinecode"><span class="id"
type="var">n</span></span> are constant, so the assertion we chose
didn't have much chance of being an invariant!
<div class="paragraph">

</div>

To do better, we need to generalize (8) to some statement that is
equivalent to (8) when <span class="inlinecode"><span class="id"
type="var">X</span></span> is <span class="inlinecode">0</span>, since
this will be the case when the loop terminates, and that "fills the gap"
in some appropriate way when <span class="inlinecode"><span class="id"
type="var">X</span></span> is nonzero. Looking at how the loop works, we
can observe that <span class="inlinecode"><span class="id"
type="var">X</span></span> and <span class="inlinecode"><span class="id"
type="var">Y</span></span> are decremented together until <span
class="inlinecode"><span class="id" type="var">X</span></span> reaches
<span class="inlinecode">0</span>. So, if <span class="inlinecode"><span
class="id" type="var">X</span></span> <span class="inlinecode">=</span>
<span class="inlinecode">2</span> and <span class="inlinecode"><span
class="id" type="var">Y</span></span> <span class="inlinecode">=</span>
<span class="inlinecode">5</span> initially, after one iteration of the
loop we obtain <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode">=</span> <span
class="inlinecode">1</span> and <span class="inlinecode"><span
class="id" type="var">Y</span></span> <span class="inlinecode">=</span>
<span class="inlinecode">4</span>; after two iterations <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">=</span> <span class="inlinecode">0</span> and <span
class="inlinecode"><span class="id" type="var">Y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode">3</span>; and then
the loop stops. Notice that the difference between <span
class="inlinecode"><span class="id" type="var">Y</span></span> and <span
class="inlinecode"><span class="id" type="var">X</span></span> stays
constant between iterations; initially, <span class="inlinecode"><span
class="id" type="var">Y</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">n</span></span> and
<span class="inlinecode"><span class="id" type="var">X</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">m</span></span>, so this difference is always
<span class="inlinecode"><span class="id" type="var">n</span></span>
<span class="inlinecode">-</span> <span class="inlinecode"><span
class="id" type="var">m</span></span>. So let's try instantiating <span
class="inlinecode"><span class="id" type="var">I</span></span> in the
skeleton above with <span class="inlinecode"><span class="id"
type="var">Y</span></span> <span class="inlinecode">-</span> <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">n</span></span> <span class="inlinecode">-</span> <span
class="inlinecode"><span class="id" type="var">m</span></span>.
<div class="paragraph">

</div>

<div class="code code-tight">

    (1)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> <span style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>               (<span class="id"
type="var">a</span> - <span class="id" type="var">OK</span>)\
     (2)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> - <span class="id"
type="var">X</span> = <span class="id" type="var">n</span> - <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
            <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ 0 <span class="id" type="var">DO</span>\
     (3)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> - <span class="id"
type="var">X</span> = <span class="id" type="var">n</span> - <span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> ≠ 0 <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>    (<span class="id"
type="var">c</span> - <span class="id" type="var">OK</span>)\
     (4)        <span style="letter-spacing:-.4em;">{</span>{ (<span
class="id" type="var">Y</span> - 1) - (<span class="id"
type="var">X</span> - 1) = <span class="id" type="var">n</span> - <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
              <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> - 1;;\
     (5)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> - (<span class="id"
type="var">X</span> - 1) = <span class="id" type="var">n</span> - <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
              <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 1\
     (6)        <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> - <span class="id"
type="var">X</span> = <span class="id" type="var">n</span> - <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
            <span class="id" type="var">END</span>\
     (7)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> - <span class="id"
type="var">X</span> = <span class="id" type="var">n</span> - <span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = 0 <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>       (<span class="id"
type="var">b</span> - <span class="id" type="var">OK</span>)\
     (8)      <span style="letter-spacing:-.4em;">{</span>{ <span
class="id" type="var">Y</span> = <span class="id"
type="var">n</span> - <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Success! Conditions (a), (b) and (c) all hold now. (To verify (c), we
need to check that, under the assumption that <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">≠</span> <span class="inlinecode">0</span>, we have
<span class="inlinecode"><span class="id" type="var">Y</span></span>
<span class="inlinecode">-</span> <span class="inlinecode"><span
class="id" type="var">X</span></span> <span class="inlinecode">=</span>
<span class="inlinecode">(<span class="id" type="var">Y</span></span>
<span class="inlinecode">-</span> <span class="inlinecode">1)</span>
<span class="inlinecode">-</span> <span class="inlinecode">(<span
class="id" type="var">X</span></span> <span class="inlinecode">-</span>
<span class="inlinecode">1)</span>; this holds for all natural numbers
<span class="inlinecode"><span class="id" type="var">X</span></span> and
<span class="inlinecode"><span class="id" type="var">Y</span></span>.)

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Exercise: Slow Assignment {.section}
-------------------------

<div class="paragraph">

</div>

#### Exercise: 2 stars (slow\_assignment) {.section}

A roundabout way of assigning a number currently stored in <span
class="inlinecode"><span class="id" type="var">X</span></span> to the
variable <span class="inlinecode"><span class="id"
type="var">Y</span></span> is to start <span class="inlinecode"><span
class="id" type="var">Y</span></span> at <span
class="inlinecode">0</span>, then decrement <span
class="inlinecode"><span class="id" type="var">X</span></span> until it
hits <span class="inlinecode">0</span>, incrementing <span
class="inlinecode"><span class="id" type="var">Y</span></span> at each
step. Here is a program that implements this idea:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Y</span> ::= 0;;\
     <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ 0 <span class="id" type="var">DO</span>\
       <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 1;;\
       <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> + 1\
     <span class="id" type="var">END</span>\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Y</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

Write an informal decorated program showing that this is correct.

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

Exercise: Slow Addition {.section}
-----------------------

<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (add\_slowly\_decoration) {.section}

The following program adds the variable X into the variable Z by
repeatedly decrementing X and incrementing Z.
<div class="paragraph">

</div>

<div class="code code-tight">

  <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ 0 <span class="id" type="var">DO</span>\
      <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span> + 1;;\
      <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 1\
   <span class="id" type="var">END</span>
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Following the pattern of the <span class="inlinecode"><span class="id"
type="var">subtract\_slowly</span></span> example above, pick a
precondition and postcondition that give an appropriate specification of
<span class="inlinecode"><span class="id"
type="var">add\_slowly</span></span>; then (informally) decorate the
program accordingly.

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

Example: Parity {.section}
---------------

<div class="paragraph">

</div>

Here is a cute little program for computing the parity of the value
initially stored in <span class="inlinecode"><span class="id"
type="var">X</span></span> (due to Daniel Cristofani).
<div class="paragraph">

</div>

<div class="code code-tight">

    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">WHILE</span> 2 ≤ <span class="id"
type="var">X</span> <span class="id" type="var">DO</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 2\
   <span class="id" type="var">END</span>\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">parity</span> <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

The mathematical <span class="inlinecode"><span class="id"
type="var">parity</span></span> function used in the specification is
defined in Coq as follows:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">parity</span> <span class="id" type="var">x</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">x</span> <span class="id" type="keyword">with</span>\
   | 0 ⇒ 0\
   | 1 ⇒ 1\
   | <span class="id" type="var">S</span> (<span class="id"
type="var">S</span> <span class="id" type="var">x'</span>) ⇒ <span
class="id" type="var">parity</span> <span class="id"
type="var">x'</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

The postcondition does not hold at the beginning of the loop, since
<span class="inlinecode"><span class="id" type="var">m</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">parity</span></span> <span
class="inlinecode"><span class="id" type="var">m</span></span> does not
hold for an arbitrary <span class="inlinecode"><span class="id"
type="var">m</span></span>, so we cannot use that as an invariant. To
find an invariant that works, let's think a bit about what this loop
does. On each iteration it decrements <span class="inlinecode"><span
class="id" type="var">X</span></span> by <span
class="inlinecode">2</span>, which preserves the parity of <span
class="inlinecode"><span class="id" type="var">X</span></span>. So the
parity of <span class="inlinecode"><span class="id"
type="var">X</span></span> does not change, i.e. it is invariant. The
initial value of <span class="inlinecode"><span class="id"
type="var">X</span></span> is <span class="inlinecode"><span class="id"
type="var">m</span></span>, so the parity of <span
class="inlinecode"><span class="id" type="var">X</span></span> is always
equal to the parity of <span class="inlinecode"><span class="id"
type="var">m</span></span>. Using <span class="inlinecode"><span
class="id" type="var">parity</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">parity</span></span> <span class="inlinecode"><span
class="id" type="var">m</span></span> as an invariant we obtain the
following decorated program:
<div class="paragraph">

</div>

<div class="code code-tight">

    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>                              (<span
class="id" type="var">a</span> - <span class="id" type="var">OK</span>)\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">parity</span> <span class="id" type="var">X</span> = <span
class="id" type="var">parity</span> <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">WHILE</span> 2 ≤ <span class="id"
type="var">X</span> <span class="id" type="var">DO</span>\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">parity</span> <span class="id" type="var">X</span> = <span
class="id" type="var">parity</span> <span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> 2 ≤ <span
class="id" type="var">X</span> <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>    (<span class="id"
type="var">c</span> - <span class="id" type="var">OK</span>)\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">parity</span> (<span class="id"
type="var">X</span>-2) = <span class="id" type="var">parity</span> <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 2\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">parity</span> <span class="id" type="var">X</span> = <span
class="id" type="var">parity</span> <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">END</span>\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">parity</span> <span class="id" type="var">X</span> = <span
class="id" type="var">parity</span> <span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">X</span> \< 2 <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>       (<span class="id"
type="var">b</span> - <span class="id" type="var">OK</span>)\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">parity</span> <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

With this invariant, conditions (a), (b), and (c) are all satisfied. For
verifying (b), we observe that, when <span class="inlinecode"><span
class="id" type="var">X</span></span> <span class="inlinecode">\<</span>
<span class="inlinecode">2</span>, we have <span
class="inlinecode"><span class="id" type="var">parity</span></span>
<span class="inlinecode"><span class="id" type="var">X</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">X</span></span> (we can easily see this in the
definition of <span class="inlinecode"><span class="id"
type="var">parity</span></span>). For verifying (c), we observe that,
when <span class="inlinecode">2</span> <span class="inlinecode">≤</span>
<span class="inlinecode"><span class="id" type="var">X</span></span>, we
have <span class="inlinecode"><span class="id"
type="var">parity</span></span> <span class="inlinecode"><span
class="id" type="var">X</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">parity</span></span> <span class="inlinecode">(<span
class="id" type="var">X</span>-2)</span>.
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (parity\_formal) {.section}

Translate this proof to Coq. Refer to the reduce-to-zero example for
ideas. You may find the following two lemmas useful:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">parity\_ge\_2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>,\
   2 ≤ <span class="id" type="var">x</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">parity</span> (<span class="id"
type="var">x</span> - 2) = <span class="id" type="var">parity</span>
<span class="id" type="var">x</span>.\
<div id="proofcontrol1" class="togglescript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')">

<span class="show"></span>

</div>

<div id="proof1" class="proofscript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">x</span>; <span class="id" type="tactic">intro</span>. <span
class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">x</span>. <span class="id" type="tactic">inversion</span>
<span class="id" type="var">H</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H1</span>.\
   <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">minus\_n\_O</span>. <span class="id"
type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">parity\_lt\_2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">x</span>,\
   ¬ 2 ≤ <span class="id" type="var">x</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">parity</span> (<span class="id"
type="var">x</span>) = <span class="id" type="var">x</span>.\
<div id="proofcontrol2" class="togglescript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')">

<span class="show"></span>

</div>

<div id="proof2" class="proofscript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">x</span>.
<span class="id" type="tactic">reflexivity</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">x</span>.
<span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ex\_falso\_quodlibet</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">omega</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">parity\_correct</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">m</span>,\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> =
<span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">BLe</span> (<span class="id" type="var">ANum</span> 2) (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
<span class="id" type="var">DO</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
2)\
   <span class="id" type="var">END</span>\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> =
<span class="id" type="var">parity</span> <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}.\
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

Example: Finding Square Roots {.section}
-----------------------------

<div class="paragraph">

</div>

The following program computes the square root of <span
class="inlinecode"><span class="id" type="var">X</span></span> by naive
iteration:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span>=<span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Z</span> ::= 0;;\
     <span class="id" type="var">WHILE</span> (<span class="id"
type="var">Z</span>+1)\*(<span class="id" type="var">Z</span>+1) ≤ <span
class="id" type="var">X</span> <span class="id" type="var">DO</span>\
       <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span>+1\
     <span class="id" type="var">END</span>\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span>×<span class="id" type="var">Z</span>≤<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">m</span>\<(<span class="id" type="var">Z</span>+1)\*(<span
class="id" type="var">Z</span>+1) <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

As above, we can try to use the postcondition as a candidate invariant,
obtaining the following decorated program:
<div class="paragraph">

</div>

<div class="code code-tight">

 (1)  <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span>=<span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>           (<span class="id"
type="var">a</span> - <span class="id" type="var">second</span> <span
class="id" type="var">conjunct</span> <span class="id"
type="var">of</span> (2) <span class="id" type="var">WRONG</span>!)\
  (2)  <span style="letter-spacing:-.4em;">{</span>{ 0×0 ≤ <span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">m</span>\<1×1 <span style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Z</span> ::= 0;;\
  (3)  <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span>×<span class="id" type="var">Z</span> ≤ <span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">m</span>\<(<span class="id" type="var">Z</span>+1)\*(<span
class="id" type="var">Z</span>+1) <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">WHILE</span> (<span class="id"
type="var">Z</span>+1)\*(<span class="id" type="var">Z</span>+1) ≤ <span
class="id" type="var">X</span> <span class="id" type="var">DO</span>\
  (4)    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span>×<span class="id" type="var">Z</span>≤<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> (<span class="id"
type="var">Z</span>+1)\*(<span class="id" type="var">Z</span>+1)≤<span
class="id" type="var">X</span> <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>           (<span class="id"
type="var">c</span> - <span class="id" type="var">WRONG</span>!)\
  (5)    <span style="letter-spacing:-.4em;">{</span>{ (<span class="id"
type="var">Z</span>+1)\*(<span class="id" type="var">Z</span>+1)≤<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">m</span>\<(<span class="id" type="var">Z</span>+2)\*(<span
class="id" type="var">Z</span>+2) <span
style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span>+1\
  (6)    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span>×<span class="id" type="var">Z</span>≤<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">m</span>\<(<span class="id" type="var">Z</span>+1)\*(<span
class="id" type="var">Z</span>+1) <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">END</span>\
  (7)  <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span>×<span class="id" type="var">Z</span>≤<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">m</span>\<(<span class="id" type="var">Z</span>+1)\*(<span
class="id" type="var">Z</span>+1) <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span>\<(<span class="id" type="var">Z</span>+1)\*(<span
class="id" type="var">Z</span>+1) <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span> (<span class="id"
type="var">b</span> - <span class="id" type="var">OK</span>)\
  (8)  <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span>×<span class="id" type="var">Z</span>≤<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">m</span>\<(<span class="id" type="var">Z</span>+1)\*(<span
class="id" type="var">Z</span>+1) <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

This didn't work very well: both conditions (a) and (c) failed. Looking
at condition (c), we see that the second conjunct of (4) is almost the
same as the first conjunct of (5), except that (4) mentions <span
class="inlinecode"><span class="id" type="var">X</span></span> while (5)
mentions <span class="inlinecode"><span class="id"
type="var">m</span></span>. But note that <span class="inlinecode"><span
class="id" type="var">X</span></span> is never assigned in this program,
so we should have <span class="inlinecode"><span class="id"
type="var">X</span>=<span class="id" type="var">m</span></span>, but we
didn't propagate this information from (1) into the loop invariant.
<div class="paragraph">

</div>

Also, looking at the second conjunct of (8), it seems quite hopeless as
an invariant — and we don't even need it, since we can obtain it from
the negation of the guard (third conjunct in (7)), again under the
assumption that <span class="inlinecode"><span class="id"
type="var">X</span>=<span class="id" type="var">m</span></span>.
<div class="paragraph">

</div>

So we now try <span class="inlinecode"><span class="id"
type="var">X</span>=<span class="id" type="var">m</span></span> <span
class="inlinecode"><span style="font-family: arial;">∧</span></span>
<span class="inlinecode"><span class="id" type="var">Z</span>×<span
class="id" type="var">Z</span></span> <span class="inlinecode">≤</span>
<span class="inlinecode"><span class="id" type="var">m</span></span> as
the loop invariant:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span>=<span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>                                      (<span
class="id" type="var">a</span> - <span class="id" type="var">OK</span>)\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span>=<span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> 0×0 ≤ <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Z</span> ::= 0;\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span>=<span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Z</span>×<span class="id" type="var">Z</span> ≤ <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">WHILE</span> (<span class="id"
type="var">Z</span>+1)\*(<span class="id" type="var">Z</span>+1) ≤ <span
class="id" type="var">X</span> <span class="id" type="var">DO</span>\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span>=<span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Z</span>×<span class="id" type="var">Z</span>≤<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> (<span class="id"
type="var">Z</span>+1)\*(<span class="id" type="var">Z</span>+1)≤<span
class="id" type="var">X</span> <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>        (<span class="id"
type="var">c</span> - <span class="id" type="var">OK</span>)\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span>=<span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> (<span class="id"
type="var">Z</span>+1)\*(<span class="id" type="var">Z</span>+1)≤<span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span>+1\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span>=<span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Z</span>×<span class="id" type="var">Z</span>≤<span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">END</span>\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span>=<span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Z</span>×<span class="id" type="var">Z</span>≤<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span>\<(<span class="id" type="var">Z</span>+1)\*(<span
class="id" type="var">Z</span>+1) <span
style="letter-spacing:-.4em;">}</span>}  <span
style="font-family: arial;">⇾</span>           (<span class="id"
type="var">b</span> - <span class="id" type="var">OK</span>)\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span>×<span class="id" type="var">Z</span>≤<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">m</span>\<(<span class="id" type="var">Z</span>+1)\*(<span
class="id" type="var">Z</span>+1) <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

This works, since conditions (a), (b), and (c) are now all trivially
satisfied.
<div class="paragraph">

</div>

Very often, if a variable is used in a loop in a read-only fashion
(i.e., it is referred to by the program or by the specification and it
is not changed by the loop) it is necessary to add the fact that it
doesn't change to the loop invariant.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Example: Squaring {.section}
-----------------

<div class="paragraph">

</div>

Here is a program that squares <span class="inlinecode"><span class="id"
type="var">X</span></span> by repeated addition:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">Y</span> ::= 0;;\
   <span class="id" type="var">Z</span> ::= 0;;\
   <span class="id" type="var">WHILE</span>  <span class="id"
type="var">Y</span>  ≠  <span class="id" type="var">X</span>  <span
class="id" type="var">DO</span>\
     <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span> + <span class="id" type="var">X</span>;;\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> + 1\
   <span class="id" type="var">END</span>\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">m</span>×<span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

The first thing to note is that the loop reads <span
class="inlinecode"><span class="id" type="var">X</span></span> but
doesn't change its value. As we saw in the previous example, in such
cases it is a good idea to add <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">m</span></span> to the
invariant. The other thing we often use in the invariant is the
postcondition, so let's add that too, leading to the invariant candidate
<span class="inlinecode"><span class="id" type="var">Z</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">m</span></span> <span class="inlinecode">×</span>
<span class="inlinecode"><span class="id" type="var">m</span></span>
<span class="inlinecode"><span
style="font-family: arial;">∧</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">m</span></span>.
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>                            (<span
class="id" type="var">a</span> - <span class="id"
type="var">WRONG</span>)\
       <span style="letter-spacing:-.4em;">{</span>{ 0 = <span
class="id" type="var">m</span>×<span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Y</span> ::= 0;;\
       <span style="letter-spacing:-.4em;">{</span>{ 0 = <span
class="id" type="var">m</span>×<span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Z</span> ::= 0;;\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">m</span>×<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">WHILE</span> <span class="id"
type="var">Y</span> ≠ <span class="id" type="var">X</span> <span
class="id" type="var">DO</span>\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">Y</span>×<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Y</span> ≠ <span class="id" type="var">X</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>     (<span class="id"
type="var">c</span> - <span class="id" type="var">WRONG</span>)\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span>+<span class="id" type="var">X</span> = <span
class="id" type="var">m</span>×<span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span> + <span class="id" type="var">X</span>;;\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">m</span>×<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> + 1\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">m</span>×<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">END</span>\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">m</span>×<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Y</span> = <span class="id" type="var">X</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>         (<span class="id"
type="var">b</span> - <span class="id" type="var">OK</span>)\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">m</span>×<span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Conditions (a) and (c) fail because of the <span
class="inlinecode"><span class="id" type="var">Z</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">m</span>×<span class="id" type="var">m</span></span> part.
While <span class="inlinecode"><span class="id"
type="var">Z</span></span> starts at <span class="inlinecode">0</span>
and works itself up to <span class="inlinecode"><span class="id"
type="var">m</span>×<span class="id" type="var">m</span></span>, we
can't expect <span class="inlinecode"><span class="id"
type="var">Z</span></span> to be <span class="inlinecode"><span
class="id" type="var">m</span>×<span class="id"
type="var">m</span></span> from the start. If we look at how <span
class="inlinecode"><span class="id" type="var">Z</span></span> progesses
in the loop, after the 1st iteration <span class="inlinecode"><span
class="id" type="var">Z</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">m</span></span>,
after the 2nd iteration <span class="inlinecode"><span class="id"
type="var">Z</span></span> <span class="inlinecode">=</span> <span
class="inlinecode">2×<span class="id" type="var">m</span></span>, and at
the end <span class="inlinecode"><span class="id"
type="var">Z</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">m</span>×<span class="id"
type="var">m</span></span>. Since the variable <span
class="inlinecode"><span class="id" type="var">Y</span></span> tracks
how many times we go through the loop, we derive the new invariant
candidate <span class="inlinecode"><span class="id"
type="var">Z</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">Y</span>×<span class="id"
type="var">m</span></span> <span class="inlinecode"><span
style="font-family: arial;">∧</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">m</span></span>.
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>                               (<span
class="id" type="var">a</span> - <span class="id" type="var">OK</span>)\
       <span style="letter-spacing:-.4em;">{</span>{ 0 = 0×<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Y</span> ::= 0;;\
       <span style="letter-spacing:-.4em;">{</span>{ 0 = <span
class="id" type="var">Y</span>×<span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Z</span> ::= 0;;\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">Y</span>×<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">WHILE</span> <span class="id"
type="var">Y</span> ≠ <span class="id" type="var">X</span> <span
class="id" type="var">DO</span>\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">Y</span>×<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Y</span> ≠ <span class="id" type="var">X</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>        (<span class="id"
type="var">c</span> - <span class="id" type="var">OK</span>)\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span>+<span class="id" type="var">X</span> = (<span
class="id" type="var">Y</span>+1)×<span class="id"
type="var">m</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">X</span> = <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span> + <span class="id" type="var">X</span>;\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = (<span class="id" type="var">Y</span>+1)×<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
       <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> + 1\
         <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">Y</span>×<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">END</span>\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">Y</span>×<span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Y</span> = <span class="id" type="var">X</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>           (<span class="id"
type="var">b</span> - <span class="id" type="var">OK</span>)\
       <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">m</span>×<span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

This new invariant makes the proof go through: all three conditions are
easy to check.
<div class="paragraph">

</div>

It is worth comparing the postcondition <span class="inlinecode"><span
class="id" type="var">Z</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">m</span>×<span
class="id" type="var">m</span></span> and the <span
class="inlinecode"><span class="id" type="var">Z</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">Y</span>×<span class="id" type="var">m</span></span> conjunct
of the invariant. It is often the case that one has to replace auxiliary
variabes (parameters) with variables — or with expressions involving
both variables and parameters (like <span class="inlinecode"><span
class="id" type="var">m</span></span> <span class="inlinecode">-</span>
<span class="inlinecode"><span class="id" type="var">Y</span></span>) —
when going from postconditions to invariants.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Exercise: Factorial {.section}
-------------------

<div class="paragraph">

</div>

#### Exercise: 3 stars (factorial) {.section}

Recall that <span class="inlinecode"><span class="id"
type="var">n</span>!</span> denotes the factorial of <span
class="inlinecode"><span class="id" type="var">n</span></span> (i.e.
<span class="inlinecode"><span class="id" type="var">n</span>!</span>
<span class="inlinecode">=</span> <span class="inlinecode">1×2×...×<span
class="id" type="var">n</span></span>). Here is an Imp program that
calculates the factorial of the number initially stored in the variable
<span class="inlinecode"><span class="id" type="var">X</span></span> and
puts it in the variable <span class="inlinecode"><span class="id"
type="var">Y</span></span>:
<div class="paragraph">

</div>

<div class="code code-tight">

    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>} \
   <span class="id" type="var">Y</span> ::= 1 ;;\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ 0\
   <span class="id" type="var">DO</span>\
      <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> × <span class="id" type="var">X</span> ;;\
      <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 1\
   <span class="id" type="var">END</span>\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Y</span> = <span class="id" type="var">m</span>! <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Fill in the blanks in following decorated program:
<div class="paragraph">

</div>

<div class="code code-tight">

    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
     <span
style="letter-spacing:-.4em;">{</span>{                                      <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">Y</span> ::= 1;;\
     <span
style="letter-spacing:-.4em;">{</span>{                                      <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ 0\
   <span class="id" type="var">DO</span>   <span
style="letter-spacing:-.4em;">{</span>{                                      <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
        <span
style="letter-spacing:-.4em;">{</span>{                                      <span
style="letter-spacing:-.4em;">}</span>}\
      <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> × <span class="id" type="var">X</span>;;\
        <span
style="letter-spacing:-.4em;">{</span>{                                      <span
style="letter-spacing:-.4em;">}</span>}\
      <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> - 1\
        <span
style="letter-spacing:-.4em;">{</span>{                                      <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">END</span>\
     <span
style="letter-spacing:-.4em;">{</span>{                                      <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Y</span> = <span class="id" type="var">m</span>! <span
style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Exercise: Min {.section}
-------------

<div class="paragraph">

</div>

#### Exercise: 3 stars (Min\_Hoare) {.section}

Fill in valid decorations for the following program. For the =\> steps
in your annotations, you may rely (silently) on the following facts
about min
<div class="paragraph">

</div>

Lemma lemma1 : forall x y, (x=0 λ/ y=0) -\> min x y = 0. Lemma lemma2 :
forall x y, min (x-1) (y-1) = (min x y) - 1.
<div class="paragraph">

</div>

plus, as usual, standard high-school algebra.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

  <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
   <span
style="letter-spacing:-.4em;">{</span>{                    <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">X</span> ::= <span class="id"
type="var">a</span>;;\
   <span
style="letter-spacing:-.4em;">{</span>{                       <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">Y</span> ::= <span class="id"
type="var">b</span>;;\
   <span
style="letter-spacing:-.4em;">{</span>{                       <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">Z</span> ::= 0;;\
   <span
style="letter-spacing:-.4em;">{</span>{                       <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">WHILE</span> (<span class="id"
type="var">X</span> ≠ 0 <span style="font-family: arial;">∧</span> <span
class="id" type="var">Y</span> ≠ 0) <span class="id"
type="var">DO</span>\
   <span
style="letter-spacing:-.4em;">{</span>{                                     <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
   <span
style="letter-spacing:-.4em;">{</span>{                                <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">X</span> := <span class="id"
type="var">X</span> - 1;;\
   <span
style="letter-spacing:-.4em;">{</span>{                            <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">Y</span> := <span class="id"
type="var">Y</span> - 1;;\
   <span
style="letter-spacing:-.4em;">{</span>{                        <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">Z</span> := <span class="id"
type="var">Z</span> + 1\
   <span
style="letter-spacing:-.4em;">{</span>{                       <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">END</span>\
   <span
style="letter-spacing:-.4em;">{</span>{                            <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
   <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">min</span> <span
class="id" type="var">a</span> <span class="id"
type="var">b</span> <span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (two\_loops) {.section}

Here is a very inefficient way of adding 3 numbers:
<div class="paragraph">

</div>

<div class="code code-tight">

  <span class="id" type="var">X</span> ::= 0;;\
   <span class="id" type="var">Y</span> ::= 0;;\
   <span class="id" type="var">Z</span> ::= <span class="id"
type="var">c</span>;;\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ <span class="id" type="var">a</span> <span
class="id" type="var">DO</span>\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> + 1;;\
     <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span> + 1\
   <span class="id" type="var">END</span>;;\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">Y</span> ≠ <span class="id" type="var">b</span> <span
class="id" type="var">DO</span>\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> + 1;;\
     <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span> + 1\
   <span class="id" type="var">END</span>
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Show that it does what it should by filling in the blanks in the
following decorated program.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

    <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
     <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">X</span> ::= 0;;\
     <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">Y</span> ::= 0;;\
     <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">Z</span> ::= <span class="id"
type="var">c</span>;;\
     <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ <span class="id" type="var">a</span> <span
class="id" type="var">DO</span>\
       <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
       <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> + 1;;\
       <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span> + 1\
       <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">END</span>;;\
     <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
     <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">Y</span> ≠ <span class="id" type="var">b</span> <span
class="id" type="var">DO</span>\
       <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
       <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> + 1;;\
       <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">Z</span> ::= <span class="id"
type="var">Z</span> + 1\
       <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">END</span>\
     <span
style="letter-spacing:-.4em;">{</span>{                                        <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Z</span> = <span class="id" type="var">a</span> + <span
class="id" type="var">b</span> + <span class="id"
type="var">c</span> <span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Exercise: Power Series {.section}
----------------------

<div class="paragraph">

</div>

#### Exercise: 4 stars, optional (dpow2\_down) {.section}

Here is a program that computes the series: <span
class="inlinecode">1</span> <span class="inlinecode">+</span> <span
class="inlinecode">2</span> <span class="inlinecode">+</span> <span
class="inlinecode">2\^2</span> <span class="inlinecode">+</span> <span
class="inlinecode">...</span> <span class="inlinecode">+</span> <span
class="inlinecode">2\^<span class="id" type="var">m</span></span> <span
class="inlinecode">=</span> <span class="inlinecode">2\^(<span
class="id" type="var">m</span>+1)</span> <span
class="inlinecode">-</span> <span class="inlinecode">1</span>
<div class="paragraph">

</div>

<div class="code code-tight">

  <span class="id" type="var">X</span> ::= 0;;\
   <span class="id" type="var">Y</span> ::= 1;;\
   <span class="id" type="var">Z</span> ::= 1;;\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">X</span> ≠ <span class="id" type="var">m</span> <span
class="id" type="var">DO</span>\
     <span class="id" type="var">Z</span> ::= 2 × <span class="id"
type="var">Z</span>;;\
     <span class="id" type="var">Y</span> ::= <span class="id"
type="var">Y</span> + <span class="id" type="var">Z</span>;;\
     <span class="id" type="var">X</span> ::= <span class="id"
type="var">X</span> + 1\
   <span class="id" type="var">END</span>
<div class="paragraph">

</div>

</div>

Write a decorated program for this.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\
\

</div>

<div class="doc">

Weakest Preconditions (Advanced) {.section}
================================

<div class="paragraph">

</div>

Some Hoare triples are more interesting than others. For example,
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">False</span> <span
style="letter-spacing:-.4em;">}</span>}  <span class="id"
type="var">X</span> ::= <span class="id" type="var">Y</span> + 1  <span
style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> ≤ 5 <span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

is *not* very interesting: although it is perfectly valid, it tells us
nothing useful. Since the precondition isn't satisfied by any state, it
doesn't describe any situations where we can use the command <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">::=</span> <span class="inlinecode"><span class="id"
type="var">Y</span></span> <span class="inlinecode">+</span> <span
class="inlinecode">1</span> to achieve the postcondition <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode">≤</span> <span class="inlinecode">5</span>.
<div class="paragraph">

</div>

By contrast,
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Y</span> ≤ 4 <span style="font-family: arial;">∧</span> <span
class="id" type="var">Z</span> = 0 <span
style="letter-spacing:-.4em;">}</span>}  <span class="id"
type="var">X</span> ::= <span class="id" type="var">Y</span> + 1 <span
style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> ≤ 5 <span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

is useful: it tells us that, if we can somehow create a situation in
which we know that <span class="inlinecode"><span class="id"
type="var">Y</span></span> <span class="inlinecode">≤</span> <span
class="inlinecode">4</span> <span class="inlinecode"><span
style="font-family: arial;">∧</span></span> <span
class="inlinecode"><span class="id" type="var">Z</span></span> <span
class="inlinecode">=</span> <span class="inlinecode">0</span>, then
running this command will produce a state satisfying the postcondition.
However, this triple is still not as useful as it could be, because the
<span class="inlinecode"><span class="id" type="var">Z</span></span>
<span class="inlinecode">=</span> <span class="inlinecode">0</span>
clause in the precondition actually has nothing to do with the
postcondition <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode">≤</span> <span
class="inlinecode">5</span>. The *most* useful triple (for a given
command and postcondition) is this one:
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Y</span> ≤ 4 <span
style="letter-spacing:-.4em;">}</span>}  <span class="id"
type="var">X</span> ::= <span class="id" type="var">Y</span> + 1  <span
style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> ≤ 5 <span style="letter-spacing:-.4em;">}</span>}
<div class="paragraph">

</div>

</div>

In other words, <span class="inlinecode"><span class="id"
type="var">Y</span></span> <span class="inlinecode">≤</span> <span
class="inlinecode">4</span> is the *weakest* valid precondition of the
command <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode">::=</span> <span
class="inlinecode"><span class="id" type="var">Y</span></span> <span
class="inlinecode">+</span> <span class="inlinecode">1</span> for the
postcondition <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode">≤</span> <span
class="inlinecode">5</span>.
<div class="paragraph">

</div>

In general, we say that "<span class="inlinecode"><span class="id"
type="var">P</span></span> is the weakest precondition of command <span
class="inlinecode"><span class="id" type="var">c</span></span> for
postcondition <span class="inlinecode"><span class="id"
type="var">Q</span></span>" if <span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>}</span>
<span class="inlinecode"><span class="id" type="var">c</span></span>
<span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}</span>
and if, whenever <span class="inlinecode"><span class="id"
type="var">P'</span></span> is an assertion such that <span
class="inlinecode"><span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">P'</span><span
style="letter-spacing:-.4em;">}</span>}</span> <span
class="inlinecode"><span class="id" type="var">c</span></span> <span
class="inlinecode"><span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">Q</span><span
style="letter-spacing:-.4em;">}</span>}</span>, we have <span
class="inlinecode"><span class="id" type="var">P'</span></span> <span
class="inlinecode"><span class="id" type="var">st</span></span> implies
<span class="inlinecode"><span class="id" type="var">P</span></span>
<span class="inlinecode"><span class="id" type="var">st</span></span>
for all states <span class="inlinecode"><span class="id"
type="var">st</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">is\_wp</span> <span class="id" type="var">P</span> <span
class="id" type="var">c</span> <span class="id" type="var">Q</span> :=\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">∧</span>\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">P'</span>, <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">P'</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">c</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">Q</span><span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">→</span> (<span class="id"
type="var">P'</span> <span style="font-family: arial;">⇾</span> <span
class="id" type="var">P</span>).\
\

</div>

<div class="doc">

That is, <span class="inlinecode"><span class="id"
type="var">P</span></span> is the weakest precondition of <span
class="inlinecode"><span class="id" type="var">c</span></span> for <span
class="inlinecode"><span class="id" type="var">Q</span></span> if (a)
<span class="inlinecode"><span class="id" type="var">P</span></span>
*is* a precondition for <span class="inlinecode"><span class="id"
type="var">Q</span></span> and <span class="inlinecode"><span class="id"
type="var">c</span></span>, and (b) <span class="inlinecode"><span
class="id" type="var">P</span></span> is the *weakest* (easiest to
satisfy) assertion that guarantees <span class="inlinecode"><span
class="id" type="var">Q</span></span> after executing <span
class="inlinecode"><span class="id" type="var">c</span></span>.
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (wp) {.section}

What are the weakest preconditions of the following commands for the
following postconditions?
<div class="paragraph">

</div>

<div class="code code-tight">

  1) <span style="letter-spacing:-.4em;">{</span>{ ? <span
style="letter-spacing:-.4em;">}</span>}  <span class="id"
type="var">SKIP</span>  <span
style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = 5 <span style="letter-spacing:-.4em;">}</span>}\
\
   2) <span style="letter-spacing:-.4em;">{</span>{ ? <span
style="letter-spacing:-.4em;">}</span>}  <span class="id"
type="var">X</span> ::= <span class="id" type="var">Y</span> + <span
class="id" type="var">Z</span> <span
style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = 5 <span style="letter-spacing:-.4em;">}</span>}\
\
   3) <span style="letter-spacing:-.4em;">{</span>{ ? <span
style="letter-spacing:-.4em;">}</span>}  <span class="id"
type="var">X</span> ::= <span class="id" type="var">Y</span>  <span
style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = <span class="id" type="var">Y</span> <span
style="letter-spacing:-.4em;">}</span>}\
\
   4) <span style="letter-spacing:-.4em;">{</span>{ ? <span
style="letter-spacing:-.4em;">}</span>}\
      <span class="id" type="var">IFB</span> <span class="id"
type="var">X</span> == 0 <span class="id" type="var">THEN</span> <span
class="id" type="var">Y</span> ::= <span class="id"
type="var">Z</span> + 1 <span class="id" type="var">ELSE</span> <span
class="id" type="var">Y</span> ::= <span class="id"
type="var">W</span> + 2 <span class="id" type="var">FI</span>\
      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Y</span> = 5 <span style="letter-spacing:-.4em;">}</span>}\
\
   5) <span style="letter-spacing:-.4em;">{</span>{ ? <span
style="letter-spacing:-.4em;">}</span>}\
      <span class="id" type="var">X</span> ::= 5\
      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = 0 <span style="letter-spacing:-.4em;">}</span>}\
\
   6) <span style="letter-spacing:-.4em;">{</span>{ ? <span
style="letter-spacing:-.4em;">}</span>}\
      <span class="id" type="var">WHILE</span> <span class="id"
type="var">True</span> <span class="id" type="var">DO</span> <span
class="id" type="var">X</span> ::= 0 <span class="id"
type="var">END</span>\
      <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">X</span> = 0 <span style="letter-spacing:-.4em;">}</span>}
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

#### Exercise: 3 stars, advanced, optional (is\_wp\_formal) {.section}

Prove formally using the definition of <span class="inlinecode"><span
class="id" type="var">hoare\_triple</span></span> that <span
class="inlinecode"><span class="id" type="var">Y</span></span> <span
class="inlinecode">≤</span> <span class="inlinecode">4</span> is indeed
the weakest precondition of <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode">::=</span> <span
class="inlinecode"><span class="id" type="var">Y</span></span> <span
class="inlinecode">+</span> <span class="inlinecode">1</span> with
respect to postcondition <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode">≤</span> <span
class="inlinecode">5</span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">is\_wp\_example</span> :\
   <span class="id" type="var">is\_wp</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">Y</span> ≤
4)\
     (<span class="id" type="var">X</span> ::= <span class="id"
type="var">APlus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">Y</span>) (<span class="id" type="var">ANum</span>
1)) (<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">st</span> <span
class="id" type="var">X</span> ≤ 5).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, advanced (hoare\_asgn\_weakest) {.section}

Show that the precondition in the rule <span class="inlinecode"><span
class="id" type="var">hoare\_asgn</span></span> is in fact the weakest
precondition.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_asgn\_weakest</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">Q</span>
<span class="id" type="var">X</span> <span class="id"
type="var">a</span>,\
   <span class="id" type="var">is\_wp</span> (<span class="id"
type="var">Q</span> [<span class="id" type="var">X</span> <span
style="font-family: arial;">↦</span> <span class="id"
type="var">a</span>]) (<span class="id" type="var">X</span> ::= <span
class="id" type="var">a</span>) <span class="id" type="var">Q</span>.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, advanced, optional (hoare\_havoc\_weakest) {.section}

Show that your <span class="inlinecode"><span class="id"
type="var">havoc\_pre</span></span> rule from the <span
class="inlinecode"><span class="id" type="var">himp\_hoare</span></span>
exercise in the <span class="inlinecode"><span class="id"
type="var">Hoare</span></span> chapter returns the weakest precondition.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">hoare\_havoc\_weakest</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> : <span
class="id" type="var">Assertion</span>) (<span class="id"
type="var">X</span> : <span class="id" type="var">id</span>),\
   <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">P</span> <span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">HAVOC</span> <span class="id" type="var">X</span>
<span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="var">Q</span> <span style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">havoc\_pre</span> <span class="id" type="var">X</span> <span
class="id" type="var">Q</span>.\
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

Formal Decorated Programs (Advanced) {.section}
====================================

<div class="paragraph">

</div>

The informal conventions for decorated programs amount to a way of
displaying Hoare triples in which commands are annotated with enough
embedded assertions that checking the validity of the triple is reduced
to simple logical and algebraic calculations showing that some
assertions imply others. In this section, we show that this informal
presentation style can actually be made completely formal and indeed
that checking the validity of decorated programs can mostly be
automated.
<div class="paragraph">

</div>

Syntax {.section}
------

<div class="paragraph">

</div>

The first thing we need to do is to formalize a variant of the syntax of
commands with embedded assertions. We call the new commands *decorated
commands*, or <span class="inlinecode"><span class="id"
type="var">dcom</span></span>s.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">dcom</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">DCSkip</span> : <span class="id"
type="var">Assertion</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">dcom</span>\
   | <span class="id" type="var">DCSeq</span> : <span class="id"
type="var">dcom</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">dcom</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">dcom</span>\
   | <span class="id" type="var">DCAsgn</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">aexp</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Assertion</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">dcom</span>\
   | <span class="id" type="var">DCIf</span> : <span class="id"
type="var">bexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Assertion</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">dcom</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Assertion</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">dcom</span>\
            <span style="font-family: arial;">→</span> <span class="id"
type="var">Assertion</span><span style="font-family: arial;">→</span>
<span class="id" type="var">dcom</span>\
   | <span class="id" type="var">DCWhile</span> : <span class="id"
type="var">bexp</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Assertion</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">dcom</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Assertion</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">dcom</span>\
   | <span class="id" type="var">DCPre</span> : <span class="id"
type="var">Assertion</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">dcom</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">dcom</span>\
   | <span class="id" type="var">DCPost</span> : <span class="id"
type="var">dcom</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Assertion</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">dcom</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span> "dcom\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "Skip" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "Seq" |
<span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "Asgn"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "If" | <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">c</span> "While"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "Pre" | <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">c</span> "Post" ].\
\
 <span class="id" type="keyword">Notation</span> "'SKIP' <span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>}"\
       := (<span class="id" type="var">DCSkip</span> <span class="id"
type="var">P</span>)\
       (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 10) : <span class="id"
type="var">dcom\_scope</span>.\
 <span class="id" type="keyword">Notation</span> "l '::=' a <span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>}"\
       := (<span class="id" type="var">DCAsgn</span> <span class="id"
type="var">l</span> <span class="id" type="var">a</span> <span
class="id" type="var">P</span>)\
       (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 60, <span class="id" type="var">a</span> <span
class="id" type="tactic">at</span> <span class="id"
type="var">next</span> <span class="id" type="var">level</span>) : <span
class="id" type="var">dcom\_scope</span>.\
 <span class="id" type="keyword">Notation</span> "'WHILE' b 'DO' <span
style="letter-spacing:-.4em;">{</span>{ Pbody <span
style="letter-spacing:-.4em;">}</span>} d 'END' <span
style="letter-spacing:-.4em;">{</span>{ Ppost <span
style="letter-spacing:-.4em;">}</span>}"\
       := (<span class="id" type="var">DCWhile</span> <span class="id"
type="var">b</span> <span class="id" type="var">Pbody</span> <span
class="id" type="var">d</span> <span class="id"
type="var">Ppost</span>)\
       (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 80, <span class="id" type="var">right</span>
<span class="id" type="var">associativity</span>) : <span class="id"
type="var">dcom\_scope</span>.\
 <span class="id" type="keyword">Notation</span> "'IFB' b 'THEN' <span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} d 'ELSE' <span
style="letter-spacing:-.4em;">{</span>{ P' <span
style="letter-spacing:-.4em;">}</span>} d' 'FI' <span
style="letter-spacing:-.4em;">{</span>{ Q <span
style="letter-spacing:-.4em;">}</span>}"\
       := (<span class="id" type="var">DCIf</span> <span class="id"
type="var">b</span> <span class="id" type="var">P</span> <span
class="id" type="var">d</span> <span class="id" type="var">P'</span>
<span class="id" type="var">d'</span> <span class="id"
type="var">Q</span>)\
       (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 80, <span class="id" type="var">right</span>
<span class="id" type="var">associativity</span>) : <span class="id"
type="var">dcom\_scope</span>.\
 <span class="id" type="keyword">Notation</span> "'<span
style="font-family: arial;">⇾</span>' <span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} d"\
       := (<span class="id" type="var">DCPre</span> <span class="id"
type="var">P</span> <span class="id" type="var">d</span>)\
       (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 90, <span class="id" type="var">right</span>
<span class="id" type="var">associativity</span>) : <span class="id"
type="var">dcom\_scope</span>.\
 <span class="id" type="keyword">Notation</span> "<span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>} d"\
       := (<span class="id" type="var">DCPre</span> <span class="id"
type="var">P</span> <span class="id" type="var">d</span>)\
       (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 90) : <span class="id"
type="var">dcom\_scope</span>.\
 <span class="id" type="keyword">Notation</span> "d '<span
style="font-family: arial;">⇾</span>' <span
style="letter-spacing:-.4em;">{</span>{ P <span
style="letter-spacing:-.4em;">}</span>}"\
       := (<span class="id" type="var">DCPost</span> <span class="id"
type="var">d</span> <span class="id" type="var">P</span>)\
       (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 80, <span class="id" type="var">right</span>
<span class="id" type="var">associativity</span>) : <span class="id"
type="var">dcom\_scope</span>.\
 <span class="id" type="keyword">Notation</span> " d ;; d' "\
       := (<span class="id" type="var">DCSeq</span> <span class="id"
type="var">d</span> <span class="id" type="var">d'</span>)\
       (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 80, <span class="id" type="var">right</span>
<span class="id" type="var">associativity</span>) : <span class="id"
type="var">dcom\_scope</span>.\
\
 <span class="id" type="keyword">Delimit</span> <span class="id"
type="keyword">Scope</span> <span class="id"
type="var">dcom\_scope</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">dcom</span>.\
\

</div>

<div class="doc">

To avoid clashing with the existing <span class="inlinecode"><span
class="id" type="keyword">Notation</span></span> definitions for
ordinary <span class="inlinecode"><span class="id"
type="var">com</span></span>mands, we introduce these notations in a
special scope called <span class="inlinecode"><span class="id"
type="var">dcom\_scope</span></span>, and we wrap examples with the
declaration <span class="inlinecode">%</span> <span
class="inlinecode"><span class="id" type="var">dcom</span></span> to
signal that we want the notations to be interpreted in this scope.
<div class="paragraph">

</div>

Careful readers will note that we've defined two notations for the <span
class="inlinecode"><span class="id" type="var">DCPre</span></span>
constructor, one with and one without a <span class="inlinecode"><span
style="font-family: arial;">⇾</span></span>. The "without" version is
intended to be used to supply the initial precondition at the very top
of the program.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">dec\_while</span> : <span class="id" type="var">dcom</span>
:= (\
   <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">WHILE</span> (<span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 0)))\
   <span class="id" type="var">DO</span>\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> ≠ 0<span
style="letter-spacing:-.4em;">}</span>}\
     <span class="id" type="var">X</span> ::= (<span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1))\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">\_</span> ⇒ <span
class="id" type="var">True</span> <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">END</span>\
   <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> = 0<span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
   <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> = 0
<span style="letter-spacing:-.4em;">}</span>}\
 ) % <span class="id" type="var">dcom</span>.\
\

</div>

<div class="doc">

It is easy to go from a <span class="inlinecode"><span class="id"
type="var">dcom</span></span> to a <span class="inlinecode"><span
class="id" type="var">com</span></span> by erasing all annotations.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">extract</span> (<span class="id" type="var">d</span>:<span
class="id" type="var">dcom</span>) : <span class="id"
type="var">com</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">d</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">DCSkip</span> <span class="id"
type="var">\_</span> ⇒ <span class="id" type="var">SKIP</span>\
   | <span class="id" type="var">DCSeq</span> <span class="id"
type="var">d1</span> <span class="id" type="var">d2</span> ⇒ (<span
class="id" type="var">extract</span> <span class="id"
type="var">d1</span> ;; <span class="id" type="var">extract</span> <span
class="id" type="var">d2</span>)\
   | <span class="id" type="var">DCAsgn</span> <span class="id"
type="var">X</span> <span class="id" type="var">a</span> <span
class="id" type="var">\_</span> ⇒ <span class="id" type="var">X</span>
::= <span class="id" type="var">a</span>\
   | <span class="id" type="var">DCIf</span> <span class="id"
type="var">b</span> <span class="id" type="var">\_</span> <span
class="id" type="var">d1</span> <span class="id" type="var">\_</span>
<span class="id" type="var">d2</span> <span class="id"
type="var">\_</span> ⇒ <span class="id" type="var">IFB</span> <span
class="id" type="var">b</span> <span class="id" type="var">THEN</span>
<span class="id" type="var">extract</span> <span class="id"
type="var">d1</span> <span class="id" type="var">ELSE</span> <span
class="id" type="var">extract</span> <span class="id"
type="var">d2</span> <span class="id" type="var">FI</span>\
   | <span class="id" type="var">DCWhile</span> <span class="id"
type="var">b</span> <span class="id" type="var">\_</span> <span
class="id" type="var">d</span> <span class="id" type="var">\_</span> ⇒
<span class="id" type="var">WHILE</span> <span class="id"
type="var">b</span> <span class="id" type="var">DO</span> <span
class="id" type="var">extract</span> <span class="id"
type="var">d</span> <span class="id" type="var">END</span>\
   | <span class="id" type="var">DCPre</span> <span class="id"
type="var">\_</span> <span class="id" type="var">d</span> ⇒ <span
class="id" type="var">extract</span> <span class="id"
type="var">d</span>\
   | <span class="id" type="var">DCPost</span> <span class="id"
type="var">d</span> <span class="id" type="var">\_</span> ⇒ <span
class="id" type="var">extract</span> <span class="id"
type="var">d</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

The choice of exactly where to put assertions in the definition of <span
class="inlinecode"><span class="id" type="var">dcom</span></span> is a
bit subtle. The simplest thing to do would be to annotate every <span
class="inlinecode"><span class="id" type="var">dcom</span></span> with a
precondition and postcondition. But this would result in very verbose
programs with a lot of repeated annotations: for example, a program like
<span class="inlinecode"><span class="id" type="var">SKIP</span>;<span
class="id" type="var">SKIP</span></span> would have to be annotated as
<div class="paragraph">

</div>

<div class="code code-tight">

        <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} (<span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">SKIP</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span
style="letter-spacing:-.4em;">}</span>}) ;; (<span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">SKIP</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>}) <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>},
<div class="paragraph">

</div>

</div>

with pre- and post-conditions on each <span class="inlinecode"><span
class="id" type="var">SKIP</span></span>, plus identical pre- and
post-conditions on the semicolon!
<div class="paragraph">

</div>

Instead, the rule we've followed is this:
<div class="paragraph">

</div>

-   The *post*-condition expected by each <span class="inlinecode"><span
    class="id" type="var">dcom</span></span> <span
    class="inlinecode"><span class="id" type="var">d</span></span> is
    embedded in <span class="inlinecode"><span class="id"
    type="var">d</span></span>
    <div class="paragraph">

    </div>

-   The *pre*-condition is supplied by the context.

<div class="paragraph">

</div>

In other words, the invariant of the representation is that a <span
class="inlinecode"><span class="id" type="var">dcom</span></span> <span
class="inlinecode"><span class="id" type="var">d</span></span> together
with a precondition <span class="inlinecode"><span class="id"
type="var">P</span></span> determines a Hoare triple <span
class="inlinecode"><span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">P</span><span
style="letter-spacing:-.4em;">}</span>}</span> <span
class="inlinecode">(<span class="id" type="var">extract</span></span>
<span class="inlinecode"><span class="id" type="var">d</span>)</span>
<span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">post</span></span> <span class="inlinecode"><span class="id"
type="var">d</span><span style="letter-spacing:-.4em;">}</span>}</span>,
where <span class="inlinecode"><span class="id"
type="var">post</span></span> is defined as follows:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">post</span> (<span class="id" type="var">d</span>:<span
class="id" type="var">dcom</span>) : <span class="id"
type="var">Assertion</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">d</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">DCSkip</span> <span class="id"
type="var">P</span> ⇒ <span class="id" type="var">P</span>\
   | <span class="id" type="var">DCSeq</span> <span class="id"
type="var">d1</span> <span class="id" type="var">d2</span> ⇒ <span
class="id" type="var">post</span> <span class="id" type="var">d2</span>\
   | <span class="id" type="var">DCAsgn</span> <span class="id"
type="var">X</span> <span class="id" type="var">a</span> <span
class="id" type="var">Q</span> ⇒ <span class="id" type="var">Q</span>\
   | <span class="id" type="var">DCIf</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">d1</span> <span class="id" type="var">\_</span>
<span class="id" type="var">d2</span> <span class="id"
type="var">Q</span> ⇒ <span class="id" type="var">Q</span>\
   | <span class="id" type="var">DCWhile</span> <span class="id"
type="var">b</span> <span class="id" type="var">Pbody</span> <span
class="id" type="var">c</span> <span class="id" type="var">Ppost</span>
⇒ <span class="id" type="var">Ppost</span>\
   | <span class="id" type="var">DCPre</span> <span class="id"
type="var">\_</span> <span class="id" type="var">d</span> ⇒ <span
class="id" type="var">post</span> <span class="id" type="var">d</span>\
   | <span class="id" type="var">DCPost</span> <span class="id"
type="var">c</span> <span class="id" type="var">Q</span> ⇒ <span
class="id" type="var">Q</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Similarly, we can extract the "initial precondition" from a decorated
program.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">pre</span> (<span class="id" type="var">d</span>:<span
class="id" type="var">dcom</span>) : <span class="id"
type="var">Assertion</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">d</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">DCSkip</span> <span class="id"
type="var">P</span> ⇒ <span class="id" type="keyword">fun</span> <span
class="id" type="var">st</span> ⇒ <span class="id"
type="var">True</span>\
   | <span class="id" type="var">DCSeq</span> <span class="id"
type="var">c1</span> <span class="id" type="var">c2</span> ⇒ <span
class="id" type="var">pre</span> <span class="id" type="var">c1</span>\
   | <span class="id" type="var">DCAsgn</span> <span class="id"
type="var">X</span> <span class="id" type="var">a</span> <span
class="id" type="var">Q</span> ⇒ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">True</span>\
   | <span class="id" type="var">DCIf</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">t</span> <span class="id" type="var">\_</span>
<span class="id" type="var">e</span> <span class="id"
type="var">\_</span> ⇒ <span class="id" type="keyword">fun</span> <span
class="id" type="var">st</span> ⇒ <span class="id"
type="var">True</span>\
   | <span class="id" type="var">DCWhile</span> <span class="id"
type="var">b</span> <span class="id" type="var">Pbody</span> <span
class="id" type="var">c</span> <span class="id" type="var">Ppost</span>
⇒ <span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">True</span>\
   | <span class="id" type="var">DCPre</span> <span class="id"
type="var">P</span> <span class="id" type="var">c</span> ⇒ <span
class="id" type="var">P</span>\
   | <span class="id" type="var">DCPost</span> <span class="id"
type="var">c</span> <span class="id" type="var">Q</span> ⇒ <span
class="id" type="var">pre</span> <span class="id" type="var">c</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

This function is not doing anything sophisticated like calculating a
weakest precondition; it just recursively searches for an explicit
annotation at the very beginning of the program, returning default
answers for programs that lack an explicit precondition (like a bare
assignment or <span class="inlinecode"><span class="id"
type="var">SKIP</span></span>).
<div class="paragraph">

</div>

Using <span class="inlinecode"><span class="id"
type="var">pre</span></span> and <span class="inlinecode"><span
class="id" type="var">post</span></span>, and assuming that we adopt the
convention of always supplying an explicit precondition annotation at
the very beginning of our decorated programs, we can express what it
means for a decorated program to be correct as follows:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">dec\_correct</span> (<span class="id"
type="var">d</span>:<span class="id" type="var">dcom</span>) :=\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">pre</span> <span class="id" type="var">d</span><span
style="letter-spacing:-.4em;">}</span>} (<span class="id"
type="var">extract</span> <span class="id" type="var">d</span>) <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">post</span> <span class="id" type="var">d</span><span
style="letter-spacing:-.4em;">}</span>}.\
\

</div>

<div class="doc">

To check whether this Hoare triple is *valid*, we need a way to extract
the "proof obligations" from a decorated program. These obligations are
often called *verification conditions*, because they are the facts that
must be verified to see that the decorations are logically consistent
and thus add up to a complete proof of correctness.
<div class="paragraph">

</div>

Extracting Verification Conditions {.section}
----------------------------------

<div class="paragraph">

</div>

The function <span class="inlinecode"><span class="id"
type="var">verification\_conditions</span></span> takes a <span
class="inlinecode"><span class="id" type="var">dcom</span></span> <span
class="inlinecode"><span class="id" type="var">d</span></span> together
with a precondition <span class="inlinecode"><span class="id"
type="var">P</span></span> and returns a *proposition* that, if it can
be proved, implies that the triple <span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>}</span>
<span class="inlinecode">(<span class="id"
type="var">extract</span></span> <span class="inlinecode"><span
class="id" type="var">d</span>)</span> <span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">post</span></span> <span class="inlinecode"><span class="id"
type="var">d</span><span style="letter-spacing:-.4em;">}</span>}</span>
is valid.
<div class="paragraph">

</div>

It does this by walking over <span class="inlinecode"><span class="id"
type="var">d</span></span> and generating a big conjunction including
all the "local checks" that we listed when we described the informal
rules for decorated programs. (Strictly speaking, we need to massage the
informal rules a little bit to add some uses of the rule of consequence,
but the correspondence should be clear.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">verification\_conditions</span> (<span class="id"
type="var">P</span> : <span class="id" type="var">Assertion</span>)
(<span class="id" type="var">d</span>:<span class="id"
type="var">dcom</span>) : <span class="id" type="keyword">Prop</span>
:=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">d</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">DCSkip</span> <span class="id"
type="var">Q</span> ⇒\
       (<span class="id" type="var">P</span> <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">Q</span>)\
   | <span class="id" type="var">DCSeq</span> <span class="id"
type="var">d1</span> <span class="id" type="var">d2</span> ⇒\
       <span class="id" type="var">verification\_conditions</span> <span
class="id" type="var">P</span> <span class="id" type="var">d1</span>\
       <span style="font-family: arial;">∧</span> <span class="id"
type="var">verification\_conditions</span> (<span class="id"
type="var">post</span> <span class="id" type="var">d1</span>) <span
class="id" type="var">d2</span>\
   | <span class="id" type="var">DCAsgn</span> <span class="id"
type="var">X</span> <span class="id" type="var">a</span> <span
class="id" type="var">Q</span> ⇒\
       (<span class="id" type="var">P</span> <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">Q</span> [<span class="id" type="var">X</span> <span
style="font-family: arial;">↦</span> <span class="id"
type="var">a</span>])\
   | <span class="id" type="var">DCIf</span> <span class="id"
type="var">b</span> <span class="id" type="var">P1</span> <span
class="id" type="var">d1</span> <span class="id" type="var">P2</span>
<span class="id" type="var">d2</span> <span class="id"
type="var">Q</span> ⇒\
       ((<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">P</span> <span
class="id" type="var">st</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span>) <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">P1</span>)\
       <span style="font-family: arial;">∧</span> ((<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">P</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">∧</span> ¬ (<span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span>)) <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">P2</span>)\
       <span style="font-family: arial;">∧</span> (<span class="id"
type="var">Q</span> <span style="font-family: arial;">⇿</span> <span
class="id" type="var">post</span> <span class="id" type="var">d1</span>)
<span style="font-family: arial;">∧</span> (<span class="id"
type="var">Q</span> <span style="font-family: arial;">⇿</span> <span
class="id" type="var">post</span> <span class="id"
type="var">d2</span>)\
       <span style="font-family: arial;">∧</span> <span class="id"
type="var">verification\_conditions</span> <span class="id"
type="var">P1</span> <span class="id" type="var">d1</span>\
       <span style="font-family: arial;">∧</span> <span class="id"
type="var">verification\_conditions</span> <span class="id"
type="var">P2</span> <span class="id" type="var">d2</span>\
   | <span class="id" type="var">DCWhile</span> <span class="id"
type="var">b</span> <span class="id" type="var">Pbody</span> <span
class="id" type="var">d</span> <span class="id" type="var">Ppost</span>
⇒\
       <span
class="comment">(\* post d is the loop invariant and the initial precondition \*)</span>\
       (<span class="id" type="var">P</span> <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">post</span> <span class="id" type="var">d</span>)\
       <span style="font-family: arial;">∧</span> (<span class="id"
type="var">Pbody</span> <span style="font-family: arial;">⇿</span>
(<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">post</span> <span
class="id" type="var">d</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span>))\
       <span style="font-family: arial;">∧</span> (<span class="id"
type="var">Ppost</span> <span style="font-family: arial;">⇿</span>
(<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">post</span> <span
class="id" type="var">d</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">∧</span> \~(<span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span>)))\
       <span style="font-family: arial;">∧</span> <span class="id"
type="var">verification\_conditions</span> <span class="id"
type="var">Pbody</span> <span class="id" type="var">d</span>\
   | <span class="id" type="var">DCPre</span> <span class="id"
type="var">P'</span> <span class="id" type="var">d</span> ⇒\
       (<span class="id" type="var">P</span> <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">P'</span>) <span style="font-family: arial;">∧</span> <span
class="id" type="var">verification\_conditions</span> <span class="id"
type="var">P'</span> <span class="id" type="var">d</span>\
   | <span class="id" type="var">DCPost</span> <span class="id"
type="var">d</span> <span class="id" type="var">Q</span> ⇒\
       <span class="id" type="var">verification\_conditions</span> <span
class="id" type="var">P</span> <span class="id" type="var">d</span>
<span style="font-family: arial;">∧</span> (<span class="id"
type="var">post</span> <span class="id" type="var">d</span> <span
style="font-family: arial;">⇾</span> <span class="id"
type="var">Q</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

And now, the key theorem, which states that <span
class="inlinecode"><span class="id"
type="var">verification\_conditions</span></span> does its job
correctly. Not surprisingly, we need to use each of the Hoare Logic
rules at some point in the proof. We have used *in* variants of several
tactics before to apply them to values in the context rather than the
goal. An extension of this idea is the syntax <span
class="inlinecode"><span class="id" type="var">tactic</span></span>
<span class="inlinecode"><span class="id"
type="keyword">in</span></span> <span class="inlinecode">×</span>, which
applies <span class="inlinecode"><span class="id"
type="var">tactic</span></span> in the goal and every hypothesis in the
context. We most commonly use this facility in conjunction with the
<span class="inlinecode"><span class="id"
type="tactic">simpl</span></span> tactic, as below.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">verification\_correct</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">d</span>
<span class="id" type="var">P</span>,\
   <span class="id" type="var">verification\_conditions</span> <span
class="id" type="var">P</span> <span class="id" type="var">d</span>
<span style="font-family: arial;">→</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} (<span
class="id" type="var">extract</span> <span class="id"
type="var">d</span>) <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">post</span> <span class="id"
type="var">d</span><span style="letter-spacing:-.4em;">}</span>}.\
<div id="proofcontrol3" class="togglescript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')">

<span class="show"></span>

</div>

<div id="proof3" class="proofscript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="var">dcom\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">d</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">P</span> <span
class="id" type="var">H</span>; <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span> ×.\
   <span class="id" type="var">Case</span> "Skip".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_skip</span>.\
       <span class="id" type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "Seq".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">H1</span> <span class="id" type="var">H2</span>].
<span class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_seq</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHd2</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">H2</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHd1</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">H1</span>.\
   <span class="id" type="var">Case</span> "Asgn".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_asgn</span>.\
       <span class="id" type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "If".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">HPre1</span> [<span class="id"
type="var">HPre2</span> [[<span class="id" type="var">Hd11</span> <span
class="id" type="var">Hd12</span>]\
                                   [[<span class="id"
type="var">Hd21</span> <span class="id" type="var">Hd22</span>] [<span
class="id" type="var">HThen</span> <span class="id"
type="var">HElse</span>]]]]].\
     <span class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHd1</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">HThen</span>. <span class="id"
type="tactic">clear</span> <span class="id" type="var">IHd1</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHd2</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">HElse</span>. <span class="id"
type="tactic">clear</span> <span class="id" type="var">IHd2</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_if</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>; <span class="id"
type="tactic">eauto</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_post</span>; <span class="id"
type="tactic">eauto</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>; <span class="id"
type="tactic">eauto</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_post</span>; <span class="id"
type="tactic">eauto</span>.\
   <span class="id" type="var">Case</span> "While".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">Hpre</span> [[<span class="id"
type="var">Hbody1</span> <span class="id" type="var">Hbody2</span>]
[[<span class="id" type="var">Hpost1</span> <span class="id"
type="var">Hpost2</span>] <span class="id" type="var">Hd</span>]]];\
     <span class="id" type="tactic">subst</span>; <span class="id"
type="tactic">clear</span> <span class="id" type="var">H</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>; <span class="id"
type="tactic">eauto</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_post</span>; <span class="id"
type="tactic">eauto</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">hoare\_while</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>; <span class="id"
type="tactic">eauto</span>.\
   <span class="id" type="var">Case</span> "Pre".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">HP</span> <span class="id" type="var">Hd</span>];
<span class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_pre</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHd</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">Hd</span>. <span class="id" type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> "Post".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">Hd</span> <span class="id" type="var">HQ</span>];
<span class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">hoare\_consequence\_post</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHd</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">Hd</span>. <span class="id" type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Examples {.section}
--------

<div class="paragraph">

</div>

The propositions generated by <span class="inlinecode"><span class="id"
type="var">verification\_conditions</span></span> are fairly big, and
they contain many conjuncts that are essentially trivial.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Eval</span> <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span>
(<span class="id" type="var">verification\_conditions</span> (<span
class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">True</span>) <span
class="id" type="var">dec\_while</span>).\

</div>

<div class="doc">

<div class="paragraph">

</div>

<div class="code code-tight">

<span style="font-family: arial;">⇒</span>\
 (((<span class="id" type="keyword">fun</span> <span class="id"
type="var">\_</span> : <span class="id" type="var">state</span> ⇒ <span
class="id" type="var">True</span>) <span
style="font-family: arial;">⇾</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">\_</span> : <span
class="id" type="var">state</span> ⇒ <span class="id"
type="var">True</span>)) <span style="font-family: arial;">∧</span>\
  ((<span class="id" type="keyword">fun</span> <span class="id"
type="var">\_</span> : <span class="id" type="var">state</span> ⇒ <span
class="id" type="var">True</span>) <span
style="font-family: arial;">⇾</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">\_</span> : <span
class="id" type="var">state</span> ⇒ <span class="id"
type="var">True</span>)) <span style="font-family: arial;">∧</span>\
  (<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> : <span class="id" type="var">state</span> ⇒ <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">bassn</span> (<span class="id" type="var">BNot</span> (<span
class="id" type="var">BEq</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">ANum</span> 0))) <span class="id"
type="var">st</span>) =\
  (<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> : <span class="id" type="var">state</span> ⇒ <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">bassn</span> (<span class="id" type="var">BNot</span> (<span
class="id" type="var">BEq</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">ANum</span> 0))) <span class="id"
type="var">st</span>) <span style="font-family: arial;">∧</span>\
  (<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> : <span class="id" type="var">state</span> ⇒ <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> ¬ <span class="id"
type="var">bassn</span> (<span class="id" type="var">BNot</span> (<span
class="id" type="var">BEq</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">ANum</span> 0))) <span class="id"
type="var">st</span>) =\
  (<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> : <span class="id" type="var">state</span> ⇒ <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> ¬ <span class="id"
type="var">bassn</span> (<span class="id" type="var">BNot</span> (<span
class="id" type="var">BEq</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">ANum</span> 0))) <span class="id"
type="var">st</span>) <span style="font-family: arial;">∧</span>\
  (<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> : <span class="id" type="var">state</span> ⇒ <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">bassn</span> (<span class="id" type="var">BNot</span> (<span
class="id" type="var">BEq</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">ANum</span> 0))) <span class="id"
type="var">st</span>) <span style="font-family: arial;">⇾</span>\
  (<span class="id" type="keyword">fun</span> <span class="id"
type="var">\_</span> : <span class="id" type="var">state</span> ⇒ <span
class="id" type="var">True</span>) [<span class="id"
type="var">X</span> <span style="font-family: arial;">↦</span> <span
class="id" type="var">AMinus</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">ANum</span> 1)]) <span
style="font-family: arial;">∧</span>\
 (<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> : <span class="id" type="var">state</span> ⇒ <span
class="id" type="var">True</span> <span
style="font-family: arial;">∧</span> ¬ <span class="id"
type="var">bassn</span> (<span class="id" type="var">BNot</span> (<span
class="id" type="var">BEq</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">ANum</span> 0))) <span class="id"
type="var">st</span>) <span style="font-family: arial;">⇾</span>\
 (<span class="id" type="keyword">fun</span> <span class="id"
type="var">st</span> : <span class="id" type="var">state</span> ⇒ <span
class="id" type="var">st</span> <span class="id"
type="var">X</span> = 0)
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

In principle, we could certainly work with them using just the tactics
we have so far, but we can make things much smoother with a bit of
automation. We first define a custom <span class="inlinecode"><span
class="id" type="var">verify</span></span> tactic that applies splitting
repeatedly to turn all the conjunctions into separate subgoals and then
uses <span class="inlinecode"><span class="id"
type="tactic">omega</span></span> and <span class="inlinecode"><span
class="id" type="tactic">eauto</span></span> (a handy general-purpose
automation tactic that we'll discuss in detail later) to deal with as
many of them as possible.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">ble\_nat\_true\_iff</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> : <span class="id"
type="var">nat</span>,\
   <span class="id" type="var">ble\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">n</span> ≤ <span class="id" type="var">m</span>.\
<div id="proofcontrol4" class="togglescript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')">

<span class="show"></span>

</div>

<div id="proof4" class="proofscript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span>. <span
class="id" type="tactic">split</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">ble\_nat\_true</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">m</span>.
<span class="id" type="tactic">induction</span> <span class="id"
type="var">n</span>; <span class="id" type="tactic">intros</span> <span
class="id" type="var">m</span> <span class="id" type="var">H</span>.
<span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">m</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">le\_S\_n</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHn</span>. <span
class="id" type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">ble\_nat\_false\_iff</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> : <span class="id"
type="var">nat</span>,\
   <span class="id" type="var">ble\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">↔</span> \~(<span class="id"
type="var">n</span> ≤ <span class="id" type="var">m</span>).\
<div id="proofcontrol5" class="togglescript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')">

<span class="show"></span>

</div>

<div id="proof5" class="proofscript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')"
style="display: none;">

<span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span>. <span
class="id" type="tactic">split</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">ble\_nat\_false</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">m</span>.
<span class="id" type="tactic">induction</span> <span class="id"
type="var">n</span>; <span class="id" type="tactic">intros</span> <span
class="id" type="var">m</span> <span class="id" type="var">H</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">ex\_falso\_quodlibet</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">le\_0\_n</span>.\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">m</span>.
<span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHn</span>. <span class="id" type="tactic">intro</span> <span
class="id" type="var">Hc</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">le\_n\_S</span>. <span class="id"
type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Tactic Notation</span> "verify" :=\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">verification\_correct</span>;\
   <span class="id" type="tactic">repeat</span> <span class="id"
type="tactic">split</span>;\
   <span class="id" type="tactic">simpl</span>; <span class="id"
type="tactic">unfold</span> <span class="id"
type="var">assert\_implies</span>;\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">bassn</span> <span class="id" type="keyword">in</span> ×;
<span class="id" type="tactic">unfold</span> <span class="id"
type="var">beval</span> <span class="id" type="keyword">in</span> ×;
<span class="id" type="tactic">unfold</span> <span class="id"
type="var">aeval</span> <span class="id" type="keyword">in</span> ×;\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">assn\_sub</span>; <span class="id"
type="tactic">intros</span>;\
   <span class="id" type="tactic">repeat</span> <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">update\_eq</span>;\
   <span class="id" type="tactic">repeat</span> (<span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">update\_neq</span>; [| (<span class="id"
type="tactic">intro</span> <span class="id" type="var">X</span>; <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">X</span>)]);\
   <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> ×;\
   <span class="id" type="tactic">repeat</span> <span class="id"
type="keyword">match</span> <span class="id" type="var">goal</span>
<span class="id" type="keyword">with</span> [<span class="id"
type="var">H</span> : <span class="id" type="var">\_</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">\_</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">\_</span>] ⇒ <span class="id"
type="tactic">destruct</span> <span class="id" type="var">H</span> <span
class="id" type="keyword">end</span>;\
   <span class="id" type="tactic">repeat</span> <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">not\_true\_iff\_false</span> <span class="id"
type="keyword">in</span> ×;\
   <span class="id" type="tactic">repeat</span> <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">not\_false\_iff\_true</span> <span class="id"
type="keyword">in</span> ×;\
   <span class="id" type="tactic">repeat</span> <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">negb\_true\_iff</span> <span class="id"
type="keyword">in</span> ×;\
   <span class="id" type="tactic">repeat</span> <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">negb\_false\_iff</span> <span class="id"
type="keyword">in</span> ×;\
   <span class="id" type="tactic">repeat</span> <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">beq\_nat\_true\_iff</span> <span class="id"
type="keyword">in</span> ×;\
   <span class="id" type="tactic">repeat</span> <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">beq\_nat\_false\_iff</span> <span class="id"
type="keyword">in</span> ×;\
   <span class="id" type="tactic">repeat</span> <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">ble\_nat\_true\_iff</span> <span class="id"
type="keyword">in</span> ×;\
   <span class="id" type="tactic">repeat</span> <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">ble\_nat\_false\_iff</span> <span class="id"
type="keyword">in</span> ×;\
   <span class="id" type="tactic">try</span> <span class="id"
type="tactic">subst</span>;\
   <span class="id" type="tactic">repeat</span>\
     <span class="id" type="keyword">match</span> <span class="id"
type="var">goal</span> <span class="id" type="keyword">with</span>\
       [<span class="id" type="var">st</span> : <span class="id"
type="var">state</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">\_</span>] ⇒\
         <span class="id" type="keyword">match</span> <span class="id"
type="var">goal</span> <span class="id" type="keyword">with</span>\
           [<span class="id" type="var">H</span> : <span class="id"
type="var">st</span> <span class="id" type="var">\_</span> = <span
class="id" type="var">\_</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">\_</span>] ⇒ <span class="id" type="tactic">rewrite</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> ×; <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>\
         | [<span class="id" type="var">H</span> : <span class="id"
type="var">\_</span> = <span class="id" type="var">st</span> <span
class="id" type="var">\_</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">\_</span>] ⇒ <span class="id" type="tactic">rewrite</span>
<span style="font-family: arial;">←</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> ×; <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>\
         <span class="id" type="keyword">end</span>\
     <span class="id" type="keyword">end</span>;\
   <span class="id" type="tactic">try</span> <span class="id"
type="tactic">eauto</span>; <span class="id" type="tactic">try</span>
<span class="id" type="tactic">omega</span>.\
\

</div>

<div class="doc">

What's left after <span class="inlinecode"><span class="id"
type="var">verify</span></span> does its thing is "just the interesting
parts" of checking that the decorations are correct. For very simple
examples <span class="inlinecode"><span class="id"
type="var">verify</span></span> immediately solves the goal (provided
that the annotations are correct).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">dec\_while\_correct</span> :\
   <span class="id" type="var">dec\_correct</span> <span class="id"
type="var">dec\_while</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="var">verify</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Another example (formalizing a decorated program we've seen before):

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">subtract\_slowly\_dec</span> (<span class="id"
type="var">m</span>:<span class="id" type="var">nat</span>) (<span
class="id" type="var">p</span>:<span class="id" type="var">nat</span>) :
<span class="id" type="var">dcom</span> := (\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">X</span> =
<span class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">st</span> <span class="id" type="var">Z</span> = <span
class="id" type="var">p</span> <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">Z</span> -
<span class="id" type="var">st</span> <span class="id"
type="var">X</span> = <span class="id" type="var">p</span> - <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">WHILE</span> <span class="id"
type="var">BNot</span> (<span class="id" type="var">BEq</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 0))\
   <span class="id" type="var">DO</span> <span
style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">Z</span> -
<span class="id" type="var">st</span> <span class="id"
type="var">X</span> = <span class="id" type="var">p</span> - <span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> ≠ 0 <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
        <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ (<span
class="id" type="var">st</span> <span class="id" type="var">Z</span> -
1) - (<span class="id" type="var">st</span> <span class="id"
type="var">X</span> - 1) = <span class="id" type="var">p</span> - <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
      <span class="id" type="var">Z</span> ::= <span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">Z</span>) (<span class="id" type="var">ANum</span>
1)\
        <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">Z</span> -
(<span class="id" type="var">st</span> <span class="id"
type="var">X</span> - 1) = <span class="id" type="var">p</span> - <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>} ;;\
      <span class="id" type="var">X</span> ::= <span class="id"
type="var">AMinus</span> (<span class="id" type="var">AId</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">ANum</span>
1)\
        <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">Z</span> -
<span class="id" type="var">st</span> <span class="id"
type="var">X</span> = <span class="id" type="var">p</span> - <span
class="id" type="var">m</span> <span
style="letter-spacing:-.4em;">}</span>}\
   <span class="id" type="var">END</span>\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">Z</span> -
<span class="id" type="var">st</span> <span class="id"
type="var">X</span> = <span class="id" type="var">p</span> - <span
class="id" type="var">m</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">st</span> <span class="id" type="var">X</span> = 0 <span
style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">⇾</span>\
     <span style="letter-spacing:-.4em;">{</span>{ <span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">st</span> <span class="id" type="var">Z</span> =
<span class="id" type="var">p</span> - <span class="id"
type="var">m</span> <span style="letter-spacing:-.4em;">}</span>}\
 ) % <span class="id" type="var">dcom</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">subtract\_slowly\_dec\_correct</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">m</span>
<span class="id" type="var">p</span>,\
   <span class="id" type="var">dec\_correct</span> (<span class="id"
type="var">subtract\_slowly\_dec</span> <span class="id"
type="var">m</span> <span class="id" type="var">p</span>).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">m</span> <span
class="id" type="var">p</span>. <span class="id"
type="var">verify</span>. <span
class="comment">(\* this grinds for a bit! \*)</span> <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars, advanced (slow\_assignment\_dec) {.section}

<div class="paragraph">

</div>

In the <span class="inlinecode"><span class="id"
type="var">slow\_assignment</span></span> exercise above, we saw a
roundabout way of assigning a number currently stored in <span
class="inlinecode"><span class="id" type="var">X</span></span> to the
variable <span class="inlinecode"><span class="id"
type="var">Y</span></span>: start <span class="inlinecode"><span
class="id" type="var">Y</span></span> at <span
class="inlinecode">0</span>, then decrement <span
class="inlinecode"><span class="id" type="var">X</span></span> until it
hits <span class="inlinecode">0</span>, incrementing <span
class="inlinecode"><span class="id" type="var">Y</span></span> at each
step.
<div class="paragraph">

</div>

Write a *formal* version of this decorated program and prove it correct.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">slow\_assignment\_dec</span> (<span class="id"
type="var">m</span>:<span class="id" type="var">nat</span>) : <span
class="id" type="var">dcom</span> :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">slow\_assignment\_dec\_correct</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">m</span>,\
   <span class="id" type="var">dec\_correct</span> (<span class="id"
type="var">slow\_assignment\_dec</span> <span class="id"
type="var">m</span>).\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, advanced (factorial\_dec) {.section}

Remember the factorial function we worked with before:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">real\_fact</span> (<span class="id" type="var">n</span>:<span
class="id" type="var">nat</span>) : <span class="id"
type="var">nat</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">n</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">O</span> ⇒ 1\
   | <span class="id" type="var">S</span> <span class="id"
type="var">n'</span> ⇒ <span class="id" type="var">n</span> × (<span
class="id" type="var">real\_fact</span> <span class="id"
type="var">n'</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Following the pattern of <span class="inlinecode"><span class="id"
type="var">subtract\_slowly\_dec</span></span>, write a decorated
program <span class="inlinecode"><span class="id"
type="var">factorial\_dec</span></span> that implements the factorial
function and prove it correct as <span class="inlinecode"><span
class="id" type="var">factorial\_dec\_correct</span></span>.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

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
