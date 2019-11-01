<div id="page">

<div id="header">

</div>

<div id="main">

References<span class="subtitle">Typing Mutable References</span> {.libtitle}
=================================================================

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

</div>

<div class="doc">

So far, we have considered a variety of *pure* language features,
including functional abstraction, basic types such as numbers and
booleans, and structured types such as records and variants. These
features form the backbone of most programming languages — including
purely functional languages such as Haskell, "mostly functional"
languages such as ML, imperative languages such as C, and
object-oriented languages such as Java.
<div class="paragraph">

</div>

Most practical programming languages also include various *impure*
features that cannot be described in the simple semantic framework we
have used so far. In particular, besides just yielding results,
evaluation of terms in these languages may assign to mutable variables
(reference cells, arrays, mutable record fields, etc.), perform input
and output to files, displays, or network connections, make non-local
transfers of control via exceptions, jumps, or continuations, engage in
inter-process synchronization and communication, and so on. In the
literature on programming languages, such "side effects" of computation
are more generally referred to as *computational effects*.
<div class="paragraph">

</div>

In this chapter, we'll see how one sort of computational effect —
mutable references — can be added to the calculi we have studied. The
main extension will be dealing explicitly with a *store* (or *heap*).
This extension is straightforward to define; the most interesting part
is the refinement we need to make to the statement of the type
preservation theorem.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Definitions {.section}
===========

<div class="paragraph">

</div>

Pretty much every programming language provides some form of assignment
operation that changes the contents of a previously allocated piece of
storage. (Coq's internal language is a rare exception!)
<div class="paragraph">

</div>

In some languages — notably ML and its relatives — the mechanisms for
name-binding and those for assignment are kept separate. We can have a
variable <span class="inlinecode"><span class="id"
type="var">x</span></span> whose *value* is the number <span
class="inlinecode">5</span>, or we can have a variable <span
class="inlinecode"><span class="id" type="var">y</span></span> whose
value is a *reference* (or *pointer*) to a mutable cell whose current
contents is <span class="inlinecode">5</span>. These are different
things, and the difference is visible to the programmer. We can add
<span class="inlinecode"><span class="id" type="var">x</span></span> to
another number, but not assign to it. We can use <span
class="inlinecode"><span class="id" type="var">y</span></span> directly
to assign a new value to the cell that it points to (by writing <span
class="inlinecode"><span class="id" type="var">y</span>:=84</span>), but
we cannot use it directly as an argument to an operation like <span
class="inlinecode">+</span>. Instead, we must explicitly *dereference*
it, writing <span class="inlinecode">!<span class="id"
type="var">y</span></span> to obtain its current contents.
<div class="paragraph">

</div>

In most other languages — in particular, in all members of the C family,
including Java — *every* variable name refers to a mutable cell, and the
operation of dereferencing a variable to obtain its current contents is
implicit.
<div class="paragraph">

</div>

For purposes of formal study, it is useful to keep these mechanisms
separate. The development in this chapter will closely follow ML's
model. Applying the lessons learned here to C-like languages is a
straightforward matter of collapsing some distinctions and rendering
some operations such as dereferencing implicit instead of explicit.
<div class="paragraph">

</div>

In this chapter, we study adding mutable references to the simply-typed
lambda calculus with natural numbers.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Syntax {.section}
======

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">STLCRef</span>.\
\

</div>

<div class="doc">

The basic operations on references are *allocation*, *dereferencing*,
and *assignment*.
<div class="paragraph">

</div>

-   To allocate a reference, we use the <span class="inlinecode"><span
    class="id" type="var">ref</span></span> operator, providing an
    initial value for the new cell. For example, <span
    class="inlinecode"><span class="id" type="var">ref</span></span>
    <span class="inlinecode">5</span> creates a new cell containing the
    value <span class="inlinecode">5</span>, and evaluates to a
    reference to that cell.
    <div class="paragraph">

    </div>

-   To read the current value of this cell, we use the dereferencing
    operator <span class="inlinecode">!</span>; for example, <span
    class="inlinecode">!(<span class="id" type="var">ref</span></span>
    <span class="inlinecode">5)</span> evaluates to <span
    class="inlinecode">5</span>.
    <div class="paragraph">

    </div>

-   To change the value stored in a cell, we use the assignment
    operator. If <span class="inlinecode"><span class="id"
    type="var">r</span></span> is a reference, <span
    class="inlinecode"><span class="id" type="var">r</span></span> <span
    class="inlinecode">:=</span> <span class="inlinecode">7</span> will
    store the value <span class="inlinecode">7</span> in the cell
    referenced by <span class="inlinecode"><span class="id"
    type="var">r</span></span>. However, <span class="inlinecode"><span
    class="id" type="var">r</span></span> <span
    class="inlinecode">:=</span> <span class="inlinecode">7</span>
    evaluates to the trivial value <span class="inlinecode"><span
    class="id" type="var">unit</span></span>; it exists only to have the
    *side effect* of modifying the contents of a cell.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Types {.section}

<div class="paragraph">

</div>

We start with the simply typed lambda calculus over the natural numbers.
To the base natural number type and arrow types we need to add two more
types to deal with references. First, we need the *unit type*, which we
will use as the result type of an assignment operation. We then add
*reference types*. If <span class="inlinecode"><span class="id"
type="var">T</span></span> is a type, then <span
class="inlinecode"><span class="id" type="var">Ref</span></span> <span
class="inlinecode"><span class="id" type="var">T</span></span> is the
type of references which point to a cell holding values of type <span
class="inlinecode"><span class="id" type="var">T</span></span>.
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">T</span> ::= <span class="id"
type="var">Nat</span>\
           | <span class="id" type="var">Unit</span>\
           | <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">T</span>\
           | <span class="id" type="var">Ref</span> <span class="id"
type="var">T</span>
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ty</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">TNat</span> : <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TUnit</span> : <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TArrow</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TRef</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span>.\
\

</div>

<div class="doc">

### Terms {.section}

<div class="paragraph">

</div>

Besides variables, abstractions, applications, natural-number-related
terms, and <span class="inlinecode"><span class="id"
type="var">unit</span></span>, we need four more sorts of terms in order
to handle mutable references:
          t ::= ...              Terms
              | ref t              allocation
              | !t                 dereference
              | t := t             assignment
              | l                  location

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">tm</span> : <span class="id" type="keyword">Type</span> :=\
   <span class="comment">(\* STLC with numbers: \*)</span>\
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
class="id" type="var">tm</span>\
   <span class="comment">(\* New terms: \*)</span>\
   | <span class="id" type="var">tunit</span> : <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tref</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">tderef</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>\
   | <span class="id" type="var">tassign</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">tloc</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>.\
\

</div>

<div class="doc">

Intuitively...
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">ref</span></span> <span class="inlinecode"><span
    class="id" type="var">t</span></span> (formally, <span
    class="inlinecode"><span class="id" type="var">tref</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t</span></span>) allocates a new reference cell with the
    value <span class="inlinecode"><span class="id"
    type="var">t</span></span> and evaluates to the location of the
    newly allocated cell;
    <div class="paragraph">

    </div>

-   <span class="inlinecode">!<span class="id"
    type="var">t</span></span> (formally, <span class="inlinecode"><span
    class="id" type="var">tderef</span></span> <span
    class="inlinecode"><span class="id" type="var">t</span></span>)
    evaluates to the contents of the cell referenced by <span
    class="inlinecode"><span class="id" type="var">t</span></span>;
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode">:=</span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> (formally, <span
    class="inlinecode"><span class="id" type="var">tassign</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span>) assigns <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span> to
    the cell referenced by <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span>; and
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id" type="var">l</span></span>
    (formally, <span class="inlinecode"><span class="id"
    type="var">tloc</span></span> <span class="inlinecode"><span
    class="id" type="var">l</span></span>) is a reference to the cell at
    location <span class="inlinecode"><span class="id"
    type="var">l</span></span>. We'll discuss locations later.

<div class="paragraph">

</div>

In informal examples, we'll also freely use the extensions of the STLC
developed in the <span class="inlinecode"><span class="id"
type="var">MoreStlc</span></span> chapter; however, to keep the proofs
small, we won't bother formalizing them again here. It would be easy to
do so, since there are no very interesting interactions between those
features and references.

</div>

<div class="code code-tight">

\
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
"tzero"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tsucc" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"tpred"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tmult" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tif0"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tunit" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tref"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tderef" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"tassign"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tloc" ].\
\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">ExampleVariables</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">x</span> := <span class="id" type="var">Id</span> 0.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">y</span> := <span class="id" type="var">Id</span> 1.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">r</span> := <span class="id" type="var">Id</span> 2.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">s</span> := <span class="id" type="var">Id</span> 3.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">ExampleVariables</span>.\
\

</div>

<div class="doc">

### Typing (Preview) {.section}

<div class="paragraph">

</div>

Informally, the typing rules for allocation, dereferencing, and
assignment will look like this:
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : T~1~
(T\_Ref)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> ref t~1~ : Ref T~1~
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : Ref T~11~
(T\_Deref)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> !t~1~ : T~11~
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : Ref T~11~
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~2~ : T~11~
(T\_Assign)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ := t~2~ : Unit
The rule for locations will require a bit more machinery, and this will
motivate some changes to the other rules; we'll come back to this later.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Values and Substitution {.section}

<div class="paragraph">

</div>

Besides abstractions and numbers, we have two new types of values: the
unit value, and locations.

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
   | <span class="id" type="var">v\_nat</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
       <span class="id" type="var">value</span> (<span class="id"
type="var">tnat</span> <span class="id" type="var">n</span>)\
   | <span class="id" type="var">v\_unit</span> :\
       <span class="id" type="var">value</span> <span class="id"
type="var">tunit</span>\
   | <span class="id" type="var">v\_loc</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l</span>,\
       <span class="id" type="var">value</span> (<span class="id"
type="var">tloc</span> <span class="id" type="var">l</span>).\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">value</span>.\
\

</div>

<div class="doc">

Extending substitution to handle the new syntax of terms is
straightforward.

</div>

<div class="code code-tight">

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
   | <span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒\
       <span class="id" type="var">tapp</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">tabs</span> <span class="id"
type="var">x'</span> <span class="id" type="var">T</span> <span
class="id" type="var">t~1~</span> ⇒\
       <span class="id" type="keyword">if</span> <span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x'</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">t</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">tabs</span> <span class="id" type="var">x'</span> <span
class="id" type="var">T</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">tnat</span> <span class="id"
type="var">n</span> ⇒\
       <span class="id" type="var">t</span>\
   | <span class="id" type="var">tsucc</span> <span class="id"
type="var">t~1~</span> ⇒\
       <span class="id" type="var">tsucc</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">tpred</span> <span class="id"
type="var">t~1~</span> ⇒\
       <span class="id" type="var">tpred</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">tmult</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒\
       <span class="id" type="var">tmult</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">tif0</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> ⇒\
       <span class="id" type="var">tif0</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>) (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~3~</span>)\
   | <span class="id" type="var">tunit</span> ⇒\
       <span class="id" type="var">t</span>\
   | <span class="id" type="var">tref</span> <span class="id"
type="var">t~1~</span> ⇒\
       <span class="id" type="var">tref</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">tderef</span> <span class="id"
type="var">t~1~</span> ⇒\
       <span class="id" type="var">tderef</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">tassign</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒\
       <span class="id" type="var">tassign</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">tloc</span> <span class="id"
type="var">\_</span> ⇒\
       <span class="id" type="var">t</span>\
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

Pragmatics {.section}
==========

</div>

<div class="code code-space">

\

</div>

<div class="doc">

Side Effects and Sequencing {.section}
---------------------------

<div class="paragraph">

</div>

The fact that the result of an assignment expression is the trivial
value <span class="inlinecode"><span class="id"
type="var">unit</span></span> allows us to use a nice abbreviation for
*sequencing*. For example, we can write
           r:=succ(!r); !r

as an abbreviation for
           (\x:Unit. !r) (r := succ(!r)).

This has the effect of evaluating two expressions in order and returning
the value of the second. Restricting the type of the first expression to
<span class="inlinecode"><span class="id" type="var">Unit</span></span>
helps the typechecker to catch some silly errors by permitting us to
throw away the first value only if it is really guaranteed to be
trivial.
<div class="paragraph">

</div>

Notice that, if the second expression is also an assignment, then the
type of the whole sequence will be <span class="inlinecode"><span
class="id" type="var">Unit</span></span>, so we can validly place it to
the left of another <span class="inlinecode">;</span> to build longer
sequences of assignments:
           r:=succ(!r); r:=succ(!r); r:=succ(!r); r:=succ(!r); !r

<div class="paragraph">

</div>

Formally, we introduce sequencing as a "derived form" <span
class="inlinecode"><span class="id" type="var">tseq</span></span> that
expands into an abstraction and an application.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">tseq</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> :=\
   <span class="id" type="var">tapp</span> (<span class="id"
type="var">tabs</span> (<span class="id" type="var">Id</span> 0) <span
class="id" type="var">TUnit</span> <span class="id"
type="var">t~2~</span>) <span class="id" type="var">t~1~</span>.\
\

</div>

<div class="doc">

References and Aliasing {.section}
-----------------------

<div class="paragraph">

</div>

It is important to bear in mind the difference between the *reference*
that is bound to <span class="inlinecode"><span class="id"
type="var">r</span></span> and the *cell* in the store that is pointed
to by this reference.
<div class="paragraph">

</div>

If we make a copy of <span class="inlinecode"><span class="id"
type="var">r</span></span>, for example by binding its value to another
variable <span class="inlinecode"><span class="id"
type="var">s</span></span>, what gets copied is only the *reference*,
not the contents of the cell itself.
<div class="paragraph">

</div>

For example, after evaluating
          let r = ref 5 in
          let s = r in
          s := 82;
          (!r)+1

the cell referenced by <span class="inlinecode"><span class="id"
type="var">r</span></span> will contain the value <span
class="inlinecode">82</span>, while the result of the whole expression
will be <span class="inlinecode">83</span>. The references <span
class="inlinecode"><span class="id" type="var">r</span></span> and <span
class="inlinecode"><span class="id" type="var">s</span></span> are said
to be *aliases* for the same cell.
<div class="paragraph">

</div>

The possibility of aliasing can make programs with references quite
tricky to reason about. For example, the expression
          r := 5; r := !s

assigns <span class="inlinecode">5</span> to <span
class="inlinecode"><span class="id" type="var">r</span></span> and then
immediately overwrites it with <span class="inlinecode"><span class="id"
type="var">s</span></span>'s current value; this has exactly the same
effect as the single assignment
          r := !s

*unless* we happen to do it in a context where <span
class="inlinecode"><span class="id" type="var">r</span></span> and <span
class="inlinecode"><span class="id" type="var">s</span></span> are
aliases for the same cell!

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Shared State {.section}
------------

<div class="paragraph">

</div>

Of course, aliasing is also a large part of what makes references
useful. In particular, it allows us to set up "implicit communication
channels" — shared state — between different parts of a program. For
example, suppose we define a reference cell and two functions that
manipulate its contents:
        let c = ref 0 in
        let incc = λ_:Unit. (c := succ (!c); !c) in
        let decc = λ_:Unit. (c := pred (!c); !c) in
        ...

<div class="paragraph">

</div>

Note that, since their argument types are <span class="inlinecode"><span
class="id" type="var">Unit</span></span>, the abstractions in the
definitions of <span class="inlinecode"><span class="id"
type="var">incc</span></span> and <span class="inlinecode"><span
class="id" type="var">decc</span></span> are not providing any useful
information to the bodies of the functions (using the wildcard <span
class="inlinecode"><span class="id" type="var">\_</span></span> as the
name of the bound variable is a reminder of this). Instead, their
purpose is to "slow down" the execution of the function bodies: since
function abstractions are values, the two <span class="inlinecode"><span
class="id" type="keyword">let</span></span>s are executed simply by
binding these functions to the names <span class="inlinecode"><span
class="id" type="var">incc</span></span> and <span
class="inlinecode"><span class="id" type="var">decc</span></span>,
rather than by actually incrementing or decrementing <span
class="inlinecode"><span class="id" type="var">c</span></span>. Later,
each call to one of these functions results in its body being executed
once and performing the appropriate mutation on <span
class="inlinecode"><span class="id" type="var">c</span></span>. Such
functions are often called *thunks*.
<div class="paragraph">

</div>

In the context of these declarations, calling <span
class="inlinecode"><span class="id" type="var">incc</span></span>
results in changes to <span class="inlinecode"><span class="id"
type="var">c</span></span> that can be observed by calling <span
class="inlinecode"><span class="id" type="var">decc</span></span>. For
example, if we replace the <span class="inlinecode">...</span> with
<span class="inlinecode">(<span class="id" type="var">incc</span></span>
<span class="inlinecode"><span class="id" type="var">unit</span>;</span>
<span class="inlinecode"><span class="id" type="var">incc</span></span>
<span class="inlinecode"><span class="id" type="var">unit</span>;</span>
<span class="inlinecode"><span class="id" type="var">decc</span></span>
<span class="inlinecode"><span class="id"
type="var">unit</span>)</span>, the result of the whole program will be
<span class="inlinecode">1</span>.
Objects {.section}
-------

<div class="paragraph">

</div>

We can go a step further and write a *function* that creates <span
class="inlinecode"><span class="id" type="var">c</span></span>, <span
class="inlinecode"><span class="id" type="var">incc</span></span>, and
<span class="inlinecode"><span class="id" type="var">decc</span></span>,
packages <span class="inlinecode"><span class="id"
type="var">incc</span></span> and <span class="inlinecode"><span
class="id" type="var">decc</span></span> together into a record, and
returns this record:
        newcounter = 
            λ_:Unit.
               let c = ref 0 in
               let incc = λ_:Unit. (c := succ (!c); !c) in
               let decc = λ_:Unit. (c := pred (!c); !c) in
               {i=incc, d=decc}

Now, each time we call <span class="inlinecode"><span class="id"
type="var">newcounter</span></span>, we get a new record of functions
that share access to the same storage cell <span
class="inlinecode"><span class="id" type="var">c</span></span>. The
caller of <span class="inlinecode"><span class="id"
type="var">newcounter</span></span> can't get at this storage cell
directly, but can affect it indirectly by calling the two functions. In
other words, we've created a simple form of *object*.
        let c1 = newcounter unit in
        let c2 = newcounter unit in
        // Note that we've allocated two separate storage cells now!
        let r1 = c1.i unit in
        let r2 = c2.i unit in
        r2  // yields 1, not 2!

#### Exercise: 1 star (store\_draw) {.section}

Draw (on paper) the contents of the store at the point in execution
where the first two <span class="inlinecode"><span class="id"
type="keyword">let</span></span>s have finished and the third one is
about to begin.

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

References to Compound Types {.section}
----------------------------

<div class="paragraph">

</div>

A reference cell need not contain just a number: the primitives we've
defined above allow us to create references to values of any type,
including functions. For example, we can use references to functions to
give a (not very efficient) implementation of arrays of numbers, as
follows. Write <span class="inlinecode"><span class="id"
type="var">NatArray</span></span> for the type <span
class="inlinecode"><span class="id" type="var">Ref</span></span> <span
class="inlinecode">(<span class="id" type="var">Nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Nat</span>)</span>.
<div class="paragraph">

</div>

Recall the <span class="inlinecode"><span class="id"
type="var">equal</span></span> function from the <span
class="inlinecode"><span class="id" type="var">MoreStlc</span></span>
chapter:
        equal = 
          fix 
            (\eq:Nat->Nat->Bool.
               λm:Nat. λn:Nat.
                 if m=0 then iszero n 
                 else if n=0 then false
                 else eq (pred m) (pred n))

Now, to build a new array, we allocate a reference cell and fill it with
a function that, when given an index, always returns <span
class="inlinecode">0</span>.
        newarray = λ_:Unit. ref (\n:Nat.0)

To look up an element of an array, we simply apply the function to the
desired index.
        lookup = λa:NatArray. λn:Nat. (!a) n

The interesting part of the encoding is the <span
class="inlinecode"><span class="id" type="var">update</span></span>
function. It takes an array, an index, and a new value to be stored at
that index, and does its job by creating (and storing in the reference)
a new function that, when it is asked for the value at this very index,
returns the new value that was given to <span class="inlinecode"><span
class="id" type="var">update</span></span>, and on all other indices
passes the lookup to the function that was previously stored in the
reference.
        update = λa:NatArray. λm:Nat. λv:Nat. 
                     let oldf = !a in
                     a := (\n:Nat. if equal m n then v else oldf n);

References to values containing other references can also be very
useful, allowing us to define data structures such as mutable lists and
trees.
<div class="paragraph">

</div>

#### Exercise: 2 stars (compact\_update) {.section}

If we defined <span class="inlinecode"><span class="id"
type="var">update</span></span> more compactly like this
        update = λa:NatArray. λm:Nat. λv:Nat. 
                    a := (\n:Nat. if equal m n then v else (!a) n)

would it behave the same?

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

Null References {.section}
---------------

<div class="paragraph">

</div>

There is one more difference between our references and C-style mutable
variables: in C-like languages, variables holding pointers into the heap
may sometimes have the value <span class="inlinecode"><span class="id"
type="var">NULL</span></span>. Dereferencing such a "null pointer" is an
error, and results in an exception (Java) or in termination of the
program (C).
<div class="paragraph">

</div>

Null pointers cause significant trouble in C-like languages: the fact
that any pointer might be null means that any dereference operation in
the program can potentially fail. However, even in ML-like languages,
there are occasionally situations where we may or may not have a valid
pointer in our hands. Fortunately, there is no need to extend the basic
mechanisms of references to achieve this: the sum types introduced in
the <span class="inlinecode"><span class="id"
type="var">MoreStlc</span></span> chapter already give us what we need.
<div class="paragraph">

</div>

First, we can use sums to build an analog of the <span
class="inlinecode"><span class="id" type="var">option</span></span>
types introduced in the <span class="inlinecode"><span class="id"
type="var">Lists</span></span> chapter. Define <span
class="inlinecode"><span class="id" type="var">Option</span></span>
<span class="inlinecode"><span class="id" type="var">T</span></span> to
be an abbreviation for <span class="inlinecode"><span class="id"
type="var">Unit</span></span> <span class="inlinecode">+</span> <span
class="inlinecode"><span class="id" type="var">T</span></span>.
<div class="paragraph">

</div>

Then a "nullable reference to a <span class="inlinecode"><span
class="id" type="var">T</span></span>" is simply an element of the type
<span class="inlinecode"><span class="id"
type="var">Option</span></span> <span class="inlinecode">(<span
class="id" type="var">Ref</span></span> <span class="inlinecode"><span
class="id" type="var">T</span>)</span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Garbage Collection {.section}
------------------

<div class="paragraph">

</div>

A last issue that we should mention before we move on with formalizing
references is storage *de*-allocation. We have not provided any
primitives for freeing reference cells when they are no longer needed.
Instead, like many modern languages (including ML and Java) we rely on
the run-time system to perform *garbage collection*, collecting and
reusing cells that can no longer be reached by the program.
<div class="paragraph">

</div>

This is *not* just a question of taste in language design: it is
extremely difficult to achieve type safety in the presence of an
explicit deallocation operation. The reason for this is the familiar
*dangling reference* problem: we allocate a cell holding a number, save
a reference to it in some data structure, use it for a while, then
deallocate it and allocate a new cell holding a boolean, possibly
reusing the same storage. Now we can have two names for the same storage
cell — one with type <span class="inlinecode"><span class="id"
type="var">Ref</span></span> <span class="inlinecode"><span class="id"
type="var">Nat</span></span> and the other with type <span
class="inlinecode"><span class="id" type="var">Ref</span></span> <span
class="inlinecode"><span class="id" type="var">Bool</span></span>.
<div class="paragraph">

</div>

#### Exercise: 1 star (type\_safety\_violation) {.section}

Show how this can lead to a violation of type safety.

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

Operational Semantics {.section}
=====================

</div>

<div class="code code-space">

\

</div>

<div class="doc">

Locations {.section}
---------

<div class="paragraph">

</div>

The most subtle aspect of the treatment of references appears when we
consider how to formalize their operational behavior. One way to see why
is to ask, "What should be the *values* of type <span
class="inlinecode"><span class="id" type="var">Ref</span></span> <span
class="inlinecode"><span class="id" type="var">T</span></span>?" The
crucial observation that we need to take into account is that evaluating
a <span class="inlinecode"><span class="id" type="var">ref</span></span>
operator should *do* something — namely, allocate some storage — and the
result of the operation should be a reference to this storage.
<div class="paragraph">

</div>

What, then, is a reference?
<div class="paragraph">

</div>

The run-time store in most programming language implementations is
essentially just a big array of bytes. The run-time system keeps track
of which parts of this array are currently in use; when we need to
allocate a new reference cell, we allocate a large enough segment from
the free region of the store (4 bytes for integer cells, 8 bytes for
cells storing <span class="inlinecode"><span class="id"
type="var">Float</span></span>s, etc.), mark it as being used, and
return the index (typically, a 32- or 64-bit integer) of the start of
the newly allocated region. These indices are references.
<div class="paragraph">

</div>

For present purposes, there is no need to be quite so concrete. We can
think of the store as an array of *values*, rather than an array of
bytes, abstracting away from the different sizes of the run-time
representations of different values. A reference, then, is simply an
index into the store. (If we like, we can even abstract away from the
fact that these indices are numbers, but for purposes of formalization
in Coq it is a bit more convenient to use numbers.) We'll use the word
*location* instead of *reference* or *pointer* from now on to emphasize
this abstract quality.
<div class="paragraph">

</div>

Treating locations abstractly in this way will prevent us from modeling
the *pointer arithmetic* found in low-level languages such as C. This
limitation is intentional. While pointer arithmetic is occasionally very
useful, especially for implementing low-level services such as garbage
collectors, it cannot be tracked by most type systems: knowing that
location <span class="inlinecode"><span class="id"
type="var">n</span></span> in the store contains a <span
class="inlinecode"><span class="id" type="var">float</span></span>
doesn't tell us anything useful about the type of location <span
class="inlinecode"><span class="id" type="var">n</span>+4</span>. In C,
pointer arithmetic is a notorious source of type safety violations.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Stores {.section}
------

<div class="paragraph">

</div>

Recall that, in the small-step operational semantics for IMP, the step
relation needed to carry along an auxiliary state in addition to the
program being executed. In the same way, once we have added reference
cells to the STLC, our step relation must carry along a store to keep
track of the contents of reference cells.
<div class="paragraph">

</div>

We could re-use the same functional representation we used for states in
IMP, but for carrying out the proofs in this chapter it is actually more
convenient to represent a store simply as a *list* of values. (The
reason we couldn't use this representation before is that, in IMP, a
program could modify any location at any time, so states had to be ready
to map *any* variable to a value. However, in the STLC with references,
the only way to create a reference cell is with <span
class="inlinecode"><span class="id" type="var">tref</span></span> <span
class="inlinecode"><span class="id" type="var">t~1~</span></span>, which
puts the value of <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> in a new reference cell and evaluates to
the location of the newly created reference cell. When evaluating such
an expression, we can just add a new reference cell to the end of the
list representing the store.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">store</span> := <span class="id" type="var">list</span> <span
class="id" type="var">tm</span>.\
\

</div>

<div class="doc">

We use <span class="inlinecode"><span class="id"
type="var">store\_lookup</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode"><span
class="id" type="var">st</span></span> to retrieve the value of the
reference cell at location <span class="inlinecode"><span class="id"
type="var">n</span></span> in the store <span class="inlinecode"><span
class="id" type="var">st</span></span>. Note that we must give a default
value to <span class="inlinecode"><span class="id"
type="var">nth</span></span> in case we try looking up an index which is
too large. (In fact, we will never actually do this, but proving it will
of course require some work!)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">store\_lookup</span> (<span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>) (<span
class="id" type="var">st</span>:<span class="id"
type="var">store</span>) :=\
   <span class="id" type="var">nth</span> <span class="id"
type="var">n</span> <span class="id" type="var">st</span> <span
class="id" type="var">tunit</span>.\
\

</div>

<div class="doc">

To add a new reference cell to the store, we use <span
class="inlinecode"><span class="id" type="var">snoc</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">snoc</span> {<span class="id" type="var">A</span>:<span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">l</span>:<span class="id" type="var">list</span> <span
class="id" type="var">A</span>) (<span class="id"
type="var">x</span>:<span class="id" type="var">A</span>) : <span
class="id" type="var">list</span> <span class="id" type="var">A</span>
:=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">x</span> :: <span class="id" type="var">nil</span>\
   | <span class="id" type="var">h</span> :: <span class="id"
type="var">t</span> ⇒ <span class="id" type="var">h</span> :: <span
class="id" type="var">snoc</span> <span class="id" type="var">t</span>
<span class="id" type="var">x</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

We will need some boring lemmas about <span class="inlinecode"><span
class="id" type="var">snoc</span></span>. The proofs are routine
inductions.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">length\_snoc</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">A</span>
(<span class="id" type="var">l</span>:<span class="id"
type="var">list</span> <span class="id" type="var">A</span>) <span
class="id" type="var">x</span>,\
   <span class="id" type="var">length</span> (<span class="id"
type="var">snoc</span> <span class="id" type="var">l</span> <span
class="id" type="var">x</span>) = <span class="id" type="var">S</span>
(<span class="id" type="var">length</span> <span class="id"
type="var">l</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">l</span>; <span class="id" type="tactic">intros</span>; [
<span class="id" type="tactic">auto</span> | <span class="id"
type="tactic">simpl</span>; <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHl</span>;
<span class="id" type="tactic">auto</span> ]. <span class="id"
type="keyword">Qed</span>.\
\
 <span
class="comment">(\* The "solve by inversion" tactic is explained in Stlc.v. \*)</span>\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">nth\_lt\_snoc</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">A</span>
(<span class="id" type="var">l</span>:<span class="id"
type="var">list</span> <span class="id" type="var">A</span>) <span
class="id" type="var">x</span> <span class="id" type="var">d</span>
<span class="id" type="var">n</span>,\
   <span class="id" type="var">n</span> \< <span class="id"
type="var">length</span> <span class="id" type="var">l</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">nth</span> <span class="id"
type="var">n</span> <span class="id" type="var">l</span> <span
class="id" type="var">d</span> = <span class="id" type="var">nth</span>
<span class="id" type="var">n</span> (<span class="id"
type="var">snoc</span> <span class="id" type="var">l</span> <span
class="id" type="var">x</span>) <span class="id" type="var">d</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">a</span> <span class="id" type="var">l'</span>];
<span class="id" type="tactic">intros</span>; <span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
   <span class="id" type="var">Case</span> "l = a :: l'".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">n</span>; <span class="id" type="tactic">auto</span>.\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHl'</span>.\
     <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">lt\_S\_n</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H</span>. <span class="id"
type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">nth\_eq\_snoc</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">A</span>
(<span class="id" type="var">l</span>:<span class="id"
type="var">list</span> <span class="id" type="var">A</span>) <span
class="id" type="var">x</span> <span class="id" type="var">d</span>,\
   <span class="id" type="var">nth</span> (<span class="id"
type="var">length</span> <span class="id" type="var">l</span>) (<span
class="id" type="var">snoc</span> <span class="id" type="var">l</span>
<span class="id" type="var">x</span>) <span class="id"
type="var">d</span> = <span class="id" type="var">x</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">l</span>; <span class="id" type="tactic">intros</span>; [
<span class="id" type="tactic">auto</span> | <span class="id"
type="tactic">simpl</span>; <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHl</span>;
<span class="id" type="tactic">auto</span> ].\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

To update the store, we use the <span class="inlinecode"><span
class="id" type="tactic">replace</span></span> function, which replaces
the contents of a cell at a particular index.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="tactic">replace</span> {<span class="id" type="var">A</span>:<span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>) (<span
class="id" type="var">x</span>:<span class="id" type="var">A</span>)
(<span class="id" type="var">l</span>:<span class="id"
type="var">list</span> <span class="id" type="var">A</span>) : <span
class="id" type="var">list</span> <span class="id" type="var">A</span>
:=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">nil</span>\
   | <span class="id" type="var">h</span> :: <span class="id"
type="var">t</span> ⇒\
     <span class="id" type="keyword">match</span> <span class="id"
type="var">n</span> <span class="id" type="keyword">with</span>\
     | <span class="id" type="var">O</span> ⇒ <span class="id"
type="var">x</span> :: <span class="id" type="var">t</span>\
     | <span class="id" type="var">S</span> <span class="id"
type="var">n'</span> ⇒ <span class="id" type="var">h</span> :: <span
class="id" type="tactic">replace</span> <span class="id"
type="var">n'</span> <span class="id" type="var">x</span> <span
class="id" type="var">t</span>\
     <span class="id" type="keyword">end</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Of course, we also need some boring lemmas about <span
class="inlinecode"><span class="id" type="tactic">replace</span></span>,
which are also fairly straightforward to prove.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">replace\_nil</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">A</span>
<span class="id" type="var">n</span> (<span class="id"
type="var">x</span>:<span class="id" type="var">A</span>),\
   <span class="id" type="tactic">replace</span> <span class="id"
type="var">n</span> <span class="id" type="var">x</span> <span
class="id" type="var">nil</span> = <span class="id"
type="var">nil</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">n</span>; <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">length\_replace</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">A</span>
<span class="id" type="var">n</span> <span class="id"
type="var">x</span> (<span class="id" type="var">l</span>:<span
class="id" type="var">list</span> <span class="id"
type="var">A</span>),\
   <span class="id" type="var">length</span> (<span class="id"
type="tactic">replace</span> <span class="id" type="var">n</span> <span
class="id" type="var">x</span> <span class="id" type="var">l</span>) =
<span class="id" type="var">length</span> <span class="id"
type="var">l</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">A</span> <span class="id" type="var">n</span> <span
class="id" type="var">x</span> <span class="id" type="var">l</span>.
<span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">n</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">l</span>; <span class="id" type="tactic">intros</span> <span
class="id" type="var">n</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">n</span>...\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">n</span>...\
       <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHl</span>...\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">lookup\_replace\_eq</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">l</span>
<span class="id" type="var">t</span> <span class="id"
type="var">st</span>,\
   <span class="id" type="var">l</span> \< <span class="id"
type="var">length</span> <span class="id" type="var">st</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_lookup</span> <span class="id"
type="var">l</span> (<span class="id" type="tactic">replace</span> <span
class="id" type="var">l</span> <span class="id" type="var">t</span>
<span class="id" type="var">st</span>) = <span class="id"
type="var">t</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">l</span> <span class="id" type="var">t</span> <span
class="id" type="var">st</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">store\_lookup</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">l</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">st</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">t'</span> <span class="id" type="var">st'</span>];
<span class="id" type="tactic">intros</span> <span class="id"
type="var">l</span> <span class="id" type="var">Hlen</span>.\
   <span class="id" type="var">Case</span> "st = []".\
    <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hlen</span>.\
   <span class="id" type="var">Case</span> "st = t' :: st'".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">l</span>; <span class="id" type="tactic">simpl</span>...\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHst'</span>. <span class="id" type="tactic">simpl</span>
<span class="id" type="keyword">in</span> <span class="id"
type="var">Hlen</span>. <span class="id" type="tactic">omega</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">lookup\_replace\_neq</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l1</span> <span class="id" type="var">l2</span> <span
class="id" type="var">t</span> <span class="id" type="var">st</span>,\
   <span class="id" type="var">l1</span> ≠ <span class="id"
type="var">l2</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_lookup</span> <span class="id"
type="var">l1</span> (<span class="id" type="tactic">replace</span>
<span class="id" type="var">l2</span> <span class="id"
type="var">t</span> <span class="id" type="var">st</span>) = <span
class="id" type="var">store\_lookup</span> <span class="id"
type="var">l1</span> <span class="id" type="var">st</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">store\_lookup</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">l1</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">l1'</span>]; <span class="id"
type="tactic">intros</span> <span class="id" type="var">l2</span> <span
class="id" type="var">t</span> <span class="id" type="var">st</span>
<span class="id" type="var">Hneq</span>.\
   <span class="id" type="var">Case</span> "l1 = 0".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">st</span>.\
     <span class="id" type="var">SCase</span> "st = []". <span
class="id" type="tactic">rewrite</span> <span class="id"
type="var">replace\_nil</span>...\
     <span class="id" type="var">SCase</span> "st = \_ :: \_". <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">l2</span>... <span class="id" type="var">contradict</span>
<span class="id" type="var">Hneq</span>...\
   <span class="id" type="var">Case</span> "l1 = S l1'".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">st</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">t~2~</span> <span class="id"
type="var">st2</span>].\
     <span class="id" type="var">SCase</span> "st = []". <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">l2</span>...\
     <span class="id" type="var">SCase</span> "st = t~2~ :: st2".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">l2</span>...\
       <span class="id" type="tactic">simpl</span>; <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHl1'</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Reduction {.section}
---------

<div class="paragraph">

</div>

Next, we need to extend our operational semantics to take stores into
account. Since the result of evaluating an expression will in general
depend on the contents of the store in which it is evaluated, the
evaluation rules should take not just a term but also a store as
argument. Furthermore, since the evaluation of a term may cause side
effects on the store that may affect the evaluation of other terms in
the future, the evaluation rules need to return a new store. Thus, the
shape of the single-step evaluation relation changes from <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span>
<span class="inlinecode"><span class="id" type="var">t'</span></span> to
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">/</span> <span class="inlinecode"><span
class="id" type="var">st</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> <span
class="inlinecode">/</span> <span class="inlinecode"><span class="id"
type="var">st'</span></span>, where <span class="inlinecode"><span
class="id" type="var">st</span></span> and <span
class="inlinecode"><span class="id" type="var">st'</span></span> are the
starting and ending states of the store.
<div class="paragraph">

</div>

To carry through this change, we first need to augment all of our
existing evaluation rules with stores:
value v~2~
(ST\_AppAbs)  

------------------------------------------------------------------------

(\\x:T.t~12~) v~2~ / st <span
style="font-family: arial;">⇒</span> [x:=v~2~]t~12~ / st
t~1~ / st <span style="font-family: arial;">⇒</span> t~1~' / st'
(ST\_App1)  

------------------------------------------------------------------------

t~1~ t~2~ / st <span
style="font-family: arial;">⇒</span> t~1~' t~2~ / st'
value v~1~     t~2~ / st <span
style="font-family: arial;">⇒</span> t~2~' / st'
(ST\_App2)  

------------------------------------------------------------------------

v~1~ t~2~ / st <span
style="font-family: arial;">⇒</span> v~1~ t~2~' / st'
Note that the first rule here returns the store unchanged: function
application, in itself, has no side effects. The other two rules simply
propagate side effects from premise to conclusion.
<div class="paragraph">

</div>

Now, the result of evaluating a <span class="inlinecode"><span
class="id" type="var">ref</span></span> expression will be a fresh
location; this is why we included locations in the syntax of terms and
in the set of values.
<div class="paragraph">

</div>

It is crucial to note that making this extension to the syntax of terms
does not mean that we intend *programmers* to write terms involving
explicit, concrete locations: such terms will arise only as intermediate
results of evaluation. This may initially seem odd, but really it
follows naturally from our design decision to represent the result of
every evaluation step by a modified term. If we had chosen a more
"machine-like" model for evaluation, e.g. with an explicit stack to
contain values of bound identifiers, then the idea of adding locations
to the set of allowed values would probably seem more obvious.
<div class="paragraph">

</div>

In terms of this expanded syntax, we can state evaluation rules for the
new constructs that manipulate locations and the store. First, to
evaluate a dereferencing expression <span class="inlinecode">!<span
class="id" type="var">t~1~</span></span>, we must first reduce <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> until
it becomes a value:
t~1~ / st <span style="font-family: arial;">⇒</span> t~1~' / st'
(ST\_Deref)  

------------------------------------------------------------------------

!t~1~ / st <span style="font-family: arial;">⇒</span> !t~1~' / st'
Once <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> has finished reducing, we should have an
expression of the form <span class="inlinecode">!<span class="id"
type="var">l</span></span>, where <span class="inlinecode"><span
class="id" type="var">l</span></span> is some location. (A term that
attempts to dereference any other sort of value, such as a function or
<span class="inlinecode"><span class="id" type="var">unit</span></span>,
is erroneous, as is a term that tries to derefence a location that is
larger than the size <span class="inlinecode">|<span class="id"
type="var">st</span>|</span> of the currently allocated store; the
evaluation rules simply get stuck in this case. The type safety
properties that we'll establish below assure us that well-typed terms
will never misbehave in this way.)
l \< |st|
(ST\_DerefLoc)  

------------------------------------------------------------------------

!(loc l) / st <span
style="font-family: arial;">⇒</span> lookup l st / st
<div class="paragraph">

</div>

Next, to evaluate an assignment expression <span
class="inlinecode"><span class="id" type="var">t~1~</span>:=<span
class="id" type="var">t~2~</span></span>, we must first evaluate <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> until
it becomes a value (a location), and then evaluate <span
class="inlinecode"><span class="id" type="var">t~2~</span></span> until
it becomes a value (of any sort):
t~1~ / st <span style="font-family: arial;">⇒</span> t~1~' / st'
(ST\_Assign1)  

------------------------------------------------------------------------

t~1~ := t~2~ / st <span
style="font-family: arial;">⇒</span> t~1~' := t~2~ / st'
t~2~ / st <span style="font-family: arial;">⇒</span> t~2~' / st'
(ST\_Assign2)  

------------------------------------------------------------------------

v~1~ := t~2~ / st <span
style="font-family: arial;">⇒</span> v~1~ := t~2~' / st'
Once we have finished with <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> and <span class="inlinecode"><span
class="id" type="var">t~2~</span></span>, we have an expression of the
form <span class="inlinecode"><span class="id"
type="var">l</span>:=<span class="id" type="var">v~2~</span></span>,
which we execute by updating the store to make location <span
class="inlinecode"><span class="id" type="var">l</span></span> contain
<span class="inlinecode"><span class="id" type="var">v~2~</span></span>:
l \< |st|
(ST\_Assign)  

------------------------------------------------------------------------

loc l := v~2~ / st <span
style="font-family: arial;">⇒</span> unit / [l:=v~2~]st
The notation <span class="inlinecode">[<span class="id"
type="var">l</span>:=<span class="id" type="var">v~2~</span>]<span
class="id" type="var">st</span></span> means "the store that maps <span
class="inlinecode"><span class="id" type="var">l</span></span> to <span
class="inlinecode"><span class="id" type="var">v~2~</span></span> and
maps all other locations to the same thing as <span
class="inlinecode"><span class="id" type="var">st</span>.</span>" Note
that the term resulting from this evaluation step is just <span
class="inlinecode"><span class="id" type="var">unit</span></span>; the
interesting result is the updated store.)
<div class="paragraph">

</div>

Finally, to evaluate an expression of the form <span
class="inlinecode"><span class="id" type="var">ref</span></span> <span
class="inlinecode"><span class="id" type="var">t~1~</span></span>, we
first evaluate <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> until it becomes a value:
t~1~ / st <span style="font-family: arial;">⇒</span> t~1~' / st'
(ST\_Ref)  

------------------------------------------------------------------------

ref t~1~ / st <span style="font-family: arial;">⇒</span> ref t~1~' / st'
Then, to evaluate the <span class="inlinecode"><span class="id"
type="var">ref</span></span> itself, we choose a fresh location at the
end of the current store — i.e., location <span
class="inlinecode">|<span class="id" type="var">st</span>|</span> — and
yield a new store that extends <span class="inlinecode"><span class="id"
type="var">st</span></span> with the new value <span
class="inlinecode"><span class="id" type="var">v~1~</span></span>.
  
(ST\_RefValue)  

------------------------------------------------------------------------

ref v~1~ / st <span
style="font-family: arial;">⇒</span> loc |st| / st,v~1~
The value resulting from this step is the newly allocated location
itself. (Formally, <span class="inlinecode"><span class="id"
type="var">st</span>,<span class="id" type="var">v~1~</span></span>
means <span class="inlinecode"><span class="id"
type="var">snoc</span></span> <span class="inlinecode"><span class="id"
type="var">st</span></span> <span class="inlinecode"><span class="id"
type="var">v~1~</span></span>.)
<div class="paragraph">

</div>

Note that these evaluation rules do not perform any kind of garbage
collection: we simply allow the store to keep growing without bound as
evaluation proceeds. This does not affect the correctness of the results
of evaluation (after all, the definition of "garbage" is precisely parts
of the store that are no longer reachable and so cannot play any further
role in evaluation), but it means that a naive implementation of our
evaluator might sometimes run out of memory where a more sophisticated
evaluator would be able to continue by reusing locations whose contents
have become garbage.
<div class="paragraph">

</div>

Formally...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> "t~1~ '/' st1
'<span style="font-family: arial;">⇒</span>' t~2~ '/' st2"\
   (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 40, <span class="id" type="var">st1</span> <span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 39, <span class="id" type="var">t~2~</span>
<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 39).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">step</span> : <span class="id" type="var">tm</span> × <span
class="id" type="var">store</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> × <span class="id" type="var">store</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">ST\_AppAbs</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">T</span> <span class="id"
type="var">t~12~</span> <span class="id" type="var">v~2~</span> <span
class="id" type="var">st</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~2~</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tapp</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T</span> <span class="id" type="var">t~12~</span>)
<span class="id" type="var">v~2~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> [<span
class="id" type="var">x</span>:=<span class="id"
type="var">v~2~</span>]<span class="id" type="var">t~12~</span> / <span
class="id" type="var">st</span>\
   | <span class="id" type="var">ST\_App1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">st</span>
<span class="id" type="var">st'</span>,\
          <span class="id" type="var">t~1~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~1~'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> / <span class="id"
type="var">st'</span>\
   | <span class="id" type="var">ST\_App2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span> <span class="id" type="var">st</span>
<span class="id" type="var">st'</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">t~2~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~2~'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tapp</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tapp</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>/ <span class="id"
type="var">st'</span>\
   | <span class="id" type="var">ST\_SuccNat</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">st</span>,\
          <span class="id" type="var">tsucc</span> (<span class="id"
type="var">tnat</span> <span class="id" type="var">n</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tnat</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>) / <span class="id" type="var">st</span>\
   | <span class="id" type="var">ST\_Succ</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>,\
          <span class="id" type="var">t~1~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~1~'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tsucc</span> <span class="id"
type="var">t~1~</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tsucc</span> <span class="id" type="var">t~1~'</span> / <span
class="id" type="var">st'</span>\
   | <span class="id" type="var">ST\_PredNat</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">st</span>,\
          <span class="id" type="var">tpred</span> (<span class="id"
type="var">tnat</span> <span class="id" type="var">n</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tnat</span> (<span class="id" type="var">pred</span> <span
class="id" type="var">n</span>) / <span class="id" type="var">st</span>\
   | <span class="id" type="var">ST\_Pred</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>,\
          <span class="id" type="var">t~1~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~1~'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tpred</span> <span class="id"
type="var">t~1~</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tpred</span> <span class="id" type="var">t~1~'</span> / <span
class="id" type="var">st'</span>\
   | <span class="id" type="var">ST\_MultNats</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n1</span> <span class="id" type="var">n2</span> <span
class="id" type="var">st</span>,\
          <span class="id" type="var">tmult</span> (<span class="id"
type="var">tnat</span> <span class="id" type="var">n1</span>) (<span
class="id" type="var">tnat</span> <span class="id" type="var">n2</span>)
/ <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tnat</span> (<span class="id" type="var">mult</span> <span
class="id" type="var">n1</span> <span class="id" type="var">n2</span>) /
<span class="id" type="var">st</span>\
   | <span class="id" type="var">ST\_Mult1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~1~'</span> <span class="id" type="var">st</span>
<span class="id" type="var">st'</span>,\
          <span class="id" type="var">t~1~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~1~'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tmult</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tmult</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> / <span class="id"
type="var">st'</span>\
   | <span class="id" type="var">ST\_Mult2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span> <span class="id" type="var">st</span>
<span class="id" type="var">st'</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">t~2~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~2~'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tmult</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tmult</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span> / <span class="id"
type="var">st'</span>\
   | <span class="id" type="var">ST\_If0</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span>,\
          <span class="id" type="var">t~1~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~1~'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tif0</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">tif0</span> <span class="id"
type="var">t~1~'</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> / <span class="id"
type="var">st'</span>\
   | <span class="id" type="var">ST\_If0\_Zero</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span> <span
class="id" type="var">st</span>,\
          <span class="id" type="var">tif0</span> (<span class="id"
type="var">tnat</span> 0) <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~2~</span> / <span class="id"
type="var">st</span>\
   | <span class="id" type="var">ST\_If0\_Nonzero</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span> <span class="id" type="var">st</span>,\
          <span class="id" type="var">tif0</span> (<span class="id"
type="var">tnat</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>)) <span class="id" type="var">t~2~</span>
<span class="id" type="var">t~3~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~3~</span> / <span class="id"
type="var">st</span>\
   | <span class="id" type="var">ST\_RefValue</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">st</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tref</span> <span class="id"
type="var">v~1~</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tloc</span> (<span class="id" type="var">length</span> <span
class="id" type="var">st</span>) / <span class="id"
type="var">snoc</span> <span class="id" type="var">st</span> <span
class="id" type="var">v~1~</span>\
   | <span class="id" type="var">ST\_Ref</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>,\
          <span class="id" type="var">t~1~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~1~'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tref</span> <span class="id"
type="var">t~1~</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tref</span> <span class="id" type="var">t~1~'</span> / <span
class="id" type="var">st'</span>\
   | <span class="id" type="var">ST\_DerefLoc</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span> <span class="id" type="var">l</span>,\
          <span class="id" type="var">l</span> \< <span class="id"
type="var">length</span> <span class="id" type="var">st</span> <span
style="font-family: arial;">→</span>\
          <span class="id" type="var">tderef</span> (<span class="id"
type="var">tloc</span> <span class="id" type="var">l</span>) / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">store\_lookup</span> <span class="id" type="var">l</span>
<span class="id" type="var">st</span> / <span class="id"
type="var">st</span>\
   | <span class="id" type="var">ST\_Deref</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>,\
          <span class="id" type="var">t~1~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~1~'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tderef</span> <span class="id"
type="var">t~1~</span> / <span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tderef</span> <span class="id" type="var">t~1~'</span> /
<span class="id" type="var">st'</span>\
   | <span class="id" type="var">ST\_Assign</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~2~</span> <span class="id" type="var">l</span> <span
class="id" type="var">st</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~2~</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">l</span> \< <span class="id"
type="var">length</span> <span class="id" type="var">st</span> <span
style="font-family: arial;">→</span>\
          <span class="id" type="var">tassign</span> (<span class="id"
type="var">tloc</span> <span class="id" type="var">l</span>) <span
class="id" type="var">v~2~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">tunit</span> / <span class="id"
type="tactic">replace</span> <span class="id" type="var">l</span> <span
class="id" type="var">v~2~</span> <span class="id" type="var">st</span>\
   | <span class="id" type="var">ST\_Assign1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">st</span>
<span class="id" type="var">st'</span>,\
          <span class="id" type="var">t~1~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~1~'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tassign</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tassign</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> / <span class="id"
type="var">st'</span>\
   | <span class="id" type="var">ST\_Assign2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span> <span class="id" type="var">st</span>
<span class="id" type="var">st'</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">t~2~</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t~2~'</span> / <span class="id"
type="var">st'</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">tassign</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> / <span
class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tassign</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span> / <span class="id"
type="var">st'</span>\
\
 <span class="id" type="keyword">where</span> "t~1~ '/' st1 '<span
style="font-family: arial;">⇒</span>' t~2~ '/' st2" := (<span class="id"
type="var">step</span> (<span class="id" type="var">t~1~</span>,<span
class="id" type="var">st1</span>) (<span class="id"
type="var">t~2~</span>,<span class="id" type="var">st2</span>)).\
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
"ST\_SuccNat"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Succ" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_PredNat"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Pred" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_MultNats"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Mult1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Mult2"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_If0" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_If0\_Zero"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_If0\_Nonzero" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_RefValue"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Ref" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_DerefLoc"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Deref" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Assign"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Assign1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Assign2" ].\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id" type="var">step</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">multistep</span> := (<span class="id" type="var">multi</span>
<span class="id" type="var">step</span>).\
 <span class="id" type="keyword">Notation</span> "t~1~ '/' st '<span
style="font-family: arial;">⇒\*</span>' t~2~ '/' st'" := (<span
class="id" type="var">multistep</span> (<span class="id"
type="var">t~1~</span>,<span class="id" type="var">st</span>) (<span
class="id" type="var">t~2~</span>,<span class="id"
type="var">st'</span>))\
   (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 40, <span class="id" type="var">st</span> <span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 39, <span class="id" type="var">t~2~</span>
<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 39).\
\

</div>

<div class="doc">

Typing {.section}
======

<div class="paragraph">

</div>

Our contexts for free variables will be exactly the same as for the
STLC, partial maps from identifiers to types.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">context</span> := <span class="id"
type="var">partial\_map</span> <span class="id" type="var">ty</span>.\
\
\

</div>

<div class="doc">

Store typings {.section}
-------------

<div class="paragraph">

</div>

Having extended our syntax and evaluation rules to accommodate
references, our last job is to write down typing rules for the new
constructs — and, of course, to check that they are sound. Naturally,
the key question is, "What is the type of a location?"
<div class="paragraph">

</div>

First of all, notice that we do *not* need to answer this question for
purposes of typechecking the terms that programmers actually write.
Concrete location constants arise only in terms that are the
intermediate results of evaluation; they are not in the language that
programmers write. So we only need to determine the type of a location
when we're in the middle of an evaluation sequence, e.g. trying to apply
the progress or preservation lemmas. Thus, even though we normally think
of typing as a *static* program property, it makes sense for the typing
of locations to depend on the *dynamic* progress of the program too.
<div class="paragraph">

</div>

As a first try, note that when we evaluate a term containing concrete
locations, the type of the result depends on the contents of the store
that we start with. For example, if we evaluate the term <span
class="inlinecode">!(<span class="id" type="var">loc</span></span> <span
class="inlinecode">1)</span> in the store <span
class="inlinecode">[<span class="id" type="var">unit</span>,</span>
<span class="inlinecode"><span class="id"
type="var">unit</span>]</span>, the result is <span
class="inlinecode"><span class="id" type="var">unit</span></span>; if we
evaluate the same term in the store <span class="inlinecode">[<span
class="id" type="var">unit</span>,</span> <span
class="inlinecode">\\<span class="id" type="var">x</span>:<span
class="id" type="var">Unit.x</span>]</span>, the result is <span
class="inlinecode">\\<span class="id" type="var">x</span>:<span
class="id" type="var">Unit.x</span></span>. With respect to the former
store, the location <span class="inlinecode">1</span> has type <span
class="inlinecode"><span class="id" type="var">Unit</span></span>, and
with respect to the latter it has type <span class="inlinecode"><span
class="id" type="var">Unit</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Unit</span></span>. This observation leads us immediately to
a first attempt at a typing rule for locations:
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> lookup  l st : T~1~
 

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> loc l : Ref T~1~
That is, to find the type of a location <span class="inlinecode"><span
class="id" type="var">l</span></span>, we look up the current contents
of <span class="inlinecode"><span class="id" type="var">l</span></span>
in the store and calculate the type <span class="inlinecode"><span
class="id" type="var">T~1~</span></span> of the contents. The type of
the location is then <span class="inlinecode"><span class="id"
type="var">Ref</span></span> <span class="inlinecode"><span class="id"
type="var">T~1~</span></span>.
<div class="paragraph">

</div>

Having begun in this way, we need to go a little further to reach a
consistent state. In effect, by making the type of a term depend on the
store, we have changed the typing relation from a three-place relation
(between contexts, terms, and types) to a four-place relation (between
contexts, *stores*, terms, and types). Since the store is, intuitively,
part of the context in which we calculate the type of a term, let's
write this four-place relation with the store to the left of the
turnstile: <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>;</span> <span
class="inlinecode"><span class="id" type="var">st</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>. Our rule for typing references
now has the form
Gamma; st <span style="font-family: arial;">⊢</span> lookup l st : T~1~
 

------------------------------------------------------------------------

Gamma; st <span style="font-family: arial;">⊢</span> loc l : Ref T~1~
and all the rest of the typing rules in the system are extended
similarly with stores. The other rules do not need to do anything
interesting with their stores — just pass them from premise to
conclusion.
<div class="paragraph">

</div>

However, there are two problems with this rule. First, typechecking is
rather inefficient, since calculating the type of a location <span
class="inlinecode"><span class="id" type="var">l</span></span> involves
calculating the type of the current contents <span
class="inlinecode"><span class="id" type="var">v</span></span> of <span
class="inlinecode"><span class="id" type="var">l</span></span>. If <span
class="inlinecode"><span class="id" type="var">l</span></span> appears
many times in a term <span class="inlinecode"><span class="id"
type="var">t</span></span>, we will re-calculate the type of <span
class="inlinecode"><span class="id" type="var">v</span></span> many
times in the course of constructing a typing derivation for <span
class="inlinecode"><span class="id" type="var">t</span></span>. Worse,
if <span class="inlinecode"><span class="id" type="var">v</span></span>
itself contains locations, then we will have to recalculate *their*
types each time they appear.
<div class="paragraph">

</div>

Second, the proposed typing rule for locations may not allow us to
derive anything at all, if the store contains a *cycle*. For example,
there is no finite typing derivation for the location <span
class="inlinecode">0</span> with respect to this store:
       [\x:Nat. (!(loc 1)) x, λx:Nat. (!(loc 0)) x]

#### Exercise: 2 stars (cyclic\_store) {.section}

Can you find a term whose evaluation will create this particular cyclic
store?
<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

Both of these problems arise from the fact that our proposed typing rule
for locations requires us to recalculate the type of a location every
time we mention it in a term. But this, intuitively, should not be
necessary. After all, when a location is first created, we know the type
of the initial value that we are storing into it. Suppose we are willing
to enforce the invariant that the type of the value contained in a given
location *never changes*; that is, although we may later store other
values into this location, those other values will always have the same
type as the initial one. In other words, we always have in mind a
single, definite type for every location in the store, which is fixed
when the location is allocated. Then these intended types can be
collected together as a *store typing* —-a finite function mapping
locations to types.
<div class="paragraph">

</div>

As usual, this *conservative* typing restriction on allowed updates
means that we will rule out as ill-typed some programs that could
evaluate perfectly well without getting stuck.
<div class="paragraph">

</div>

Just like we did for stores, we will represent a store type simply as a
list of types: the type at index <span class="inlinecode"><span
class="id" type="var">i</span></span> records the type of the value
stored in cell <span class="inlinecode"><span class="id"
type="var">i</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">store\_ty</span> := <span class="id" type="var">list</span>
<span class="id" type="var">ty</span>.\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="var">store\_Tlookup</span></span> function retrieves the type at a
particular index.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">store\_Tlookup</span> (<span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>) (<span
class="id" type="var">ST</span>:<span class="id"
type="var">store\_ty</span>) :=\
   <span class="id" type="var">nth</span> <span class="id"
type="var">n</span> <span class="id" type="var">ST</span> <span
class="id" type="var">TUnit</span>.\
\

</div>

<div class="doc">

Suppose we are *given* a store typing <span class="inlinecode"><span
class="id" type="var">ST</span></span> describing the store <span
class="inlinecode"><span class="id" type="var">st</span></span> in which
some term <span class="inlinecode"><span class="id"
type="var">t</span></span> will be evaluated. Then we can use <span
class="inlinecode"><span class="id" type="var">ST</span></span> to
calculate the type of the result of <span class="inlinecode"><span
class="id" type="var">t</span></span> without ever looking directly at
<span class="inlinecode"><span class="id" type="var">st</span></span>.
For example, if <span class="inlinecode"><span class="id"
type="var">ST</span></span> is <span class="inlinecode">[<span
class="id" type="var">Unit</span>,</span> <span class="inlinecode"><span
class="id" type="var">Unit</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Unit</span>]</span>, then we may immediately infer that <span
class="inlinecode">!(<span class="id" type="var">loc</span></span> <span
class="inlinecode">1)</span> has type <span class="inlinecode"><span
class="id" type="var">Unit</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Unit</span></span>. More generally, the typing rule for
locations can be reformulated in terms of store typings like this:
l \< |ST|
 

------------------------------------------------------------------------

Gamma; ST <span
style="font-family: arial;">⊢</span> loc l : Ref (lookup l ST)
<div class="paragraph">

</div>

That is, as long as <span class="inlinecode"><span class="id"
type="var">l</span></span> is a valid location (it is less than the
length of <span class="inlinecode"><span class="id"
type="var">ST</span></span>), we can compute the type of <span
class="inlinecode"><span class="id" type="var">l</span></span> just by
looking it up in <span class="inlinecode"><span class="id"
type="var">ST</span></span>. Typing is again a four-place relation, but
it is parameterized on a store *typing* rather than a concrete store.
The rest of the typing rules are analogously augmented with store
typings.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

The Typing Relation {.section}
-------------------

<div class="paragraph">

</div>

We can now give the typing relation for the STLC with references. Here,
again, are the rules we're adding to the base STLC (with numbers and
<span class="inlinecode"><span class="id"
type="var">Unit</span></span>):
<div class="paragraph">

</div>

<div class="paragraph">

</div>

l \< |ST|
(T\_Loc)  

------------------------------------------------------------------------

Gamma; ST <span
style="font-family: arial;">⊢</span> loc l : Ref (lookup l ST)
Gamma; ST <span style="font-family: arial;">⊢</span> t~1~ : T~1~
(T\_Ref)  

------------------------------------------------------------------------

Gamma; ST <span style="font-family: arial;">⊢</span> ref t~1~ : Ref T~1~
Gamma; ST <span style="font-family: arial;">⊢</span> t~1~ : Ref T~11~
(T\_Deref)  

------------------------------------------------------------------------

Gamma; ST <span style="font-family: arial;">⊢</span> !t~1~ : T~11~
Gamma; ST <span style="font-family: arial;">⊢</span> t~1~ : Ref T~11~
Gamma; ST <span style="font-family: arial;">⊢</span> t~2~ : T~11~
(T\_Assign)  

------------------------------------------------------------------------

Gamma; ST <span style="font-family: arial;">⊢</span> t~1~ := t~2~ : Unit

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> "Gamma ';' ST
'<span style="font-family: arial;">⊢</span>' t '∈' T" (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">has\_type</span> : <span class="id" type="var">context</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">store\_ty</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">T\_Var</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">x</span> <span
class="id" type="var">T</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
class="id" type="var">x</span> = <span class="id" type="var">Some</span>
<span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) ∈ <span
class="id" type="var">T</span>\
   | <span class="id" type="var">T\_Abs</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">T~12~</span> <span class="id" type="var">t~12~</span>,\
       (<span class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T~11~</span>); <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~12~</span> ∈ <span class="id" type="var">T~12~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>) ∈ (<span class="id" type="var">TArrow</span>
<span class="id" type="var">T~11~</span> <span class="id"
type="var">T~12~</span>)\
   | <span class="id" type="var">T\_App</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ (<span class="id" type="var">TArrow</span>
<span class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) ∈ <span class="id"
type="var">T~2~</span>\
   | <span class="id" type="var">T\_Nat</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">n</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tnat</span> <span class="id" type="var">n</span>) ∈ <span
class="id" type="var">TNat</span>\
   | <span class="id" type="var">T\_Succ</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t~1~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tsucc</span> <span class="id" type="var">t~1~</span>) ∈ <span
class="id" type="var">TNat</span>\
   | <span class="id" type="var">T\_Pred</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t~1~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tpred</span> <span class="id" type="var">t~1~</span>) ∈ <span
class="id" type="var">TNat</span>\
   | <span class="id" type="var">T\_Mult</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tmult</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) ∈ <span class="id"
type="var">TNat</span>\
   | <span class="id" type="var">T\_If0</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span> <span class="id" type="var">T</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TNat</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~3~</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tif0</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>) ∈ <span class="id" type="var">T</span>\
   | <span class="id" type="var">T\_Unit</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tunit</span> ∈ <span class="id" type="var">TUnit</span>\
   | <span class="id" type="var">T\_Loc</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">l</span>,\
       <span class="id" type="var">l</span> \< <span class="id"
type="var">length</span> <span class="id" type="var">ST</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tloc</span> <span class="id" type="var">l</span>) ∈ (<span
class="id" type="var">TRef</span> (<span class="id"
type="var">store\_Tlookup</span> <span class="id" type="var">l</span>
<span class="id" type="var">ST</span>))\
   | <span class="id" type="var">T\_Ref</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">T~1~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tref</span> <span class="id" type="var">t~1~</span>) ∈ (<span
class="id" type="var">TRef</span> <span class="id"
type="var">T~1~</span>)\
   | <span class="id" type="var">T\_Deref</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">T~11~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ (<span class="id" type="var">TRef</span> <span
class="id" type="var">T~11~</span>) <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tderef</span> <span class="id" type="var">t~1~</span>) ∈
<span class="id" type="var">T~11~</span>\
   | <span class="id" type="var">T\_Assign</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">T~11~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ (<span class="id" type="var">TRef</span> <span
class="id" type="var">T~11~</span>) <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T~11~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tassign</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) ∈ <span class="id"
type="var">TUnit</span>\
\
 <span class="id" type="keyword">where</span> "Gamma ';' ST '<span
style="font-family: arial;">⊢</span>' t '∈' T" := (<span class="id"
type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span>).\
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
type="var">c</span> "T\_Nat" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_Succ" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "T\_Pred"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Mult" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_If0"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Unit" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_Loc"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Ref" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_Deref"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Assign" ].\
\

</div>

<div class="doc">

Of course, these typing rules will accurately predict the results of
evaluation only if the concrete store used during evaluation actually
conforms to the store typing that we assume for purposes of
typechecking. This proviso exactly parallels the situation with free
variables in the STLC: the substitution lemma promises us that, if <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>, then we can replace the free
variables in <span class="inlinecode"><span class="id"
type="var">t</span></span> with values of the types listed in <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> to obtain a
closed term of type <span class="inlinecode"><span class="id"
type="var">T</span></span>, which, by the type preservation theorem will
evaluate to a final result of type <span class="inlinecode"><span
class="id" type="var">T</span></span> if it yields any result at all.
(We will see later how to formalize an analogous intuition for stores
and store typings.)
<div class="paragraph">

</div>

However, for purposes of typechecking the terms that programmers
actually write, we do not need to do anything tricky to guess what store
typing we should use. Recall that concrete location constants arise only
in terms that are the intermediate results of evaluation; they are not
in the language that programmers write. Thus, we can simply typecheck
the programmer's terms with respect to the *empty* store typing. As
evaluation proceeds and new locations are created, we will always be
able to see how to extend the store typing by looking at the type of the
initial values being placed in newly allocated cells; this intuition is
formalized in the statement of the type preservation theorem below.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Properties {.section}
==========

<div class="paragraph">

</div>

Our final task is to check that standard type safety properties continue
to hold for the STLC with references. The progress theorem ("well-typed
terms are not stuck") can be stated and proved almost as for the STLC;
we just need to add a few straightforward cases to the proof, dealing
with the new constructs. The preservation theorem is a bit more
interesting, so let's look at it first.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Well-Typed Stores {.section}
-----------------

<div class="paragraph">

</div>

Since we have extended both the evaluation relation (with initial and
final stores) and the typing relation (with a store typing), we need to
change the statement of preservation to include these parameters.
Clearly, though, we cannot just add stores and store typings without
saying anything about how they are related:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">preservation\_wrong1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST</span> <span class="id" type="var">T</span> <span
class="id" type="var">t</span> <span class="id" type="var">st</span>
<span class="id" type="var">t'</span> <span class="id"
type="var">st'</span>,\
   <span class="id" type="var">empty</span>; <span class="id"
type="var">ST</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">t</span> ∈ <span class="id" type="var">T</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">t</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t'</span> / <span class="id" type="var">st'</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">empty</span>; <span class="id"
type="var">ST</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">t'</span> ∈ <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

If we typecheck with respect to some set of assumptions about the types
of the values in the store and then evaluate with respect to a store
that violates these assumptions, the result will be disaster. We say
that a store <span class="inlinecode"><span class="id"
type="var">st</span></span> is *well typed* with respect a store typing
<span class="inlinecode"><span class="id" type="var">ST</span></span> if
the term at each location <span class="inlinecode"><span class="id"
type="var">l</span></span> in <span class="inlinecode"><span class="id"
type="var">st</span></span> has the type at location <span
class="inlinecode"><span class="id" type="var">l</span></span> in <span
class="inlinecode"><span class="id" type="var">ST</span></span>. Since
only closed terms ever get stored in locations (why?), it suffices to
type them in the empty context. The following definition of <span
class="inlinecode"><span class="id"
type="var">store\_well\_typed</span></span> formalizes this.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">store\_well\_typed</span> (<span class="id"
type="var">ST</span>:<span class="id" type="var">store\_ty</span>)
(<span class="id" type="var">st</span>:<span class="id"
type="var">store</span>) :=\
   <span class="id" type="var">length</span> <span class="id"
type="var">ST</span> = <span class="id" type="var">length</span> <span
class="id" type="var">st</span> <span
style="font-family: arial;">∧</span>\
   (<span style="font-family: arial;">∀</span><span class="id"
type="var">l</span>, <span class="id" type="var">l</span> \< <span
class="id" type="var">length</span> <span class="id"
type="var">st</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">empty</span>; <span class="id"
type="var">ST</span> <span style="font-family: arial;">⊢</span> (<span
class="id" type="var">store\_lookup</span> <span class="id"
type="var">l</span> <span class="id" type="var">st</span>) ∈ (<span
class="id" type="var">store\_Tlookup</span> <span class="id"
type="var">l</span> <span class="id" type="var">ST</span>)).\
\

</div>

<div class="doc">

Informally, we will write <span class="inlinecode"><span class="id"
type="var">ST</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">st</span></span> for
<span class="inlinecode"><span class="id"
type="var">store\_well\_typed</span></span> <span
class="inlinecode"><span class="id" type="var">ST</span></span> <span
class="inlinecode"><span class="id" type="var">st</span></span>.
<div class="paragraph">

</div>

Intuitively, a store <span class="inlinecode"><span class="id"
type="var">st</span></span> is consistent with a store typing <span
class="inlinecode"><span class="id" type="var">ST</span></span> if every
value in the store has the type predicted by the store typing. (The only
subtle point is the fact that, when typing the values in the store, we
supply the very same store typing to the typing relation! This allows us
to type circular stores.)
<div class="paragraph">

</div>

#### Exercise: 2 stars (store\_not\_unique) {.section}

Can you find a store <span class="inlinecode"><span class="id"
type="var">st</span></span>, and two different store typings <span
class="inlinecode"><span class="id" type="var">ST1</span></span> and
<span class="inlinecode"><span class="id" type="var">ST2</span></span>
such that both <span class="inlinecode"><span class="id"
type="var">ST1</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">st</span></span> and
<span class="inlinecode"><span class="id" type="var">ST2</span></span>
<span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">st</span></span>?

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

We can now state something closer to the desired preservation property:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">preservation\_wrong2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST</span> <span class="id" type="var">T</span> <span
class="id" type="var">t</span> <span class="id" type="var">st</span>
<span class="id" type="var">t'</span> <span class="id"
type="var">st'</span>,\
   <span class="id" type="var">empty</span>; <span class="id"
type="var">ST</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">t</span> ∈ <span class="id" type="var">T</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">t</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t'</span> / <span class="id" type="var">st'</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">empty</span>; <span class="id"
type="var">ST</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">t'</span> ∈ <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

This statement is fine for all of the evaluation rules except the
allocation rule <span class="inlinecode"><span class="id"
type="var">ST\_RefValue</span></span>. The problem is that this rule
yields a store with a larger domain than the initial store, which
falsifies the conclusion of the above statement: if <span
class="inlinecode"><span class="id" type="var">st'</span></span>
includes a binding for a fresh location <span class="inlinecode"><span
class="id" type="var">l</span></span>, then <span
class="inlinecode"><span class="id" type="var">l</span></span> cannot be
in the domain of <span class="inlinecode"><span class="id"
type="var">ST</span></span>, and it will not be the case that <span
class="inlinecode"><span class="id" type="var">t'</span></span> (which
definitely mentions <span class="inlinecode"><span class="id"
type="var">l</span></span>) is typable under <span
class="inlinecode"><span class="id" type="var">ST</span></span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Extending Store Typings {.section}
-----------------------

<div class="paragraph">

</div>

Evidently, since the store can increase in size during evaluation, we
need to allow the store typing to grow as well. This motivates the
following definition. We say that the store type <span
class="inlinecode"><span class="id" type="var">ST'</span></span>
*extends* <span class="inlinecode"><span class="id"
type="var">ST</span></span> if <span class="inlinecode"><span class="id"
type="var">ST'</span></span> is just <span class="inlinecode"><span
class="id" type="var">ST</span></span> with some new types added to the
end.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">extends</span> : <span class="id" type="var">store\_ty</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">store\_ty</span> <span style="font-family: arial;">→</span>
<span class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">extends\_nil</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST'</span>,\
       <span class="id" type="var">extends</span> <span class="id"
type="var">ST'</span> <span class="id" type="var">nil</span>\
   | <span class="id" type="var">extends\_cons</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">ST'</span> <span class="id"
type="var">ST</span>,\
       <span class="id" type="var">extends</span> <span class="id"
type="var">ST'</span> <span class="id" type="var">ST</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">extends</span> (<span class="id"
type="var">x</span>::<span class="id" type="var">ST'</span>) (<span
class="id" type="var">x</span>::<span class="id" type="var">ST</span>).\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">extends</span>.\
\

</div>

<div class="doc">

We'll need a few technical lemmas about extended contexts.
<div class="paragraph">

</div>

First, looking up a type in an extended store typing yields the same
result as in the original:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">extends\_lookup</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">l</span>
<span class="id" type="var">ST</span> <span class="id"
type="var">ST'</span>,\
   <span class="id" type="var">l</span> \< <span class="id"
type="var">length</span> <span class="id" type="var">ST</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">extends</span> <span class="id"
type="var">ST'</span> <span class="id" type="var">ST</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_Tlookup</span> <span class="id"
type="var">l</span> <span class="id" type="var">ST'</span> = <span
class="id" type="var">store\_Tlookup</span> <span class="id"
type="var">l</span> <span class="id" type="var">ST</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">l</span> <span class="id" type="var">ST</span> <span
class="id" type="var">ST'</span> <span class="id" type="var">Hlen</span>
<span class="id" type="var">H</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">ST'</span>.
<span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">l</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">ST</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">a</span> <span class="id" type="var">ST2</span>];
<span class="id" type="tactic">intros</span> <span class="id"
type="var">l</span> <span class="id" type="var">Hlen</span> <span
class="id" type="var">ST'</span> <span class="id"
type="var">HST'</span>.\
   <span class="id" type="var">Case</span> "nil". <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hlen</span>.\
   <span class="id" type="var">Case</span> "cons". <span class="id"
type="tactic">unfold</span> <span class="id"
type="var">store\_Tlookup</span> <span class="id"
type="keyword">in</span> ×.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">ST'</span>.\
     <span class="id" type="var">SCase</span> "ST' = nil". <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">HST'</span>.\
     <span class="id" type="var">SCase</span> "ST' = a' :: ST'2".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HST'</span>; <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">l'</span>].\
       <span class="id" type="var">SSCase</span> "l = 0"...\
       <span class="id" type="var">SSCase</span> "l = S l'". <span
class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHST2</span>...\
         <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hlen</span>; <span
class="id" type="tactic">omega</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Next, if <span class="inlinecode"><span class="id"
type="var">ST'</span></span> extends <span class="inlinecode"><span
class="id" type="var">ST</span></span>, the length of <span
class="inlinecode"><span class="id" type="var">ST'</span></span> is at
least that of <span class="inlinecode"><span class="id"
type="var">ST</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">length\_extends</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">l</span>
<span class="id" type="var">ST</span> <span class="id"
type="var">ST'</span>,\
   <span class="id" type="var">l</span> \< <span class="id"
type="var">length</span> <span class="id" type="var">ST</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">extends</span> <span class="id"
type="var">ST'</span> <span class="id" type="var">ST</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">l</span> \< <span class="id"
type="var">length</span> <span class="id" type="var">ST'</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">l</span>.
<span class="id" type="tactic">induction</span> <span class="id"
type="var">H0</span>; <span class="id" type="tactic">intros</span> <span
class="id" type="var">l</span> <span class="id" type="var">Hlen</span>.\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hlen</span>.\
     <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> ×.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">l</span>; <span class="id" type="tactic">try</span> <span
class="id" type="tactic">omega</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">lt\_n\_S</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">IHextends</span>. <span class="id"
type="tactic">omega</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Finally, <span class="inlinecode"><span class="id"
type="var">snoc</span></span> <span class="inlinecode"><span class="id"
type="var">ST</span></span> <span class="inlinecode"><span class="id"
type="var">T</span></span> extends <span class="inlinecode"><span
class="id" type="var">ST</span></span>, and <span
class="inlinecode"><span class="id" type="var">extends</span></span> is
reflexive.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">extends\_snoc</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST</span> <span class="id" type="var">T</span>,\
   <span class="id" type="var">extends</span> (<span class="id"
type="var">snoc</span> <span class="id" type="var">ST</span> <span
class="id" type="var">T</span>) <span class="id" type="var">ST</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">ST</span>; <span class="id" type="tactic">intros</span> <span
class="id" type="var">T</span>...\
   <span class="id" type="tactic">simpl</span>...\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">extends\_refl</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST</span>,\
   <span class="id" type="var">extends</span> <span class="id"
type="var">ST</span> <span class="id" type="var">ST</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">ST</span>; <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Preservation, Finally {.section}
---------------------

<div class="paragraph">

</div>

We can now give the final, correct statement of the type preservation
property:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">preservation\_theorem</span> := <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span> <span class="id" type="var">T</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span>,\
   <span class="id" type="var">empty</span>; <span class="id"
type="var">ST</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">t</span> ∈ <span class="id" type="var">T</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">t</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t'</span> / <span class="id" type="var">st'</span>
<span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>,\
     (<span class="id" type="var">extends</span> <span class="id"
type="var">ST'</span> <span class="id" type="var">ST</span> <span
style="font-family: arial;">∧</span>\
      <span class="id" type="var">empty</span>; <span class="id"
type="var">ST'</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">t'</span> ∈ <span class="id" type="var">T</span>
<span style="font-family: arial;">∧</span>\
      <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST'</span> <span class="id"
type="var">st'</span>).\
\

</div>

<div class="doc">

Note that the preservation theorem merely asserts that there is *some*
store typing <span class="inlinecode"><span class="id"
type="var">ST'</span></span> extending <span class="inlinecode"><span
class="id" type="var">ST</span></span> (i.e., agreeing with <span
class="inlinecode"><span class="id" type="var">ST</span></span> on the
values of all the old locations) such that the new term <span
class="inlinecode"><span class="id" type="var">t'</span></span> is well
typed with respect to <span class="inlinecode"><span class="id"
type="var">ST'</span></span>; it does not tell us exactly what <span
class="inlinecode"><span class="id" type="var">ST'</span></span> is. It
is intuitively clear, of course, that <span class="inlinecode"><span
class="id" type="var">ST'</span></span> is either <span
class="inlinecode"><span class="id" type="var">ST</span></span> or else
it is exactly <span class="inlinecode"><span class="id"
type="var">snoc</span></span> <span class="inlinecode"><span class="id"
type="var">ST</span></span> <span class="inlinecode"><span class="id"
type="var">T~1~</span></span>, where <span class="inlinecode"><span
class="id" type="var">T~1~</span></span> is the type of the value <span
class="inlinecode"><span class="id" type="var">v~1~</span></span> in the
extended store <span class="inlinecode"><span class="id"
type="var">snoc</span></span> <span class="inlinecode"><span class="id"
type="var">st</span></span> <span class="inlinecode"><span class="id"
type="var">v~1~</span></span>, but stating this explicitly would
complicate the statement of the theorem without actually making it any
more useful: the weaker version above is already in the right form
(because its conclusion implies its hypothesis) to "turn the crank"
repeatedly and conclude that every *sequence* of evaluation steps
preserves well-typedness. Combining this with the progress property, we
obtain the usual guarantee that "well-typed programs never go wrong."
<div class="paragraph">

</div>

In order to prove this, we'll need a few lemmas, as usual.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Substitution lemma {.section}
------------------

<div class="paragraph">

</div>

First, we need an easy extension of the standard substitution lemma,
along with the same machinery about context invariance that we used in
the proof of the substitution lemma for the STLC.

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
   | <span class="id" type="var">afi\_succ</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tsucc</span>
<span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">afi\_pred</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tpred</span>
<span class="id" type="var">t~1~</span>)\
   | <span class="id" type="var">afi\_mult1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tmult</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_mult2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tmult</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_if0\_1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif0</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>)\
   | <span class="id" type="var">afi\_if0\_2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif0</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>)\
   | <span class="id" type="var">afi\_if0\_3</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~3~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif0</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>)\
   | <span class="id" type="var">afi\_ref</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">appears\_free\_in</span> <span class="id" type="var">x</span>
(<span class="id" type="var">tref</span> <span class="id"
type="var">t~1~</span>)\
   | <span class="id" type="var">afi\_deref</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">appears\_free\_in</span> <span class="id" type="var">x</span>
(<span class="id" type="var">tderef</span> <span class="id"
type="var">t~1~</span>)\
   | <span class="id" type="var">afi\_assign1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">appears\_free\_in</span> <span class="id" type="var">x</span>
(<span class="id" type="var">tassign</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">afi\_assign2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">appears\_free\_in</span> <span class="id" type="var">x</span>
(<span class="id" type="var">tassign</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>).\
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
"afi\_app2" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "afi\_abs"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "afi\_succ" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"afi\_pred"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "afi\_mult1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"afi\_mult2"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "afi\_if0\_1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"afi\_if0\_2" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "afi\_if0\_3"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "afi\_ref" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"afi\_deref"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "afi\_assign1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"afi\_assign2" ].\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">appears\_free\_in</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">free\_in\_context</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t</span> <span class="id"
type="var">T</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span>,\
    <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
    <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
    <span style="font-family: arial;">∃</span><span class="id"
type="var">T'</span>, <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> = <span class="id" type="var">Some</span> <span
class="id" type="var">T'</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">T</span>.\
   <span class="id" type="var">afi\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>)
<span class="id" type="var">Case</span>;\
         <span class="id" type="tactic">intros</span>; (<span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> [
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">eauto</span> ]).\
   <span class="id" type="var">Case</span> "afi\_abs".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H1</span>; <span class="id" type="tactic">subst</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHappears\_free\_in</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H8</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">extend\_neq</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H8</span>; <span class="id"
type="tactic">assumption</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">context\_invariance</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: serif; font-size:85%;">Γ'</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span>,\
   <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
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
   <span style="font-family: serif; font-size:85%;">Γ'</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ'</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span>...\
   <span class="id" type="var">Case</span> "T\_Var".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Var</span>. <span class="id"
type="tactic">symmetry</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">H</span>...\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">IHhas\_type</span>; <span class="id"
type="tactic">intros</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x0</span>)...\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_App</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHhas\_type1</span>...\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHhas\_type2</span>...\
   <span class="id" type="var">Case</span> "T\_Mult".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Mult</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHhas\_type1</span>...\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHhas\_type2</span>...\
   <span class="id" type="var">Case</span> "T\_If0".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_If0</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHhas\_type1</span>...\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHhas\_type2</span>...\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHhas\_type3</span>...\
   <span class="id" type="var">Case</span> "T\_Assign".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Assign</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHhas\_type1</span>...\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHhas\_type2</span>...\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">substitution\_preserves\_typing</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">S</span>
<span class="id" type="var">t</span> <span class="id"
type="var">T</span>,\
   <span class="id" type="var">empty</span>; <span class="id"
type="var">ST</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">s</span> ∈ <span class="id" type="var">S</span>
<span style="font-family: arial;">→</span>\
   (<span class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">S</span>); <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> ([<span class="id"
type="var">x</span>:=<span class="id" type="var">s</span>]<span
class="id" type="var">t</span>) ∈ <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">S</span>
<span class="id" type="var">t</span> <span class="id"
type="var">T</span> <span class="id" type="var">Hs</span> <span
class="id" type="var">Ht</span>.\
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
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">simpl</span>...\
   <span class="id" type="var">Case</span> "tvar".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>).\
     <span class="id" type="var">SCase</span> "x = y".\
       <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">extend\_eq</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H3</span>.\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H3</span>; <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>...\
       <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">Hcontra</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">free\_in\_context</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span> <span class="id"
type="var">Hcontra</span> <span class="id" type="var">Hs</span>) <span
class="id" type="keyword">as</span> [<span class="id"
type="var">T'</span> <span class="id" type="var">HT'</span>].\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT'</span>.\
     <span class="id" type="var">SCase</span> "x ≠ y".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Var</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">extend\_neq</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H3</span>...\
   <span class="id" type="var">Case</span> "tabs". <span class="id"
type="tactic">subst</span>.\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>).\
     <span class="id" type="var">SCase</span> "x = y".\
       <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">context\_invariance</span>...\
       <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">extend\_shadow</span>.\
     <span class="id" type="var">SCase</span> "x ≠ x0".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">IHt</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>...\
       <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">extend</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">y</span> <span
class="id" type="var">x0</span>)...\
       <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Assignment Preserves Store Typing {.section}
---------------------------------

<div class="paragraph">

</div>

Next, we must show that replacing the contents of a cell in the store
with a new value of appropriate type does not change the overall type of
the store. (This is needed for the <span class="inlinecode"><span
class="id" type="var">ST\_Assign</span></span> rule.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">assign\_pres\_store\_typing</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST</span> <span class="id" type="var">st</span> <span
class="id" type="var">l</span> <span class="id" type="var">t</span>,\
   <span class="id" type="var">l</span> \< <span class="id"
type="var">length</span> <span class="id" type="var">st</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">empty</span>; <span class="id"
type="var">ST</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">t</span> ∈ (<span class="id"
type="var">store\_Tlookup</span> <span class="id" type="var">l</span>
<span class="id" type="var">ST</span>) <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST</span> (<span class="id"
type="tactic">replace</span> <span class="id" type="var">l</span> <span
class="id" type="var">t</span> <span class="id" type="var">st</span>).\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">ST</span> <span class="id" type="var">st</span> <span
class="id" type="var">l</span> <span class="id" type="var">t</span>
<span class="id" type="var">Hlen</span> <span class="id"
type="var">HST</span> <span class="id" type="var">Ht</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HST</span>; <span class="id" type="tactic">subst</span>.\
   <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">length\_replace</span>...\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">l'</span> <span class="id" type="var">Hl'</span>.\
   <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">beq\_nat</span> <span class="id" type="var">l'</span> <span
class="id" type="var">l</span>) <span class="id" type="var">eqn</span>:
<span class="id" type="var">Heqll'</span>.\
   <span class="id" type="var">Case</span> "l' = l".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">beq\_nat\_true</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Heqll'</span>;
<span class="id" type="tactic">subst</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">lookup\_replace\_eq</span>...\
   <span class="id" type="var">Case</span> "l' ≠ l".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">beq\_nat\_false</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Heqll'</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">lookup\_replace\_neq</span>...\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">length\_replace</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hl'</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">H0</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Weakening for Stores {.section}
--------------------

<div class="paragraph">

</div>

Finally, we need a lemma on store typings, stating that, if a store
typing is extended with a new location, the extended one still allows us
to assign the same types to the same terms as the original.
<div class="paragraph">

</div>

(The lemma is called <span class="inlinecode"><span class="id"
type="var">store\_weakening</span></span> because it resembles the
"weakening" lemmas found in proof theory, which show that adding a new
assumption to some logical theory does not decrease the set of provable
theorems.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">store\_weakening</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ST</span> <span class="id" type="var">ST'</span> <span
class="id" type="var">t</span> <span class="id" type="var">T</span>,\
   <span class="id" type="var">extends</span> <span class="id"
type="var">ST'</span> <span class="id" type="var">ST</span> <span
style="font-family: arial;">→</span>\
   <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span style="font-family: serif; font-size:85%;">Γ</span>; <span
class="id" type="var">ST'</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H0</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">eauto</span>.\
   <span class="id" type="var">Case</span> "T\_Loc".\
     <span class="id" type="var">erewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">extends\_lookup</span>...\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Loc</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">length\_extends</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

We can use the <span class="inlinecode"><span class="id"
type="var">store\_weakening</span></span> lemma to prove that if a store
is well typed with respect to a store typing, then the store extended
with a new term <span class="inlinecode"><span class="id"
type="var">t</span></span> will still be well typed with respect to the
store typing extended with <span class="inlinecode"><span class="id"
type="var">t</span></span>'s type.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">store\_well\_typed\_snoc</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST</span> <span class="id" type="var">st</span> <span
class="id" type="var">t~1~</span> <span class="id"
type="var">T~1~</span>,\
   <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">empty</span>; <span class="id"
type="var">ST</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">t~1~</span> ∈ <span class="id"
type="var">T~1~</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_well\_typed</span> (<span
class="id" type="var">snoc</span> <span class="id" type="var">ST</span>
<span class="id" type="var">T~1~</span>) (<span class="id"
type="var">snoc</span> <span class="id" type="var">st</span> <span
class="id" type="var">t~1~</span>).\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">store\_well\_typed</span> <span class="id"
type="keyword">in</span> ×.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">Hlen</span> <span class="id"
type="var">Hmatch</span>]; <span class="id" type="tactic">clear</span>
<span class="id" type="var">H</span>.\
   <span class="id" type="tactic">rewrite</span> !<span class="id"
type="var">length\_snoc</span>.\
   <span class="id" type="tactic">split</span>...\
   <span class="id" type="var">Case</span> "types match.".\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">l</span> <span class="id" type="var">Hl</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">store\_lookup</span>, <span class="id"
type="var">store\_Tlookup</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">le\_lt\_eq\_dec</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hl</span>; <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">Hl</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">Hlt</span> | <span class="id"
type="var">Heq</span>].\
     <span class="id" type="var">SCase</span> "l \< length st".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">lt\_S\_n</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">Hlt</span>.\
       <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> !<span class="id"
type="var">nth\_lt\_snoc</span>...\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">store\_weakening</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">ST</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">extends\_snoc</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">Hmatch</span>...\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">Hlen</span>...\
     <span class="id" type="var">SCase</span> "l = length st".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heq</span>.\
       <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">nth\_eq\_snoc</span>.\
       <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">Hlen</span>. <span class="id" type="tactic">rewrite</span>
<span class="id" type="var">nth\_eq\_snoc</span>...\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">store\_weakening</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">ST</span>...
<span class="id" type="tactic">apply</span> <span class="id"
type="var">extends\_snoc</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Preservation! {.section}
-------------

<div class="paragraph">

</div>

Now that we've got everything set up right, the proof of preservation is
actually quite straightforward.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">preservation</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span> <span class="id" type="var">T</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span>,\
   <span class="id" type="var">empty</span>; <span class="id"
type="var">ST</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">t</span> ∈ <span class="id" type="var">T</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">t</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇒</span> <span
class="id" type="var">t'</span> / <span class="id" type="var">st'</span>
<span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>,\
     (<span class="id" type="var">extends</span> <span class="id"
type="var">ST'</span> <span class="id" type="var">ST</span> <span
style="font-family: arial;">∧</span>\
      <span class="id" type="var">empty</span>; <span class="id"
type="var">ST'</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">t'</span> ∈ <span class="id" type="var">T</span>
<span style="font-family: arial;">∧</span>\
      <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST'</span> <span class="id"
type="var">st'</span>).\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>
<span class="id" type="keyword">using</span> <span class="id"
type="var">store\_weakening</span>, <span class="id"
type="var">extends\_refl</span>.\
     <span class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t</span> <span
class="id" type="var">t'</span> <span class="id" type="var">T</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span> <span class="id" type="var">Ht</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">t'</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Ht</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">t'</span> <span
class="id" type="var">HST</span> <span class="id"
type="var">Hstep</span>;\
     <span class="id" type="tactic">subst</span>; <span class="id"
type="tactic">try</span> (<span class="id" type="var">solve</span> <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">inversion</span>); <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hstep</span>;
<span class="id" type="tactic">subst</span>;\
     <span class="id" type="tactic">try</span> (<span class="id"
type="tactic">eauto</span> <span class="id" type="keyword">using</span>
<span class="id" type="var">store\_weakening</span>, <span class="id"
type="var">extends\_refl</span>).\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="var">SCase</span> "ST\_AppAbs". <span
style="font-family: arial;">∃</span><span class="id"
type="var">ST</span>.\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1</span>; <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">split</span>; <span class="id"
type="tactic">try</span> <span class="id" type="tactic">split</span>...
<span class="id" type="tactic">eapply</span> <span class="id"
type="var">substitution\_preserves\_typing</span>...\
     <span class="id" type="var">SCase</span> "ST\_App1".\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHHt1</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H0</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">ST'</span> [<span class="id"
type="var">Hext</span> [<span class="id" type="var">Hty</span> <span
class="id" type="var">Hsty</span>]]].\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>...\
     <span class="id" type="var">SCase</span> "ST\_App2".\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHHt2</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H5</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">ST'</span> [<span class="id"
type="var">Hext</span> [<span class="id" type="var">Hty</span> <span
class="id" type="var">Hsty</span>]]].\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>...\
   <span class="id" type="var">Case</span> "T\_Succ".\
     <span class="id" type="var">SCase</span> "ST\_Succ".\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHHt</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H0</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">ST'</span> [<span class="id"
type="var">Hext</span> [<span class="id" type="var">Hty</span> <span
class="id" type="var">Hsty</span>]]].\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>...\
   <span class="id" type="var">Case</span> "T\_Pred".\
     <span class="id" type="var">SCase</span> "ST\_Pred".\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHHt</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H0</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">ST'</span> [<span class="id"
type="var">Hext</span> [<span class="id" type="var">Hty</span> <span
class="id" type="var">Hsty</span>]]].\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>...\
   <span class="id" type="var">Case</span> "T\_Mult".\
     <span class="id" type="var">SCase</span> "ST\_Mult1".\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHHt1</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H0</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">ST'</span> [<span class="id"
type="var">Hext</span> [<span class="id" type="var">Hty</span> <span
class="id" type="var">Hsty</span>]]].\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>...\
     <span class="id" type="var">SCase</span> "ST\_Mult2".\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHHt2</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H5</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">ST'</span> [<span class="id"
type="var">Hext</span> [<span class="id" type="var">Hty</span> <span
class="id" type="var">Hsty</span>]]].\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>...\
   <span class="id" type="var">Case</span> "T\_If0".\
     <span class="id" type="var">SCase</span> "ST\_If0\_1".\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHHt1</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H0</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">ST'</span> [<span class="id"
type="var">Hext</span> [<span class="id" type="var">Hty</span> <span
class="id" type="var">Hsty</span>]]].\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>... <span class="id" type="tactic">split</span>...\
   <span class="id" type="var">Case</span> "T\_Ref".\
     <span class="id" type="var">SCase</span> "ST\_RefValue".\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">snoc</span> <span class="id" type="var">ST</span> <span
class="id" type="var">T~1~</span>).\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HST</span>; <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">split</span>.\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">extends\_snoc</span>.\
       <span class="id" type="tactic">split</span>.\
         <span class="id" type="tactic">replace</span> (<span class="id"
type="var">TRef</span> <span class="id" type="var">T~1~</span>)\
           <span class="id" type="keyword">with</span> (<span class="id"
type="var">TRef</span> (<span class="id"
type="var">store\_Tlookup</span> (<span class="id"
type="var">length</span> <span class="id" type="var">st</span>) (<span
class="id" type="var">snoc</span> <span class="id" type="var">ST</span>
<span class="id" type="var">T~1~</span>))).\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Loc</span>.\
         <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">rewrite</span> <span
class="id" type="var">length\_snoc</span>. <span class="id"
type="tactic">omega</span>.\
         <span class="id" type="tactic">unfold</span> <span class="id"
type="var">store\_Tlookup</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">H</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">nth\_eq\_snoc</span>...\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">store\_well\_typed\_snoc</span>; <span class="id"
type="tactic">assumption</span>.\
     <span class="id" type="var">SCase</span> "ST\_Ref".\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHHt</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H0</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">ST'</span> [<span class="id"
type="var">Hext</span> [<span class="id" type="var">Hty</span> <span
class="id" type="var">Hsty</span>]]].\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>...\
   <span class="id" type="var">Case</span> "T\_Deref".\
     <span class="id" type="var">SCase</span> "ST\_DerefLoc".\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST</span>. <span class="id" type="tactic">split</span>; <span
class="id" type="tactic">try</span> <span class="id"
type="tactic">split</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HST</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">\_</span> <span class="id"
type="var">Hsty</span>].\
       <span class="id" type="tactic">replace</span> <span class="id"
type="var">T~11~</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">store\_Tlookup</span> <span class="id"
type="var">l</span> <span class="id" type="var">ST</span>).\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">Hsty</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">SCase</span> "ST\_Deref".\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHHt</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H0</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">ST'</span> [<span class="id"
type="var">Hext</span> [<span class="id" type="var">Hty</span> <span
class="id" type="var">Hsty</span>]]].\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>...\
   <span class="id" type="var">Case</span> "T\_Assign".\
     <span class="id" type="var">SCase</span> "ST\_Assign".\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST</span>. <span class="id" type="tactic">split</span>; <span
class="id" type="tactic">try</span> <span class="id"
type="tactic">split</span>...\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">assign\_pres\_store\_typing</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">SCase</span> "ST\_Assign1".\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHHt1</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H0</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">ST'</span> [<span class="id"
type="var">Hext</span> [<span class="id" type="var">Hty</span> <span
class="id" type="var">Hsty</span>]]].\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>...\
     <span class="id" type="var">SCase</span> "ST\_Assign2".\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHHt2</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H5</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">ST'</span> [<span class="id"
type="var">Hext</span> [<span class="id" type="var">Hty</span> <span
class="id" type="var">Hsty</span>]]].\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ST'</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars (preservation\_informal) {.section}

Write a careful informal proof of the preservation theorem,
concentrating on the <span class="inlinecode"><span class="id"
type="var">T\_App</span></span>, <span class="inlinecode"><span
class="id" type="var">T\_Deref</span></span>, <span
class="inlinecode"><span class="id" type="var">T\_Assign</span></span>,
and <span class="inlinecode"><span class="id"
type="var">T\_Ref</span></span> cases.
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Progress {.section}
--------

<div class="paragraph">

</div>

Fortunately, progress for this system is pretty easy to prove; the proof
is very similar to the proof of progress for the STLC, with a few new
cases for the new syntactic constructs.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="tactic">progress</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">ST</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span class="id" type="var">st</span>,\
   <span class="id" type="var">empty</span>; <span class="id"
type="var">ST</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">t</span> ∈ <span class="id" type="var">T</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">store\_well\_typed</span> <span
class="id" type="var">ST</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">→</span>\
   (<span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">∨</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">st'</span>, <span class="id" type="var">t</span> /
<span class="id" type="var">st</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span> / <span class="id" type="var">st'</span>).\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">ST</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span class="id" type="var">st</span>
<span class="id" type="var">Ht</span> <span class="id"
type="var">HST</span>. <span class="id" type="var">remember</span>
(@<span class="id" type="var">empty</span> <span class="id"
type="var">ty</span>) <span class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Ht</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">subst</span>; <span class="id" type="tactic">try</span>
<span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>...\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">IHHt1</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">Ht1p</span> | <span class="id" type="var">Ht1p</span>]...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">Ht2p</span> | <span class="id"
type="var">Ht2p</span>]...\
       <span class="id" type="var">SSCase</span> "t~2~ steps".\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">Ht2p</span> <span class="id"
type="keyword">as</span> [<span class="id" type="var">t~2~'</span>
[<span class="id" type="var">st'</span> <span class="id"
type="var">Hstep</span>]].\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> (<span class="id" type="var">tabs</span> <span
class="id" type="var">x</span> <span class="id" type="var">T</span>
<span class="id" type="var">t</span>) <span class="id"
type="var">t~2~'</span>). <span
style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> [<span class="id"
type="var">st'</span> <span class="id" type="var">Hstep</span>]].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>). <span
style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>...\
   <span class="id" type="var">Case</span> "T\_Succ".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">IHHt</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">Ht1p</span> | <span class="id" type="var">Ht1p</span>]...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> [ <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Ht</span> ].\
       <span class="id" type="var">SSCase</span> "t~1~ is a tnat".\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tnat</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>)). <span
style="font-family: arial;">∃</span><span class="id"
type="var">st</span>...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> [<span class="id"
type="var">st'</span> <span class="id" type="var">Hstep</span>]].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tsucc</span> <span class="id" type="var">t~1~'</span>). <span
style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>...\
   <span class="id" type="var">Case</span> "T\_Pred".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">IHHt</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">Ht1p</span> | <span class="id" type="var">Ht1p</span>]...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> [<span class="id" type="tactic">inversion</span>
<span class="id" type="var">Ht</span> ].\
       <span class="id" type="var">SSCase</span> "t~1~ is a tnat".\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tnat</span> (<span class="id" type="var">pred</span> <span
class="id" type="var">n</span>)). <span
style="font-family: arial;">∃</span><span class="id"
type="var">st</span>...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> [<span class="id"
type="var">st'</span> <span class="id" type="var">Hstep</span>]].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tpred</span> <span class="id" type="var">t~1~'</span>). <span
style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>...\
   <span class="id" type="var">Case</span> "T\_Mult".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">IHHt1</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">Ht1p</span> | <span class="id" type="var">Ht1p</span>]...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> [<span class="id" type="tactic">inversion</span>
<span class="id" type="var">Ht1</span>].\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">Ht2p</span> | <span class="id"
type="var">Ht2p</span>]...\
       <span class="id" type="var">SSCase</span> "t~2~ is a value".\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">Ht2p</span>; <span class="id"
type="tactic">subst</span>; <span class="id" type="tactic">try</span>
<span class="id" type="var">solve</span> [<span class="id"
type="tactic">inversion</span> <span class="id" type="var">Ht2</span>].\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tnat</span> (<span class="id" type="var">mult</span> <span
class="id" type="var">n</span> <span class="id" type="var">n0</span>)).
<span style="font-family: arial;">∃</span><span class="id"
type="var">st</span>...\
       <span class="id" type="var">SSCase</span> "t~2~ steps".\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">Ht2p</span> <span class="id"
type="keyword">as</span> [<span class="id" type="var">t~2~'</span>
[<span class="id" type="var">st'</span> <span class="id"
type="var">Hstep</span>]].\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tmult</span> (<span class="id" type="var">tnat</span> <span
class="id" type="var">n</span>) <span class="id"
type="var">t~2~'</span>). <span
style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> [<span class="id"
type="var">st'</span> <span class="id" type="var">Hstep</span>]].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tmult</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>). <span
style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>...\
   <span class="id" type="var">Case</span> "T\_If0".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">IHHt1</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">Ht1p</span> | <span class="id" type="var">Ht1p</span>]...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> [<span class="id" type="tactic">inversion</span>
<span class="id" type="var">Ht1</span>].\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">n</span>.\
       <span class="id" type="var">SSCase</span> "n = 0". <span
style="font-family: arial;">∃</span><span class="id"
type="var">t~2~</span>. <span style="font-family: arial;">∃</span><span
class="id" type="var">st</span>...\
       <span class="id" type="var">SSCase</span> "n = S n'". <span
style="font-family: arial;">∃</span><span class="id"
type="var">t~3~</span>. <span style="font-family: arial;">∃</span><span
class="id" type="var">st</span>...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> [<span class="id"
type="var">st'</span> <span class="id" type="var">Hstep</span>]].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tif0</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>). <span style="font-family: arial;">∃</span><span
class="id" type="var">st'</span>...\
   <span class="id" type="var">Case</span> "T\_Ref".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">IHHt</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">Ht1p</span> | <span class="id" type="var">Ht1p</span>]...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> [<span class="id"
type="var">st'</span> <span class="id" type="var">Hstep</span>]].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tref</span> <span class="id" type="var">t~1~'</span>). <span
style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>...\
   <span class="id" type="var">Case</span> "T\_Deref".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">IHHt</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">Ht1p</span> | <span class="id" type="var">Ht1p</span>]...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
       <span class="id" type="var">eexists</span>. <span class="id"
type="var">eexists</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">ST\_DerefLoc</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht</span>; <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">HST</span>; <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">H</span>...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> [<span class="id"
type="var">st'</span> <span class="id" type="var">Hstep</span>]].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tderef</span> <span class="id" type="var">t~1~'</span>).
<span style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>...\
   <span class="id" type="var">Case</span> "T\_Assign".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">IHHt1</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">Ht1p</span>|<span class="id" type="var">Ht1p</span>]...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">Ht2p</span>|<span class="id"
type="var">Ht2p</span>]...\
       <span class="id" type="var">SSCase</span> "t~2~ is a value".\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">Ht1p</span>; <span class="id"
type="tactic">subst</span>; <span class="id" type="tactic">try</span>
<span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
         <span class="id" type="var">eexists</span>. <span class="id"
type="var">eexists</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">ST\_Assign</span>...\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">HST</span>; <span class="id"
type="tactic">subst</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Ht1</span>;
<span class="id" type="tactic">subst</span>.\
         <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H5</span>...\
       <span class="id" type="var">SSCase</span> "t~2~ steps".\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">Ht2p</span> <span class="id"
type="keyword">as</span> [<span class="id" type="var">t~2~'</span>
[<span class="id" type="var">st'</span> <span class="id"
type="var">Hstep</span>]].\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tassign</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~'</span>). <span
style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Ht1p</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> [<span class="id"
type="var">st'</span> <span class="id" type="var">Hstep</span>]].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">tassign</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>). <span
style="font-family: arial;">∃</span><span class="id"
type="var">st'</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

References and Nontermination {.section}
=============================

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Section</span> <span class="id"
type="var">RefsAndNontermination</span>.\
 <span class="id" type="keyword">Import</span> <span class="id"
type="var">ExampleVariables</span>.\
\

</div>

<div class="doc">

We know that the simply typed lambda calculus is *normalizing*, that is,
every well-typed term can be reduced to a value in a finite number of
steps. What about STLC + references? Surprisingly, adding references
causes us to lose the normalization property: there exist well-typed
terms in the STLC + references which can continue to reduce forever,
without ever reaching a normal form!
<div class="paragraph">

</div>

How can we construct such a term? The main idea is to make a function
which calls itself. We first make a function which calls another
function stored in a reference cell; the trick is that we then smuggle
in a reference to itself!
       (\r:Ref (Unit -> Unit). 
            r := (\x:Unit.(!r) unit); (!r) unit) 
       (ref (\x:Unit.unit))

<div class="paragraph">

</div>

First, <span class="inlinecode"><span class="id"
type="var">ref</span></span> <span class="inlinecode">(\\<span
class="id" type="var">x</span>:<span class="id"
type="var">Unit.unit</span>)</span> creates a reference to a cell of
type <span class="inlinecode"><span class="id"
type="var">Unit</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">Unit</span></span>. We
then pass this reference as the argument to a function which binds it to
the name <span class="inlinecode"><span class="id"
type="var">r</span></span>, and assigns to it the function
(\\x:Unit.(!r) unit) — that is, the function which ignores its argument
and calls the function stored in <span class="inlinecode"><span
class="id" type="var">r</span></span> on the argument <span
class="inlinecode"><span class="id" type="var">unit</span></span>; but
of course, that function is itself! To get the ball rolling we finally
execute this function with <span class="inlinecode">(!<span class="id"
type="var">r</span>)</span> <span class="inlinecode"><span class="id"
type="var">unit</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">loop\_fun</span> :=\
   <span class="id" type="var">tabs</span> <span class="id"
type="var">x</span> <span class="id" type="var">TUnit</span> (<span
class="id" type="var">tapp</span> (<span class="id"
type="var">tderef</span> (<span class="id" type="var">tvar</span> <span
class="id" type="var">r</span>)) <span class="id"
type="var">tunit</span>).\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">loop</span> :=\
   <span class="id" type="var">tapp</span>\
   (<span class="id" type="var">tabs</span> <span class="id"
type="var">r</span> (<span class="id" type="var">TRef</span> (<span
class="id" type="var">TArrow</span> <span class="id"
type="var">TUnit</span> <span class="id" type="var">TUnit</span>))\
     (<span class="id" type="var">tseq</span> (<span class="id"
type="var">tassign</span> (<span class="id" type="var">tvar</span> <span
class="id" type="var">r</span>) <span class="id"
type="var">loop\_fun</span>)\
             (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tderef</span> (<span class="id" type="var">tvar</span> <span
class="id" type="var">r</span>)) <span class="id"
type="var">tunit</span>)))\
   (<span class="id" type="var">tref</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">TUnit</span> <span class="id"
type="var">tunit</span>)).\
\

</div>

<div class="doc">

This term is well typed:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">loop\_typeable</span> : <span
style="font-family: arial;">∃</span><span class="id"
type="var">T</span>, <span class="id" type="var">empty</span>; <span
class="id" type="var">nil</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">loop</span> ∈ <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="var">eexists</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">loop</span>.
<span class="id" type="tactic">unfold</span> <span class="id"
type="var">loop\_fun</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_App</span>...\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Abs</span>...\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_App</span>...\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Abs</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">T\_App</span>. <span class="id"
type="tactic">eapply</span> <span class="id" type="var">T\_Deref</span>.
<span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Var</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>. <span class="id" type="tactic">simpl</span>.
<span class="id" type="tactic">reflexivity</span>. <span class="id"
type="tactic">auto</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Assign</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Var</span>. <span class="id" type="tactic">unfold</span>
<span class="id" type="var">extend</span>. <span class="id"
type="tactic">simpl</span>. <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Abs</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_App</span>...\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_Deref</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">T\_Var</span>. <span class="id"
type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

To show formally that the term diverges, we first define the <span
class="inlinecode"><span class="id"
type="var">step\_closure</span></span> of the single-step reduction
relation, written <span class="inlinecode"><span
style="font-family: arial;">⇒+</span></span>. This is just like the
reflexive step closure of single-step reduction (which we're been
writing <span class="inlinecode"><span
style="font-family: arial;">⇒\*</span></span>), except that it is not
reflexive: <span class="inlinecode"><span class="id"
type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒+</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> means
that <span class="inlinecode"><span class="id"
type="var">t</span></span> can reach <span class="inlinecode"><span
class="id" type="var">t'</span></span> by *one or more* steps of
reduction.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">step\_closure</span> {<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>} (<span
class="id" type="var">R</span>: <span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) : <span
class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">sc\_one</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> <span class="id" type="var">y</span> : <span
class="id" type="var">X</span>),\
                 <span class="id" type="var">R</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">step\_closure</span> <span class="id" type="var">R</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y</span>\
   | <span class="id" type="var">sc\_step</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span> : <span class="id" type="var">X</span>),\
                 <span class="id" type="var">R</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
style="font-family: arial;">→</span>\
                 <span class="id" type="var">step\_closure</span> <span
class="id" type="var">R</span> <span class="id" type="var">y</span>
<span class="id" type="var">z</span> <span
style="font-family: arial;">→</span>\
                 <span class="id" type="var">step\_closure</span> <span
class="id" type="var">R</span> <span class="id" type="var">x</span>
<span class="id" type="var">z</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">multistep1</span> := (<span class="id"
type="var">step\_closure</span> <span class="id"
type="var">step</span>).\
 <span class="id" type="keyword">Notation</span> "t~1~ '/' st '<span
style="font-family: arial;">⇒+</span>' t~2~ '/' st'" := (<span
class="id" type="var">multistep1</span> (<span class="id"
type="var">t~1~</span>,<span class="id" type="var">st</span>) (<span
class="id" type="var">t~2~</span>,<span class="id"
type="var">st'</span>))\
   (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 40, <span class="id" type="var">st</span> <span
class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 39, <span class="id" type="var">t~2~</span>
<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 39).\
\

</div>

<div class="doc">

Now, we can show that the expression <span class="inlinecode"><span
class="id" type="var">loop</span></span> reduces to the expression <span
class="inlinecode">!(<span class="id" type="var">loc</span></span> <span
class="inlinecode">0)</span> <span class="inlinecode"><span class="id"
type="var">unit</span></span> and the size-one store <span
class="inlinecode"></span> <span class="inlinecode">[<span class="id"
type="var">r</span>:=(<span class="id" type="var">loc</span></span>
<span class="inlinecode">0)]</span> <span class="inlinecode"><span
class="id" type="var">loop\_fun</span></span>.
<div class="paragraph">

</div>

As a convenience, we introduce a slight variant of the <span
class="inlinecode"><span class="id" type="var">normalize</span></span>
tactic, called <span class="inlinecode"><span class="id"
type="var">reduce</span></span>, which tries solving the goal with <span
class="inlinecode"><span class="id" type="var">multi\_refl</span></span>
at each step, instead of waiting until the goal can't be reduced any
more. Of course, the whole point is that <span class="inlinecode"><span
class="id" type="var">loop</span></span> doesn't normalize, so the old
<span class="inlinecode"><span class="id"
type="var">normalize</span></span> tactic would just go into an infinite
loop reducing it forever!

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Ltac</span> <span class="id"
type="var">print\_goal</span> := <span class="id"
type="keyword">match</span> <span class="id" type="var">goal</span>
<span class="id" type="keyword">with</span> <span
style="font-family: arial;">⊢</span> ?<span class="id"
type="var">x</span> ⇒ <span class="id" type="var">idtac</span> <span
class="id" type="var">x</span> <span class="id"
type="keyword">end</span>.\
 <span class="id" type="keyword">Ltac</span> <span class="id"
type="var">reduce</span> :=\
     <span class="id" type="tactic">repeat</span> (<span class="id"
type="var">print\_goal</span>; <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">multi\_step</span> ;\
             [ (<span class="id" type="tactic">eauto</span> 10; <span
class="id" type="tactic">fail</span>) | (<span class="id"
type="var">instantiate</span>; <span class="id"
type="tactic">compute</span>)];\
             <span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> [<span class="id" type="tactic">apply</span>
<span class="id" type="var">multi\_refl</span>]).\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">loop\_steps\_to\_loop\_fun</span> :\
   <span class="id" type="var">loop</span> / <span class="id"
type="var">nil</span> <span style="font-family: arial;">⇒\*</span>\
   <span class="id" type="var">tapp</span> (<span class="id"
type="var">tderef</span> (<span class="id" type="var">tloc</span> 0))
<span class="id" type="var">tunit</span> / <span class="id"
type="var">cons</span> ([<span class="id" type="var">r</span>:=<span
class="id" type="var">tloc</span> 0]<span class="id"
type="var">loop\_fun</span>) <span class="id" type="var">nil</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">loop</span>.\
   <span class="id" type="var">reduce</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Finally, the latter expression reduces in two steps to itself!

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">loop\_fun\_step\_self</span> :\
   <span class="id" type="var">tapp</span> (<span class="id"
type="var">tderef</span> (<span class="id" type="var">tloc</span> 0))
<span class="id" type="var">tunit</span> / <span class="id"
type="var">cons</span> ([<span class="id" type="var">r</span>:=<span
class="id" type="var">tloc</span> 0]<span class="id"
type="var">loop\_fun</span>) <span class="id" type="var">nil</span>
<span style="font-family: arial;">⇒+</span>\
   <span class="id" type="var">tapp</span> (<span class="id"
type="var">tderef</span> (<span class="id" type="var">tloc</span> 0))
<span class="id" type="var">tunit</span> / <span class="id"
type="var">cons</span> ([<span class="id" type="var">r</span>:=<span
class="id" type="var">tloc</span> 0]<span class="id"
type="var">loop\_fun</span>) <span class="id" type="var">nil</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">loop\_fun</span>; <span class="id"
type="tactic">simpl</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">sc\_step</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">ST\_App1</span>...\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">sc\_one</span>. <span class="id"
type="tactic">compute</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">ST\_AppAbs</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 4 stars (factorial\_ref) {.section}

Use the above ideas to implement a factorial function in STLC with
references. (There is no need to prove formally that it really behaves
like the factorial. Just use the example below to make sure it gives the
correct result when applied to the argument <span
class="inlinecode">4</span>.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">factorial</span> : <span class="id" type="var">tm</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">factorial\_type</span> : <span class="id"
type="var">empty</span>; <span class="id" type="var">nil</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">factorial</span> ∈ (<span class="id" type="var">TArrow</span>
<span class="id" type="var">TNat</span> <span class="id"
type="var">TNat</span>).\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

If your definition is correct, you should be able to just uncomment the
example below; the proof should be fully automatic using the <span
class="inlinecode"><span class="id" type="var">reduce</span></span>
tactic.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* \
 Lemma factorial\_4 : exists st, \
   tapp factorial (tnat 4) / nil ==\>\* tnat 24 / st.\
 Proof.\
   eexists. unfold factorial. reduce.\
 Qed.\
 \*)</span>\

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

#### Exercise: 5 stars, optional (garabage\_collector) {.section}

Challenge problem: modify our formalization to include an account of
garbage collection, and prove that it satisfies whatever nice properties
you can think to prove about it.
<div class="paragraph">

</div>

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">RefsAndNontermination</span>.\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">STLCRef</span>.\
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
