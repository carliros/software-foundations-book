<div id="page">

<div id="header">

</div>

<div id="main">

Poly<span class="subtitle">Polymorphism and Higher-Order Functions</span> {.libtitle}
=========================================================================

<div class="code code-tight">

</div>

<div class="doc">

<div class="paragraph">

</div>

In this chapter we continue our development of basic concepts of
functional programming. The critical new ideas are *polymorphism*
(abstracting functions over the types of the data they manipulate) and
*higher-order functions* (treating functions as data).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">Lists</span>.\
\

</div>

<div class="doc">

Polymorphism {.section}
============

</div>

<div class="code code-space">

</div>

<div class="doc">

Polymorphic Lists {.section}
-----------------

<div class="paragraph">

</div>

For the last couple of chapters, we've been working just with lists of
numbers. Obviously, interesting programs also need to be able to
manipulate lists with elements from other types — lists of strings,
lists of booleans, lists of lists, etc. We *could* just define a new
inductive datatype for each of these, for example...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">boollist</span> : <span class="id" type="keyword">Type</span>
:=\
   | <span class="id" type="var">bool\_nil</span> : <span class="id"
type="var">boollist</span>\
   | <span class="id" type="var">bool\_cons</span> : <span class="id"
type="var">bool</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">boollist</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">boollist</span>.\
\

</div>

<div class="doc">

... but this would quickly become tedious, partly because we have to
make up different constructor names for each datatype, but mostly
because we would also need to define new versions of all our list
manipulating functions (<span class="inlinecode"><span class="id"
type="var">length</span></span>, <span class="inlinecode"><span
class="id" type="var">rev</span></span>, etc.) for each new datatype
definition.
<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

To avoid all this repetition, Coq supports *polymorphic* inductive type
definitions. For example, here is a *polymorphic list* datatype.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">list</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) : <span class="id"
type="keyword">Type</span> :=\
   | <span class="id" type="var">nil</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span>\
   | <span class="id" type="var">cons</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">list</span> <span class="id" type="var">X</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">list</span> <span class="id" type="var">X</span>.\
\

</div>

<div class="doc">

This is exactly like the definition of <span class="inlinecode"><span
class="id" type="var">natlist</span></span> from the previous chapter,
except that the <span class="inlinecode"><span class="id"
type="var">nat</span></span> argument to the <span
class="inlinecode"><span class="id" type="var">cons</span></span>
constructor has been replaced by an arbitrary type <span
class="inlinecode"><span class="id" type="var">X</span></span>, a
binding for <span class="inlinecode"><span class="id"
type="var">X</span></span> has been added to the header, and the
occurrences of <span class="inlinecode"><span class="id"
type="var">natlist</span></span> in the types of the constructors have
been replaced by <span class="inlinecode"><span class="id"
type="var">list</span></span> <span class="inlinecode"><span class="id"
type="var">X</span></span>. (We can re-use the constructor names <span
class="inlinecode"><span class="id" type="var">nil</span></span> and
<span class="inlinecode"><span class="id" type="var">cons</span></span>
because the earlier definition of <span class="inlinecode"><span
class="id" type="var">natlist</span></span> was inside of a <span
class="inlinecode"><span class="id" type="keyword">Module</span></span>
definition that is now out of scope.)
<div class="paragraph">

</div>

What sort of thing is <span class="inlinecode"><span class="id"
type="var">list</span></span> itself? One good way to think about it is
that <span class="inlinecode"><span class="id"
type="var">list</span></span> is a *function* from <span
class="inlinecode"><span class="id" type="keyword">Type</span></span>s
to <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> definitions; or, to put it
another way, <span class="inlinecode"><span class="id"
type="var">list</span></span> is a function from <span
class="inlinecode"><span class="id" type="keyword">Type</span></span>s
to <span class="inlinecode"><span class="id"
type="keyword">Type</span></span>s. For any particular type <span
class="inlinecode"><span class="id" type="var">X</span></span>, the type
<span class="inlinecode"><span class="id" type="var">list</span></span>
<span class="inlinecode"><span class="id" type="var">X</span></span> is
an <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span>ly defined set of lists whose
elements are things of type <span class="inlinecode"><span class="id"
type="var">X</span></span>.
<div class="paragraph">

</div>

With this definition, when we use the constructors <span
class="inlinecode"><span class="id" type="var">nil</span></span> and
<span class="inlinecode"><span class="id" type="var">cons</span></span>
to build lists, we need to tell Coq the type of the elements in the
lists we are building — that is, <span class="inlinecode"><span
class="id" type="var">nil</span></span> and <span
class="inlinecode"><span class="id" type="var">cons</span></span> are
now *polymorphic constructors*. Observe the types of these constructors:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">nil</span>.\
 <span
class="comment">(\* ===\> nil : forall X : Type, list X \*)</span>\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">cons</span>.\
 <span
class="comment">(\* ===\> cons : forall X : Type, X -\> list X -\> list X \*)</span>\
\

</div>

<div class="doc">

The "<span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span>" in these
types can be read as an additional argument to the constructors that
determines the expected types of the arguments that follow. When <span
class="inlinecode"><span class="id" type="var">nil</span></span> and
<span class="inlinecode"><span class="id" type="var">cons</span></span>
are used, these arguments are supplied in the same way as the others.
For example, the list containing <span class="inlinecode">2</span> and
<span class="inlinecode">1</span> is written like this:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> (<span class="id"
type="var">cons</span> <span class="id" type="var">nat</span> 2 (<span
class="id" type="var">cons</span> <span class="id" type="var">nat</span>
1 (<span class="id" type="var">nil</span> <span class="id"
type="var">nat</span>))).\
\

</div>

<div class="doc">

(We've gone back to writing <span class="inlinecode"><span class="id"
type="var">nil</span></span> and <span class="inlinecode"><span
class="id" type="var">cons</span></span> explicitly here because we
haven't yet defined the <span class="inlinecode"></span> <span
class="inlinecode">[]</span> <span class="inlinecode"></span> and <span
class="inlinecode">::</span> notations for the new version of lists.
We'll do that in a bit.)
<div class="paragraph">

</div>

We can now go back and make polymorphic (or "generic") versions of all
the list-processing functions that we wrote before. Here is <span
class="inlinecode"><span class="id" type="var">length</span></span>, for
example:
<div class="paragraph">

</div>

###  {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">length</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) (<span class="id"
type="var">l</span>:<span class="id" type="var">list</span> <span
class="id" type="var">X</span>) : <span class="id" type="var">nat</span>
:=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ 0\
   | <span class="id" type="var">cons</span> <span class="id"
type="var">h</span> <span class="id" type="var">t</span> ⇒ <span
class="id" type="var">S</span> (<span class="id"
type="var">length</span> <span class="id" type="var">X</span> <span
class="id" type="var">t</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Note that the uses of <span class="inlinecode"><span class="id"
type="var">nil</span></span> and <span class="inlinecode"><span
class="id" type="var">cons</span></span> in <span
class="inlinecode"><span class="id" type="keyword">match</span></span>
patterns do not require any type annotations: Coq already knows that the
list <span class="inlinecode"><span class="id"
type="var">l</span></span> contains elements of type <span
class="inlinecode"><span class="id" type="var">X</span></span>, so
there's no reason to include <span class="inlinecode"><span class="id"
type="var">X</span></span> in the pattern. (More precisely, the type
<span class="inlinecode"><span class="id" type="var">X</span></span> is
a parameter of the whole definition of <span class="inlinecode"><span
class="id" type="var">list</span></span>, not of the individual
constructors. We'll come back to this point later.)
<div class="paragraph">

</div>

As with <span class="inlinecode"><span class="id"
type="var">nil</span></span> and <span class="inlinecode"><span
class="id" type="var">cons</span></span>, we can use <span
class="inlinecode"><span class="id" type="var">length</span></span> by
applying it first to a type and then to its list argument:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_length1</span> :\
     <span class="id" type="var">length</span> <span class="id"
type="var">nat</span> (<span class="id" type="var">cons</span> <span
class="id" type="var">nat</span> 1 (<span class="id"
type="var">cons</span> <span class="id" type="var">nat</span> 2 (<span
class="id" type="var">nil</span> <span class="id"
type="var">nat</span>))) = 2.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

To use our length with other kinds of lists, we simply instantiate it
with an appropriate type parameter:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_length2</span> :\
     <span class="id" type="var">length</span> <span class="id"
type="var">bool</span> (<span class="id" type="var">cons</span> <span
class="id" type="var">bool</span> <span class="id"
type="var">true</span> (<span class="id" type="var">nil</span> <span
class="id" type="var">bool</span>)) = 1.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

Let's close this subsection by re-implementing a few other standard list
functions on our new polymorphic lists:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">app</span> (<span class="id" type="var">X</span> : <span
class="id" type="keyword">Type</span>) (<span class="id"
type="var">l1</span> <span class="id" type="var">l2</span> : <span
class="id" type="var">list</span> <span class="id" type="var">X</span>)\
                 : (<span class="id" type="var">list</span> <span
class="id" type="var">X</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l1</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">l2</span>\
   | <span class="id" type="var">cons</span> <span class="id"
type="var">h</span> <span class="id" type="var">t</span> ⇒ <span
class="id" type="var">cons</span> <span class="id" type="var">X</span>
<span class="id" type="var">h</span> (<span class="id"
type="var">app</span> <span class="id" type="var">X</span> <span
class="id" type="var">t</span> <span class="id" type="var">l2</span>)\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">snoc</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) (<span class="id"
type="var">l</span>:<span class="id" type="var">list</span> <span
class="id" type="var">X</span>) (<span class="id"
type="var">v</span>:<span class="id" type="var">X</span>) : (<span
class="id" type="var">list</span> <span class="id" type="var">X</span>)
:=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">cons</span> <span class="id" type="var">X</span> <span
class="id" type="var">v</span> (<span class="id" type="var">nil</span>
<span class="id" type="var">X</span>)\
   | <span class="id" type="var">cons</span> <span class="id"
type="var">h</span> <span class="id" type="var">t</span> ⇒ <span
class="id" type="var">cons</span> <span class="id" type="var">X</span>
<span class="id" type="var">h</span> (<span class="id"
type="var">snoc</span> <span class="id" type="var">X</span> <span
class="id" type="var">t</span> <span class="id" type="var">v</span>)\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">rev</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) (<span class="id"
type="var">l</span>:<span class="id" type="var">list</span> <span
class="id" type="var">X</span>) : <span class="id"
type="var">list</span> <span class="id" type="var">X</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">nil</span> <span class="id" type="var">X</span>\
   | <span class="id" type="var">cons</span> <span class="id"
type="var">h</span> <span class="id" type="var">t</span> ⇒ <span
class="id" type="var">snoc</span> <span class="id" type="var">X</span>
(<span class="id" type="var">rev</span> <span class="id"
type="var">X</span> <span class="id" type="var">t</span>) <span
class="id" type="var">h</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_rev1</span> :\
     <span class="id" type="var">rev</span> <span class="id"
type="var">nat</span> (<span class="id" type="var">cons</span> <span
class="id" type="var">nat</span> 1 (<span class="id"
type="var">cons</span> <span class="id" type="var">nat</span> 2 (<span
class="id" type="var">nil</span> <span class="id"
type="var">nat</span>)))\
   = (<span class="id" type="var">cons</span> <span class="id"
type="var">nat</span> 2 (<span class="id" type="var">cons</span> <span
class="id" type="var">nat</span> 1 (<span class="id"
type="var">nil</span> <span class="id" type="var">nat</span>))).\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_rev2</span>:\
   <span class="id" type="var">rev</span> <span class="id"
type="var">bool</span> (<span class="id" type="var">nil</span> <span
class="id" type="var">bool</span>) = <span class="id"
type="var">nil</span> <span class="id" type="var">bool</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">MumbleBaz</span>.\

</div>

<div class="doc">

#### Exercise: 2 stars (mumble\_grumble) {.section}

Consider the following two inductively defined types.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">mumble</span> : <span class="id" type="keyword">Type</span>
:=\
   | <span class="id" type="var">a</span> : <span class="id"
type="var">mumble</span>\
   | <span class="id" type="var">b</span> : <span class="id"
type="var">mumble</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">mumble</span>\
   | <span class="id" type="var">c</span> : <span class="id"
type="var">mumble</span>.\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">grumble</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) : <span class="id"
type="keyword">Type</span> :=\
   | <span class="id" type="var">d</span> : <span class="id"
type="var">mumble</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">grumble</span> <span class="id"
type="var">X</span>\
   | <span class="id" type="var">e</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">grumble</span> <span class="id"
type="var">X</span>.\
\

</div>

<div class="doc">

Which of the following are well-typed elements of <span
class="inlinecode"><span class="id" type="var">grumble</span></span>
<span class="inlinecode"><span class="id" type="var">X</span></span> for
some type <span class="inlinecode"><span class="id"
type="var">X</span></span>?
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">d</span></span>
    <span class="inlinecode">(<span class="id"
    type="var">b</span></span> <span class="inlinecode"><span class="id"
    type="var">a</span></span> <span class="inlinecode">5)</span>
-   <span class="inlinecode"><span class="id" type="var">d</span></span>
    <span class="inlinecode"><span class="id"
    type="var">mumble</span></span> <span class="inlinecode">(<span
    class="id" type="var">b</span></span> <span class="inlinecode"><span
    class="id" type="var">a</span></span> <span
    class="inlinecode">5)</span>
-   <span class="inlinecode"><span class="id" type="var">d</span></span>
    <span class="inlinecode"><span class="id"
    type="var">bool</span></span> <span class="inlinecode">(<span
    class="id" type="var">b</span></span> <span class="inlinecode"><span
    class="id" type="var">a</span></span> <span
    class="inlinecode">5)</span>
-   <span class="inlinecode"><span class="id" type="var">e</span></span>
    <span class="inlinecode"><span class="id"
    type="var">bool</span></span> <span class="inlinecode"><span
    class="id" type="var">true</span></span>
-   <span class="inlinecode"><span class="id" type="var">e</span></span>
    <span class="inlinecode"><span class="id"
    type="var">mumble</span></span> <span class="inlinecode">(<span
    class="id" type="var">b</span></span> <span class="inlinecode"><span
    class="id" type="var">c</span></span> <span
    class="inlinecode">0)</span>
-   <span class="inlinecode"><span class="id" type="var">e</span></span>
    <span class="inlinecode"><span class="id"
    type="var">bool</span></span> <span class="inlinecode">(<span
    class="id" type="var">b</span></span> <span class="inlinecode"><span
    class="id" type="var">c</span></span> <span
    class="inlinecode">0)</span>
-   <span class="inlinecode"><span class="id" type="var">c</span></span>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (baz\_num\_elts) {.section}

Consider the following inductive definition:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">baz</span> : <span class="id" type="keyword">Type</span> :=\
    | <span class="id" type="var">x</span> : <span class="id"
type="var">baz</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">baz</span>\
    | <span class="id" type="var">y</span> : <span class="id"
type="var">baz</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">bool</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">baz</span>.\
\

</div>

<div class="doc">

How *many* elements does the type <span class="inlinecode"><span
class="id" type="var">baz</span></span> have? <span
class="comment">(\* FILL IN HERE \*)</span>\
 ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">MumbleBaz</span>.\
\

</div>

<div class="doc">

### Type Annotation Inference {.section}

<div class="paragraph">

</div>

Let's write the definition of <span class="inlinecode"><span class="id"
type="var">app</span></span> again, but this time we won't specify the
types of any of the arguments. Will Coq still accept it?

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">app'</span> <span class="id" type="var">X</span> <span
class="id" type="var">l1</span> <span class="id" type="var">l2</span> :
<span class="id" type="var">list</span> <span class="id"
type="var">X</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l1</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">l2</span>\
   | <span class="id" type="var">cons</span> <span class="id"
type="var">h</span> <span class="id" type="var">t</span> ⇒ <span
class="id" type="var">cons</span> <span class="id" type="var">X</span>
<span class="id" type="var">h</span> (<span class="id"
type="var">app'</span> <span class="id" type="var">X</span> <span
class="id" type="var">t</span> <span class="id" type="var">l2</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Indeed it will. Let's see what type Coq has assigned to <span
class="inlinecode"><span class="id" type="var">app'</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">app'</span>.\
 <span
class="comment">(\* ===\> forall X : Type, list X -\> list X -\> list X \*)</span>\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">app</span>.\
 <span
class="comment">(\* ===\> forall X : Type, list X -\> list X -\> list X \*)</span>\
\

</div>

<div class="doc">

It has exactly the same type type as <span class="inlinecode"><span
class="id" type="var">app</span></span>. Coq was able to use a process
called *type inference* to deduce what the types of <span
class="inlinecode"><span class="id" type="var">X</span></span>, <span
class="inlinecode"><span class="id" type="var">l1</span></span>, and
<span class="inlinecode"><span class="id" type="var">l2</span></span>
must be, based on how they are used. For example, since <span
class="inlinecode"><span class="id" type="var">X</span></span> is used
as an argument to <span class="inlinecode"><span class="id"
type="var">cons</span></span>, it must be a <span
class="inlinecode"><span class="id" type="keyword">Type</span></span>,
since <span class="inlinecode"><span class="id"
type="var">cons</span></span> expects a <span class="inlinecode"><span
class="id" type="keyword">Type</span></span> as its first argument;
matching <span class="inlinecode"><span class="id"
type="var">l1</span></span> with <span class="inlinecode"><span
class="id" type="var">nil</span></span> and <span
class="inlinecode"><span class="id" type="var">cons</span></span> means
it must be a <span class="inlinecode"><span class="id"
type="var">list</span></span>; and so on.
<div class="paragraph">

</div>

This powerful facility means we don't always have to write explicit type
annotations everywhere, although explicit type annotations are still
quite useful as documentation and sanity checks. You should try to find
a balance in your own code between too many type annotations (so many
that they clutter and distract) and too few (which forces readers to
perform type inference in their heads in order to understand your code).

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Type Argument Synthesis {.section}

<div class="paragraph">

</div>

Whenever we use a polymorphic function, we need to pass it one or more
types in addition to its other arguments. For example, the recursive
call in the body of the <span class="inlinecode"><span class="id"
type="var">length</span></span> function above must pass along the type
<span class="inlinecode"><span class="id" type="var">X</span></span>.
But just like providing explicit type annotations everywhere, this is
heavy and verbose. Since the second argument to <span
class="inlinecode"><span class="id" type="var">length</span></span> is a
list of <span class="inlinecode"><span class="id"
type="var">X</span></span>s, it seems entirely obvious that the first
argument can only be <span class="inlinecode"><span class="id"
type="var">X</span></span> — why should we have to write it explicitly?
<div class="paragraph">

</div>

Fortunately, Coq permits us to avoid this kind of redundancy. In place
of any type argument we can write the "implicit argument" <span
class="inlinecode"><span class="id" type="var">\_</span></span>, which
can be read as "Please figure out for yourself what type belongs here."
More precisely, when Coq encounters a <span class="inlinecode"><span
class="id" type="var">\_</span></span>, it will attempt to *unify* all
locally available information — the type of the function being applied,
the types of the other arguments, and the type expected by the context
in which the application appears — to determine what concrete type
should replace the <span class="inlinecode"><span class="id"
type="var">\_</span></span>.
<div class="paragraph">

</div>

This may sound similar to type annotation inference — and, indeed, the
two procedures rely on the same underlying mechanisms. Instead of simply
omitting the types of some arguments to a function, like
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">app'</span> <span class="id"
type="var">X</span> <span class="id" type="var">l1</span> <span
class="id" type="var">l2</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span> :=
<div class="paragraph">

</div>

</div>

we can also replace the types with <span class="inlinecode"><span
class="id" type="var">\_</span></span>, like
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">app'</span> (<span class="id"
type="var">X</span> : <span class="id" type="var">\_</span>) (<span
class="id" type="var">l1</span> <span class="id"
type="var">l2</span> : <span class="id" type="var">\_</span>) : <span
class="id" type="var">list</span> <span class="id"
type="var">X</span> :=
<div class="paragraph">

</div>

</div>

which tells Coq to attempt to infer the missing information, just as
with argument synthesis.
<div class="paragraph">

</div>

Using implicit arguments, the <span class="inlinecode"><span class="id"
type="var">length</span></span> function can be written like this:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">length'</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) (<span class="id"
type="var">l</span>:<span class="id" type="var">list</span> <span
class="id" type="var">X</span>) : <span class="id" type="var">nat</span>
:=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ 0\
   | <span class="id" type="var">cons</span> <span class="id"
type="var">h</span> <span class="id" type="var">t</span> ⇒ <span
class="id" type="var">S</span> (<span class="id"
type="var">length'</span> <span class="id" type="var">\_</span> <span
class="id" type="var">t</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

In this instance, we don't save much by writing <span
class="inlinecode"><span class="id" type="var">\_</span></span> instead
of <span class="inlinecode"><span class="id" type="var">X</span></span>.
But in many cases the difference can be significant. For example,
suppose we want to write down a list containing the numbers <span
class="inlinecode">1</span>, <span class="inlinecode">2</span>, and
<span class="inlinecode">3</span>. Instead of writing this...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">list123</span> :=\
   <span class="id" type="var">cons</span> <span class="id"
type="var">nat</span> 1 (<span class="id" type="var">cons</span> <span
class="id" type="var">nat</span> 2 (<span class="id"
type="var">cons</span> <span class="id" type="var">nat</span> 3 (<span
class="id" type="var">nil</span> <span class="id"
type="var">nat</span>))).\
\

</div>

<div class="doc">

...we can use argument synthesis to write this:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">list123'</span> := <span class="id" type="var">cons</span>
<span class="id" type="var">\_</span> 1 (<span class="id"
type="var">cons</span> <span class="id" type="var">\_</span> 2 (<span
class="id" type="var">cons</span> <span class="id" type="var">\_</span>
3 (<span class="id" type="var">nil</span> <span class="id"
type="var">\_</span>))).\
\

</div>

<div class="doc">

### Implicit Arguments {.section}

<div class="paragraph">

</div>

In fact, we can go further. To avoid having to sprinkle <span
class="inlinecode"><span class="id" type="var">\_</span></span>'s
throughout our programs, we can tell Coq *always* to infer the type
argument(s) of a given function. The <span class="inlinecode"><span
class="id" type="var">Arguments</span></span> directive specifies the
name of the function or constructor, and then lists its argument names,
with curly braces around any arguments to be treated as implicit.

</div>

<div class="code code-tight">

\
 <span class="id" type="var">Arguments</span> <span class="id"
type="var">nil</span> {<span class="id" type="var">X</span>}.\
 <span class="id" type="var">Arguments</span> <span class="id"
type="var">cons</span> {<span class="id" type="var">X</span>} <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>.
<span
class="comment">(\* use underscore for argument position that has no name \*)</span>\
 <span class="id" type="var">Arguments</span> <span class="id"
type="var">length</span> {<span class="id" type="var">X</span>} <span
class="id" type="var">l</span>.\
 <span class="id" type="var">Arguments</span> <span class="id"
type="var">app</span> {<span class="id" type="var">X</span>} <span
class="id" type="var">l1</span> <span class="id" type="var">l2</span>.\
 <span class="id" type="var">Arguments</span> <span class="id"
type="var">rev</span> {<span class="id" type="var">X</span>} <span
class="id" type="var">l</span>.\
 <span class="id" type="var">Arguments</span> <span class="id"
type="var">snoc</span> {<span class="id" type="var">X</span>} <span
class="id" type="var">l</span> <span class="id" type="var">v</span>.\
\
 <span class="comment">(\* note: no \_ arguments required... \*)</span>\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">list123''</span> := <span class="id" type="var">cons</span> 1
(<span class="id" type="var">cons</span> 2 (<span class="id"
type="var">cons</span> 3 <span class="id" type="var">nil</span>)).\
 <span class="id" type="keyword">Check</span> (<span class="id"
type="var">length</span> <span class="id" type="var">list123''</span>).\
\

</div>

<div class="doc">

###  {.section}

<div class="paragraph">

</div>

Alternatively, we can declare an argument to be implicit while defining
the function itself, by surrounding the argument in curly braces. For
example:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">length''</span> {<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">l</span>:<span class="id" type="var">list</span> <span
class="id" type="var">X</span>) : <span class="id" type="var">nat</span>
:=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ 0\
   | <span class="id" type="var">cons</span> <span class="id"
type="var">h</span> <span class="id" type="var">t</span> ⇒ <span
class="id" type="var">S</span> (<span class="id"
type="var">length''</span> <span class="id" type="var">t</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

(Note that we didn't even have to provide a type argument to the
recursive call to <span class="inlinecode"><span class="id"
type="var">length''</span></span>; indeed, it is invalid to provide
one.) We will use this style whenever possible, although we will
continue to use use explicit <span class="inlinecode"><span class="id"
type="var">Argument</span></span> declarations for <span
class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> constructors.
<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

One small problem with declaring arguments <span
class="inlinecode"><span class="id"
type="keyword">Implicit</span></span> is that, occasionally, Coq does
not have enough local information to determine a type argument; in such
cases, we need to tell Coq that we want to give the argument explicitly
this time, even though we've globally declared it to be <span
class="inlinecode"><span class="id"
type="keyword">Implicit</span></span>. For example, suppose we write
this:

</div>

<div class="code code-tight">

\
 <span class="comment">(\* Definition mynil := nil.  \*)</span>\
\

</div>

<div class="doc">

If we uncomment this definition, Coq will give us an error, because it
doesn't know what type argument to supply to <span
class="inlinecode"><span class="id" type="var">nil</span></span>. We can
help it by providing an explicit type declaration (so that Coq has more
information available when it gets to the "application" of <span
class="inlinecode"><span class="id" type="var">nil</span></span>):

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">mynil</span> : <span class="id" type="var">list</span> <span
class="id" type="var">nat</span> := <span class="id"
type="var">nil</span>.\
\

</div>

<div class="doc">

Alternatively, we can force the implicit arguments to be explicit by
prefixing the function name with <span class="inlinecode">@</span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> @<span class="id"
type="var">nil</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">mynil'</span> := @<span class="id" type="var">nil</span>
<span class="id" type="var">nat</span>.\
\

</div>

<div class="doc">

###  {.section}

Using argument synthesis and implicit arguments, we can define
convenient notation for lists, as before. Since we have made the
constructor type arguments implicit, Coq will know to automatically
infer these when we use the notations.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "x :: y" := (<span
class="id" type="var">cons</span> <span class="id" type="var">x</span>
<span class="id" type="var">y</span>)\
                      (<span class="id" type="tactic">at</span> <span
class="id" type="var">level</span> 60, <span class="id"
type="var">right</span> <span class="id"
type="var">associativity</span>).\
 <span class="id" type="keyword">Notation</span> "[ ]" := <span
class="id" type="var">nil</span>.\
 <span class="id" type="keyword">Notation</span> "[ x ; .. ; y ]" :=
(<span class="id" type="var">cons</span> <span class="id"
type="var">x</span> .. (<span class="id" type="var">cons</span> <span
class="id" type="var">y</span> []) ..).\
 <span class="id" type="keyword">Notation</span> "x ++ y" := (<span
class="id" type="var">app</span> <span class="id" type="var">x</span>
<span class="id" type="var">y</span>)\
                      (<span class="id" type="tactic">at</span> <span
class="id" type="var">level</span> 60, <span class="id"
type="var">right</span> <span class="id"
type="var">associativity</span>).\
\

</div>

<div class="doc">

Now lists can be written just the way we'd hope:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">list123'''</span> := [1; 2; 3].\
\

</div>

<div class="doc">

### Exercises: Polymorphic Lists {.section}

<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (poly\_exercises) {.section}

Here are a few simple exercises, just like ones in the <span
class="inlinecode"><span class="id" type="var">Lists</span></span>
chapter, for practice with polymorphism. Fill in the definitions and
complete the proofs below.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="tactic">repeat</span> {<span class="id" type="var">X</span> :
<span class="id" type="keyword">Type</span>} (<span class="id"
type="var">n</span> : <span class="id" type="var">X</span>) (<span
class="id" type="var">count</span> : <span class="id"
type="var">nat</span>) : <span class="id" type="var">list</span> <span
class="id" type="var">X</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_repeat1</span>:\
   <span class="id" type="tactic">repeat</span> <span class="id"
type="var">true</span> 2 = <span class="id" type="var">cons</span> <span
class="id" type="var">true</span> (<span class="id"
type="var">cons</span> <span class="id" type="var">true</span> <span
class="id" type="var">nil</span>).\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">nil\_app</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>, <span
style="font-family: arial;">∀</span><span class="id"
type="var">l</span>:<span class="id" type="var">list</span> <span
class="id" type="var">X</span>,\
   <span class="id" type="var">app</span> [] <span class="id"
type="var">l</span> = <span class="id" type="var">l</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">rev\_snoc</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">X</span>
: <span class="id" type="keyword">Type</span>,\
                      <span style="font-family: arial;">∀</span><span
class="id" type="var">v</span> : <span class="id" type="var">X</span>,\
                      <span style="font-family: arial;">∀</span><span
class="id" type="var">s</span> : <span class="id" type="var">list</span>
<span class="id" type="var">X</span>,\
   <span class="id" type="var">rev</span> (<span class="id"
type="var">snoc</span> <span class="id" type="var">s</span> <span
class="id" type="var">v</span>) = <span class="id" type="var">v</span>
:: (<span class="id" type="var">rev</span> <span class="id"
type="var">s</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">rev\_involutive</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">X</span>
: <span class="id" type="keyword">Type</span>, <span
style="font-family: arial;">∀</span><span class="id" type="var">l</span>
: <span class="id" type="var">list</span> <span class="id"
type="var">X</span>,\
   <span class="id" type="var">rev</span> (<span class="id"
type="var">rev</span> <span class="id" type="var">l</span>) = <span
class="id" type="var">l</span>.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">snoc\_with\_append</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">X</span>
: <span class="id" type="keyword">Type</span>,\
                          <span
style="font-family: arial;">∀</span><span class="id"
type="var">l1</span> <span class="id" type="var">l2</span> : <span
class="id" type="var">list</span> <span class="id" type="var">X</span>,\
                          <span
style="font-family: arial;">∀</span><span class="id" type="var">v</span>
: <span class="id" type="var">X</span>,\
   <span class="id" type="var">snoc</span> (<span class="id"
type="var">l1</span> ++ <span class="id" type="var">l2</span>) <span
class="id" type="var">v</span> = <span class="id"
type="var">l1</span> ++ (<span class="id" type="var">snoc</span> <span
class="id" type="var">l2</span> <span class="id" type="var">v</span>).\
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

Polymorphic Pairs {.section}
-----------------

<div class="paragraph">

</div>

Following the same pattern, the type definition we gave in the last
chapter for pairs of numbers can be generalized to *polymorphic pairs*
(or *products*):

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">prod</span> (<span class="id" type="var">X</span> <span
class="id" type="var">Y</span> : <span class="id"
type="keyword">Type</span>) : <span class="id"
type="keyword">Type</span> :=\
   <span class="id" type="var">pair</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Y</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">prod</span> <span class="id" type="var">X</span> <span
class="id" type="var">Y</span>.\
\
 <span class="id" type="var">Arguments</span> <span class="id"
type="var">pair</span> {<span class="id" type="var">X</span>} {<span
class="id" type="var">Y</span>} <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span>.\
\

</div>

<div class="doc">

As with lists, we make the type arguments implicit and define the
familiar concrete notation.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "( x , y )" := (<span
class="id" type="var">pair</span> <span class="id" type="var">x</span>
<span class="id" type="var">y</span>).\
\

</div>

<div class="doc">

We can also use the <span class="inlinecode"><span class="id"
type="keyword">Notation</span></span> mechanism to define the standard
notation for pair *types*:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "X × Y" := (<span
class="id" type="var">prod</span> <span class="id" type="var">X</span>
<span class="id" type="var">Y</span>) : <span class="id"
type="var">type\_scope</span>.\
\

</div>

<div class="doc">

(The annotation <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">type\_scope</span></span>
tells Coq that this abbreviation should be used when parsing types. This
avoids a clash with the multiplication symbol.)
<div class="paragraph">

</div>

###  {.section}

A note of caution: it is easy at first to get <span
class="inlinecode">(<span class="id" type="var">x</span>,<span
class="id" type="var">y</span>)</span> and <span
class="inlinecode"><span class="id" type="var">X</span>×<span class="id"
type="var">Y</span></span> confused. Remember that <span
class="inlinecode">(<span class="id" type="var">x</span>,<span
class="id" type="var">y</span>)</span> is a *value* built from two other
values; <span class="inlinecode"><span class="id"
type="var">X</span>×<span class="id" type="var">Y</span></span> is a
*type* built from two other types. If <span class="inlinecode"><span
class="id" type="var">x</span></span> has type <span
class="inlinecode"><span class="id" type="var">X</span></span> and <span
class="inlinecode"><span class="id" type="var">y</span></span> has type
<span class="inlinecode"><span class="id" type="var">Y</span></span>,
then <span class="inlinecode">(<span class="id"
type="var">x</span>,<span class="id" type="var">y</span>)</span> has
type <span class="inlinecode"><span class="id" type="var">X</span>×<span
class="id" type="var">Y</span></span>.
<div class="paragraph">

</div>

The first and second projection functions now look pretty much as they
would in any functional programming language.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">fst</span> {<span class="id" type="var">X</span> <span
class="id" type="var">Y</span> : <span class="id"
type="keyword">Type</span>} (<span class="id" type="var">p</span> :
<span class="id" type="var">X</span> × <span class="id"
type="var">Y</span>) : <span class="id" type="var">X</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">p</span> <span class="id" type="keyword">with</span> (<span
class="id" type="var">x</span>,<span class="id" type="var">y</span>) ⇒
<span class="id" type="var">x</span> <span class="id"
type="keyword">end</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">snd</span> {<span class="id" type="var">X</span> <span
class="id" type="var">Y</span> : <span class="id"
type="keyword">Type</span>} (<span class="id" type="var">p</span> :
<span class="id" type="var">X</span> × <span class="id"
type="var">Y</span>) : <span class="id" type="var">Y</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">p</span> <span class="id" type="keyword">with</span> (<span
class="id" type="var">x</span>,<span class="id" type="var">y</span>) ⇒
<span class="id" type="var">y</span> <span class="id"
type="keyword">end</span>.\
\

</div>

<div class="doc">

The following function takes two lists and combines them into a list of
pairs. In many functional programming languages, it is called <span
class="inlinecode"><span class="id" type="var">zip</span></span>. We
call it <span class="inlinecode"><span class="id"
type="var">combine</span></span> for consistency with Coq's standard
library. Note that the pair notation can be used both in expressions and
in patterns...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">combine</span> {<span class="id" type="var">X</span> <span
class="id" type="var">Y</span> : <span class="id"
type="keyword">Type</span>} (<span class="id" type="var">lx</span> :
<span class="id" type="var">list</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">ly</span> : <span
class="id" type="var">list</span> <span class="id" type="var">Y</span>)\
            : <span class="id" type="var">list</span> (<span class="id"
type="var">X</span>×<span class="id" type="var">Y</span>) :=\
   <span class="id" type="keyword">match</span> (<span class="id"
type="var">lx</span>,<span class="id" type="var">ly</span>) <span
class="id" type="keyword">with</span>\
   | ([],\_) ⇒ []\
   | (<span class="id" type="var">\_</span>,[]) ⇒ []\
   | (<span class="id" type="var">x</span>::<span class="id"
type="var">tx</span>, <span class="id" type="var">y</span>::<span
class="id" type="var">ty</span>) ⇒ (<span class="id"
type="var">x</span>,<span class="id" type="var">y</span>) :: (<span
class="id" type="var">combine</span> <span class="id"
type="var">tx</span> <span class="id" type="var">ty</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star, optional (combine\_checks) {.section}

Try answering the following questions on paper and checking your answers
in coq:
<div class="paragraph">

</div>

-   What is the type of <span class="inlinecode"><span class="id"
    type="var">combine</span></span> (i.e., what does <span
    class="inlinecode"><span class="id"
    type="keyword">Check</span></span> <span class="inlinecode">@<span
    class="id" type="var">combine</span></span> print?)
-   What does
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="keyword">Eval</span> <span class="id"
    type="tactic">compute</span> <span class="id"
    type="keyword">in</span> (<span class="id"
    type="var">combine</span> [1;2] [<span class="id"
    type="var">false</span>;<span class="id"
    type="var">false</span>;<span class="id"
    type="var">true</span>;<span class="id" type="var">true</span>]).
    <div class="paragraph">

    </div>

    </div>

    print? ☐

<div class="paragraph">

</div>

#### Exercise: 2 stars (split) {.section}

The function <span class="inlinecode"><span class="id"
type="tactic">split</span></span> is the right inverse of combine: it
takes a list of pairs and returns a pair of lists. In many functional
programing languages, this function is called <span
class="inlinecode"><span class="id" type="var">unzip</span></span>.
<div class="paragraph">

</div>

Uncomment the material below and fill in the definition of <span
class="inlinecode"><span class="id" type="tactic">split</span></span>.
Make sure it passes the given unit tests.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="tactic">split</span>\
            {<span class="id" type="var">X</span> <span class="id"
type="var">Y</span> : <span class="id" type="keyword">Type</span>}
(<span class="id" type="var">l</span> : <span class="id"
type="var">list</span> (<span class="id" type="var">X</span>×<span
class="id" type="var">Y</span>))\
            : (<span class="id" type="var">list</span> <span class="id"
type="var">X</span>) × (<span class="id" type="var">list</span> <span
class="id" type="var">Y</span>) :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_split</span>:\
   <span class="id" type="tactic">split</span> [(1,<span class="id"
type="var">false</span>);(2,<span class="id" type="var">false</span>)] =
([1;2],[<span class="id" type="var">false</span>;<span class="id"
type="var">false</span>]).\
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

Polymorphic Options {.section}
-------------------

<div class="paragraph">

</div>

One last polymorphic type for now: *polymorphic options*. The type
declaration generalizes the one for <span class="inlinecode"><span
class="id" type="var">natoption</span></span> in the previous chapter:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">option</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) : <span class="id"
type="keyword">Type</span> :=\
   | <span class="id" type="var">Some</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">option</span> <span class="id"
type="var">X</span>\
   | <span class="id" type="var">None</span> : <span class="id"
type="var">option</span> <span class="id" type="var">X</span>.\
\
 <span class="id" type="var">Arguments</span> <span class="id"
type="var">Some</span> {<span class="id" type="var">X</span>} <span
class="id" type="var">\_</span>.\
 <span class="id" type="var">Arguments</span> <span class="id"
type="var">None</span> {<span class="id" type="var">X</span>}.\
\

</div>

<div class="doc">

###  {.section}

We can now rewrite the <span class="inlinecode"><span class="id"
type="var">index</span></span> function so that it works with any type
of lists.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">index</span> {<span class="id" type="var">X</span> : <span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>)\
                (<span class="id" type="var">l</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span>) : <span
class="id" type="var">option</span> <span class="id" type="var">X</span>
:=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | [] ⇒ <span class="id" type="var">None</span>\
   | <span class="id" type="var">a</span> :: <span class="id"
type="var">l'</span> ⇒ <span class="id" type="keyword">if</span> <span
class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">O</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">Some</span> <span class="id" type="var">a</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">index</span> (<span class="id" type="var">pred</span> <span
class="id" type="var">n</span>) <span class="id" type="var">l'</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_index1</span> : <span class="id"
type="var">index</span> 0 [4;5;6;7] = <span class="id"
type="var">Some</span> 4.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_index2</span> : <span class="id"
type="var">index</span> 1 [[1];[2]] = <span class="id"
type="var">Some</span> [2].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_index3</span> : <span class="id"
type="var">index</span> 2 [<span class="id" type="var">true</span>] =
<span class="id" type="var">None</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star, optional (hd\_opt\_poly) {.section}

Complete the definition of a polymorphic version of the <span
class="inlinecode"><span class="id" type="var">hd\_opt</span></span>
function from the last chapter. Be sure that it passes the unit tests
below.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">hd\_opt</span> {<span class="id" type="var">X</span> : <span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">l</span> : <span class="id" type="var">list</span> <span
class="id" type="var">X</span>) : <span class="id"
type="var">option</span> <span class="id" type="var">X</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\

</div>

<div class="doc">

Once again, to force the implicit arguments to be explicit, we can use
<span class="inlinecode">@</span> before the name of the function.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> @<span class="id"
type="var">hd\_opt</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_hd\_opt1</span> : <span class="id"
type="var">hd\_opt</span> [1;2] = <span class="id"
type="var">Some</span> 1.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_hd\_opt2</span> : <span class="id"
type="var">hd\_opt</span> [[1];[2]] = <span class="id"
type="var">Some</span> [1].\
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

Functions as Data {.section}
=================

</div>

<div class="code code-space">

</div>

<div class="doc">

Higher-Order Functions {.section}
----------------------

<div class="paragraph">

</div>

Like many other modern programming languages — including all *functional
languages* (ML, Haskell, Scheme, etc.) — Coq treats functions as
first-class citizens, allowing functions to be passed as arguments to
other functions, returned as results, stored in data structures, etc.
<div class="paragraph">

</div>

Functions that manipulate other functions are often called
*higher-order* functions. Here's a simple one:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">doit3times</span> {<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">f</span>:<span class="id" type="var">X</span><span
style="font-family: arial;">→</span><span class="id"
type="var">X</span>) (<span class="id" type="var">n</span>:<span
class="id" type="var">X</span>) : <span class="id" type="var">X</span>
:=\
   <span class="id" type="var">f</span> (<span class="id"
type="var">f</span> (<span class="id" type="var">f</span> <span
class="id" type="var">n</span>)).\
\

</div>

<div class="doc">

The argument <span class="inlinecode"><span class="id"
type="var">f</span></span> here is itself a function (from <span
class="inlinecode"><span class="id" type="var">X</span></span> to <span
class="inlinecode"><span class="id" type="var">X</span></span>); the
body of <span class="inlinecode"><span class="id"
type="var">doit3times</span></span> applies <span
class="inlinecode"><span class="id" type="var">f</span></span> three
times to some value <span class="inlinecode"><span class="id"
type="var">n</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> @<span class="id"
type="var">doit3times</span>.\
 <span
class="comment">(\* ===\> doit3times : forall X : Type, (X -\> X) -\> X -\> X \*)</span>\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_doit3times</span>: <span class="id"
type="var">doit3times</span> <span class="id" type="var">minustwo</span>
9 = 3.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_doit3times'</span>: <span class="id"
type="var">doit3times</span> <span class="id" type="var">negb</span>
<span class="id" type="var">true</span> = <span class="id"
type="var">false</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Partial Application {.section}
-------------------

<div class="paragraph">

</div>

In fact, the multiple-argument functions we have already seen are also
examples of passing functions as data. To see why, recall the type of
<span class="inlinecode"><span class="id" type="var">plus</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">plus</span>.\
 <span class="comment">(\* ==\> nat -\> nat -\> nat \*)</span>\
\

</div>

<div class="doc">

Each <span class="inlinecode"><span
style="font-family: arial;">→</span></span> in this expression is
actually a *binary* operator on types. (This is the same as saying that
Coq primitively supports only one-argument functions — do you see why?)
This operator is *right-associative*, so the type of <span
class="inlinecode"><span class="id" type="var">plus</span></span> is
really a shorthand for <span class="inlinecode"><span class="id"
type="var">nat</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode">(<span class="id" type="var">nat</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">nat</span>)</span>
— i.e., it can be read as saying that "<span class="inlinecode"><span
class="id" type="var">plus</span></span> is a one-argument function that
takes a <span class="inlinecode"><span class="id"
type="var">nat</span></span> and returns a one-argument function that
takes another <span class="inlinecode"><span class="id"
type="var">nat</span></span> and returns a <span
class="inlinecode"><span class="id" type="var">nat</span></span>." In
the examples above, we have always applied <span
class="inlinecode"><span class="id" type="var">plus</span></span> to
both of its arguments at once, but if we like we can supply just the
first. This is called *partial application*.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">plus3</span> := <span class="id" type="var">plus</span> 3.\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">plus3</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_plus3</span> : <span class="id" type="var">plus3</span>
4 = 7.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_plus3'</span> : <span class="id"
type="var">doit3times</span> <span class="id" type="var">plus3</span> 0
= 9.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_plus3''</span> : <span class="id"
type="var">doit3times</span> (<span class="id" type="var">plus</span> 3)
0 = 9.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Digression: Currying {.section}
--------------------

<div class="paragraph">

</div>

#### Exercise: 2 stars, advanced (currying) {.section}

In Coq, a function <span class="inlinecode"><span class="id"
type="var">f</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">A</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">B</span></span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">C</span></span> really
has the type <span class="inlinecode"><span class="id"
type="var">A</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode">(<span class="id" type="var">B</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">C</span>)</span>.
That is, if you give <span class="inlinecode"><span class="id"
type="var">f</span></span> a value of type <span
class="inlinecode"><span class="id" type="var">A</span></span>, it will
give you function <span class="inlinecode"><span class="id"
type="var">f'</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">B</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">C</span></span>. If
you then give <span class="inlinecode"><span class="id"
type="var">f'</span></span> a value of type <span
class="inlinecode"><span class="id" type="var">B</span></span>, it will
return a value of type <span class="inlinecode"><span class="id"
type="var">C</span></span>. This allows for partial application, as in
<span class="inlinecode"><span class="id"
type="var">plus3</span></span>. Processing a list of arguments with
functions that return functions is called *currying*, in honor of the
logician Haskell Curry.
<div class="paragraph">

</div>

Conversely, we can reinterpret the type <span class="inlinecode"><span
class="id" type="var">A</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">B</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">C</span></span> as
<span class="inlinecode">(<span class="id" type="var">A</span></span>
<span class="inlinecode">×</span> <span class="inlinecode"><span
class="id" type="var">B</span>)</span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">C</span></span>. This is
called *uncurrying*. With an uncurried binary function, both arguments
must be given at once as a pair; there is no partial application.
<div class="paragraph">

</div>

We can define currying as follows:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">prod\_curry</span> {<span class="id" type="var">X</span>
<span class="id" type="var">Y</span> <span class="id"
type="var">Z</span> : <span class="id" type="keyword">Type</span>}\
   (<span class="id" type="var">f</span> : <span class="id"
type="var">X</span> × <span class="id" type="var">Y</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Z</span>) (<span class="id" type="var">x</span> : <span
class="id" type="var">X</span>) (<span class="id" type="var">y</span> :
<span class="id" type="var">Y</span>) : <span class="id"
type="var">Z</span> := <span class="id" type="var">f</span> (<span
class="id" type="var">x</span>, <span class="id" type="var">y</span>).\
\

</div>

<div class="doc">

As an exercise, define its inverse, <span class="inlinecode"><span
class="id" type="var">prod\_uncurry</span></span>. Then prove the
theorems below to show that the two are inverses.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">prod\_uncurry</span> {<span class="id" type="var">X</span>
<span class="id" type="var">Y</span> <span class="id"
type="var">Z</span> : <span class="id" type="keyword">Type</span>}\
   (<span class="id" type="var">f</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Y</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Z</span>) (<span class="id" type="var">p</span> : <span
class="id" type="var">X</span> × <span class="id" type="var">Y</span>) :
<span class="id" type="var">Z</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\

</div>

<div class="doc">

(Thought exercise: before running these commands, can you calculate the
types of <span class="inlinecode"><span class="id"
type="var">prod\_curry</span></span> and <span class="inlinecode"><span
class="id" type="var">prod\_uncurry</span></span>?)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> @<span class="id"
type="var">prod\_curry</span>.\
 <span class="id" type="keyword">Check</span> @<span class="id"
type="var">prod\_uncurry</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">uncurry\_curry</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> <span class="id" type="var">Y</span> <span
class="id" type="var">Z</span> : <span class="id"
type="keyword">Type</span>) (<span class="id" type="var">f</span> :
<span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Y</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Z</span>) <span class="id" type="var">x</span>
<span class="id" type="var">y</span>,\
   <span class="id" type="var">prod\_curry</span> (<span class="id"
type="var">prod\_uncurry</span> <span class="id" type="var">f</span>)
<span class="id" type="var">x</span> <span class="id"
type="var">y</span> = <span class="id" type="var">f</span> <span
class="id" type="var">x</span> <span class="id" type="var">y</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">curry\_uncurry</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> <span class="id" type="var">Y</span> <span
class="id" type="var">Z</span> : <span class="id"
type="keyword">Type</span>)\
                                (<span class="id" type="var">f</span> :
(<span class="id" type="var">X</span> × <span class="id"
type="var">Y</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">Z</span>) (<span class="id" type="var">p</span> :
<span class="id" type="var">X</span> × <span class="id"
type="var">Y</span>),\
   <span class="id" type="var">prod\_uncurry</span> (<span class="id"
type="var">prod\_curry</span> <span class="id" type="var">f</span>)
<span class="id" type="var">p</span> = <span class="id"
type="var">f</span> <span class="id" type="var">p</span>.\
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

Filter {.section}
------

<div class="paragraph">

</div>

Here is a useful higher-order function, which takes a list of <span
class="inlinecode"><span class="id" type="var">X</span></span>s and a
*predicate* on <span class="inlinecode"><span class="id"
type="var">X</span></span> (a function from <span
class="inlinecode"><span class="id" type="var">X</span></span> to <span
class="inlinecode"><span class="id" type="var">bool</span></span>) and
"filters" the list, returning a new list containing just those elements
for which the predicate returns <span class="inlinecode"><span
class="id" type="var">true</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">filter</span> {<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">test</span>: <span class="id" type="var">X</span><span
style="font-family: arial;">→</span><span class="id"
type="var">bool</span>) (<span class="id" type="var">l</span>:<span
class="id" type="var">list</span> <span class="id" type="var">X</span>)\
                 : (<span class="id" type="var">list</span> <span
class="id" type="var">X</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | [] ⇒ []\
   | <span class="id" type="var">h</span> :: <span class="id"
type="var">t</span> ⇒ <span class="id" type="keyword">if</span> <span
class="id" type="var">test</span> <span class="id" type="var">h</span>
<span class="id" type="keyword">then</span> <span class="id"
type="var">h</span> :: (<span class="id" type="var">filter</span> <span
class="id" type="var">test</span> <span class="id" type="var">t</span>)\
                         <span class="id" type="keyword">else</span>
<span class="id" type="var">filter</span> <span class="id"
type="var">test</span> <span class="id" type="var">t</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

For example, if we apply <span class="inlinecode"><span class="id"
type="var">filter</span></span> to the predicate <span
class="inlinecode"><span class="id" type="var">evenb</span></span> and a
list of numbers <span class="inlinecode"><span class="id"
type="var">l</span></span>, it returns a list containing just the even
members of <span class="inlinecode"><span class="id"
type="var">l</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_filter1</span>: <span class="id"
type="var">filter</span> <span class="id" type="var">evenb</span>
[1;2;3;4] = [2;4].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Definition</span> <span class="id"
type="var">length\_is\_1</span> {<span class="id" type="var">X</span> :
<span class="id" type="keyword">Type</span>} (<span class="id"
type="var">l</span> : <span class="id" type="var">list</span> <span
class="id" type="var">X</span>) : <span class="id"
type="var">bool</span> :=\
   <span class="id" type="var">beq\_nat</span> (<span class="id"
type="var">length</span> <span class="id" type="var">l</span>) 1.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_filter2</span>:\
     <span class="id" type="var">filter</span> <span class="id"
type="var">length\_is\_1</span>\
            [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]\
   = [ [3]; [4]; [8] ].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

<div class="paragraph">

</div>

We can use <span class="inlinecode"><span class="id"
type="var">filter</span></span> to give a concise version of the <span
class="inlinecode"><span class="id"
type="var">countoddmembers</span></span> function from the <span
class="inlinecode"><span class="id" type="var">Lists</span></span>
chapter.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">countoddmembers'</span> (<span class="id"
type="var">l</span>:<span class="id" type="var">list</span> <span
class="id" type="var">nat</span>) : <span class="id"
type="var">nat</span> :=\
   <span class="id" type="var">length</span> (<span class="id"
type="var">filter</span> <span class="id" type="var">oddb</span> <span
class="id" type="var">l</span>).\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_countoddmembers'1</span>: <span class="id"
type="var">countoddmembers'</span> [1;0;3;1;4;5] = 4.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_countoddmembers'2</span>: <span class="id"
type="var">countoddmembers'</span> [0;2;4] = 0.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_countoddmembers'3</span>: <span class="id"
type="var">countoddmembers'</span> <span class="id"
type="var">nil</span> = 0.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Anonymous Functions {.section}
-------------------

<div class="paragraph">

</div>

It is a little annoying to be forced to define the function <span
class="inlinecode"><span class="id"
type="var">length\_is\_1</span></span> and give it a name just to be
able to pass it as an argument to <span class="inlinecode"><span
class="id" type="var">filter</span></span>, since we will probably never
use it again. Moreover, this is not an isolated example. When using
higher-order functions, we often want to pass as arguments "one-off"
functions that we will never use again; having to give each of these
functions a name would be tedious.
<div class="paragraph">

</div>

Fortunately, there is a better way. It is also possible to construct a
function "on the fly" without declaring it at the top level or giving it
a name; this is analogous to the notation we've been using for writing
down constant lists, natural numbers, and so on.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_anon\_fun'</span>:\
   <span class="id" type="var">doit3times</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">n</span> ⇒ <span
class="id" type="var">n</span> × <span class="id" type="var">n</span>) 2
= 256.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Here is the motivating example from before, rewritten to use an
anonymous function.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_filter2'</span>:\
     <span class="id" type="var">filter</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">l</span> ⇒ <span
class="id" type="var">beq\_nat</span> (<span class="id"
type="var">length</span> <span class="id" type="var">l</span>) 1)\
            [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]\
   = [ [3]; [4]; [8] ].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (filter\_even\_gt7) {.section}

<div class="paragraph">

</div>

Use <span class="inlinecode"><span class="id"
type="var">filter</span></span> (instead of <span
class="inlinecode"><span class="id"
type="keyword">Fixpoint</span></span>) to write a Coq function <span
class="inlinecode"><span class="id"
type="var">filter\_even\_gt7</span></span> that takes a list of natural
numbers as input and returns a list of just those that are even and
greater than 7.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">filter\_even\_gt7</span> (<span class="id"
type="var">l</span> : <span class="id" type="var">list</span> <span
class="id" type="var">nat</span>) : <span class="id"
type="var">list</span> <span class="id" type="var">nat</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_filter\_even\_gt7\_1</span> :\
   <span class="id" type="var">filter\_even\_gt7</span>
[1;2;6;9;10;3;12;8] = [10;12;8].\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_filter\_even\_gt7\_2</span> :\
   <span class="id" type="var">filter\_even\_gt7</span> [5;2;6;19;129] =
[].\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (partition) {.section}

Use <span class="inlinecode"><span class="id"
type="var">filter</span></span> to write a Coq function <span
class="inlinecode"><span class="id" type="var">partition</span></span>:
<div class="paragraph">

</div>

<div class="code code-tight">

  <span class="id" type="var">partition</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">X</span> : <span class="id" type="keyword">Type</span>,\
               (<span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bool</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">list</span> <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">list</span> <span class="id"
type="var">X</span> × <span class="id" type="var">list</span> <span
class="id" type="var">X</span>
<div class="paragraph">

</div>

</div>

Given a set <span class="inlinecode"><span class="id"
type="var">X</span></span>, a test function of type <span
class="inlinecode"><span class="id" type="var">X</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">bool</span></span>
and a <span class="inlinecode"><span class="id"
type="var">list</span></span> <span class="inlinecode"><span class="id"
type="var">X</span></span>, <span class="inlinecode"><span class="id"
type="var">partition</span></span> should return a pair of lists. The
first member of the pair is the sublist of the original list containing
the elements that satisfy the test, and the second is the sublist
containing those that fail the test. The order of elements in the two
sublists should be the same as their order in the original list.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">partition</span> {<span class="id" type="var">X</span> :
<span class="id" type="keyword">Type</span>} (<span class="id"
type="var">test</span> : <span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bool</span>) (<span class="id" type="var">l</span> : <span
class="id" type="var">list</span> <span class="id" type="var">X</span>)\
                      : <span class="id" type="var">list</span> <span
class="id" type="var">X</span> × <span class="id" type="var">list</span>
<span class="id" type="var">X</span> :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_partition1</span>: <span class="id"
type="var">partition</span> <span class="id" type="var">oddb</span>
[1;2;3;4;5] = ([1;3;5], [2;4]).\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_partition2</span>: <span class="id"
type="var">partition</span> (<span class="id" type="keyword">fun</span>
<span class="id" type="var">x</span> ⇒ <span class="id"
type="var">false</span>) [5;9;0] = ([], [5;9;0]).\
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

Map {.section}
---

<div class="paragraph">

</div>

Another handy higher-order function is called <span
class="inlinecode"><span class="id" type="var">map</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">map</span> {<span class="id" type="var">X</span> <span
class="id" type="var">Y</span>:<span class="id"
type="keyword">Type</span>} (<span class="id" type="var">f</span>:<span
class="id" type="var">X</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Y</span>) (<span class="id" type="var">l</span>:<span
class="id" type="var">list</span> <span class="id" type="var">X</span>)\
              : (<span class="id" type="var">list</span> <span
class="id" type="var">Y</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | [] ⇒ []\
   | <span class="id" type="var">h</span> :: <span class="id"
type="var">t</span> ⇒ (<span class="id" type="var">f</span> <span
class="id" type="var">h</span>) :: (<span class="id"
type="var">map</span> <span class="id" type="var">f</span> <span
class="id" type="var">t</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

###  {.section}

It takes a function <span class="inlinecode"><span class="id"
type="var">f</span></span> and a list <span class="inlinecode"></span>
<span class="inlinecode"><span class="id" type="var">l</span></span>
<span class="inlinecode">=</span> <span class="inlinecode">[<span
class="id" type="var">n1</span>,</span> <span class="inlinecode"><span
class="id" type="var">n2</span>,</span> <span class="inlinecode"><span
class="id" type="var">n3</span>,</span> <span
class="inlinecode">...]</span> <span class="inlinecode"></span> and
returns the list <span class="inlinecode"></span> <span
class="inlinecode">[<span class="id" type="var">f</span></span> <span
class="inlinecode"><span class="id" type="var">n1</span>,</span> <span
class="inlinecode"><span class="id" type="var">f</span></span> <span
class="inlinecode"><span class="id" type="var">n2</span>,</span> <span
class="inlinecode"><span class="id" type="var">f</span></span> <span
class="inlinecode"><span class="id" type="var">n3</span>,...]</span>
<span class="inlinecode"></span>, where <span class="inlinecode"><span
class="id" type="var">f</span></span> has been applied to each element
of <span class="inlinecode"><span class="id" type="var">l</span></span>
in turn. For example:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_map1</span>: <span class="id" type="var">map</span>
(<span class="id" type="var">plus</span> 3) [2;0;2] = [5;3;5].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The element types of the input and output lists need not be the same
(<span class="inlinecode"><span class="id" type="var">map</span></span>
takes *two* type arguments, <span class="inlinecode"><span class="id"
type="var">X</span></span> and <span class="inlinecode"><span class="id"
type="var">Y</span></span>). This version of <span
class="inlinecode"><span class="id" type="var">map</span></span> can
thus be applied to a list of numbers and a function from numbers to
booleans to yield a list of booleans:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_map2</span>: <span class="id" type="var">map</span>
<span class="id" type="var">oddb</span> [2;1;2;5] = [<span class="id"
type="var">false</span>;<span class="id" type="var">true</span>;<span
class="id" type="var">false</span>;<span class="id"
type="var">true</span>].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

It can even be applied to a list of numbers and a function from numbers
to *lists* of booleans to yield a list of lists of booleans:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_map3</span>:\
     <span class="id" type="var">map</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">n</span> ⇒ [<span
class="id" type="var">evenb</span> <span class="id"
type="var">n</span>;<span class="id" type="var">oddb</span> <span
class="id" type="var">n</span>]) [2;1;2;5]\
   = [[<span class="id" type="var">true</span>;<span class="id"
type="var">false</span>];[<span class="id" type="var">false</span>;<span
class="id" type="var">true</span>];[<span class="id"
type="var">true</span>;<span class="id" type="var">false</span>];[<span
class="id" type="var">false</span>;<span class="id"
type="var">true</span>]].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Map for options {.section}
---------------

#### Exercise: 3 stars (map\_rev) {.section}

Show that <span class="inlinecode"><span class="id"
type="var">map</span></span> and <span class="inlinecode"><span
class="id" type="var">rev</span></span> commute. You may need to define
an auxiliary lemma.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">map\_rev</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span> <span class="id" type="var">Y</span> : <span
class="id" type="keyword">Type</span>) (<span class="id"
type="var">f</span> : <span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Y</span>) (<span class="id" type="var">l</span> : <span
class="id" type="var">list</span> <span class="id"
type="var">X</span>),\
   <span class="id" type="var">map</span> <span class="id"
type="var">f</span> (<span class="id" type="var">rev</span> <span
class="id" type="var">l</span>) = <span class="id" type="var">rev</span>
(<span class="id" type="var">map</span> <span class="id"
type="var">f</span> <span class="id" type="var">l</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (flat\_map) {.section}

The function <span class="inlinecode"><span class="id"
type="var">map</span></span> maps a <span class="inlinecode"><span
class="id" type="var">list</span></span> <span class="inlinecode"><span
class="id" type="var">X</span></span> to a <span
class="inlinecode"><span class="id" type="var">list</span></span> <span
class="inlinecode"><span class="id" type="var">Y</span></span> using a
function of type <span class="inlinecode"><span class="id"
type="var">X</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">Y</span></span>. We can
define a similar function, <span class="inlinecode"><span class="id"
type="var">flat\_map</span></span>, which maps a <span
class="inlinecode"><span class="id" type="var">list</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span> to a
<span class="inlinecode"><span class="id" type="var">list</span></span>
<span class="inlinecode"><span class="id" type="var">Y</span></span>
using a function <span class="inlinecode"><span class="id"
type="var">f</span></span> of type <span class="inlinecode"><span
class="id" type="var">X</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">list</span></span> <span
class="inlinecode"><span class="id" type="var">Y</span></span>. Your
definition should work by 'flattening' the results of <span
class="inlinecode"><span class="id" type="var">f</span></span>, like so:
<div class="paragraph">

</div>

<div class="code code-tight">

        <span class="id" type="var">flat\_map</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">n</span> ⇒ [<span
class="id" type="var">n</span>;<span class="id"
type="var">n</span>+1;<span class="id" type="var">n</span>+2]) [1;5;10]\
       = [1; 2; 3; 5; 6; 7; 10; 11; 12].
<div class="paragraph">

</div>

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">flat\_map</span> {<span class="id" type="var">X</span> <span
class="id" type="var">Y</span>:<span class="id"
type="keyword">Type</span>} (<span class="id" type="var">f</span>:<span
class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">list</span> <span class="id" type="var">Y</span>) (<span
class="id" type="var">l</span>:<span class="id" type="var">list</span>
<span class="id" type="var">X</span>)\
                    : (<span class="id" type="var">list</span> <span
class="id" type="var">Y</span>) :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_flat\_map1</span>:\
   <span class="id" type="var">flat\_map</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">n</span> ⇒ [<span
class="id" type="var">n</span>;<span class="id"
type="var">n</span>;<span class="id" type="var">n</span>]) [1;5;4]\
   = [1; 1; 1; 5; 5; 5; 4; 4; 4].\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Lists are not the only inductive type that we can write a <span
class="inlinecode"><span class="id" type="var">map</span></span>
function for. Here is the definition of <span class="inlinecode"><span
class="id" type="var">map</span></span> for the <span
class="inlinecode"><span class="id" type="var">option</span></span>
type:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">option\_map</span> {<span class="id" type="var">X</span>
<span class="id" type="var">Y</span> : <span class="id"
type="keyword">Type</span>} (<span class="id" type="var">f</span> :
<span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Y</span>) (<span class="id" type="var">xo</span> : <span
class="id" type="var">option</span> <span class="id"
type="var">X</span>)\
                       : <span class="id" type="var">option</span> <span
class="id" type="var">Y</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">xo</span> <span class="id" type="keyword">with</span>\
     | <span class="id" type="var">None</span> ⇒ <span class="id"
type="var">None</span>\
     | <span class="id" type="var">Some</span> <span class="id"
type="var">x</span> ⇒ <span class="id" type="var">Some</span> (<span
class="id" type="var">f</span> <span class="id" type="var">x</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (implicit\_args) {.section}

The definitions and uses of <span class="inlinecode"><span class="id"
type="var">filter</span></span> and <span class="inlinecode"><span
class="id" type="var">map</span></span> use implicit arguments in many
places. Replace the curly braces around the implicit arguments with
parentheses, and then fill in explicit type parameters where necessary
and use Coq to check that you've done so correctly. (This exercise is
not to be turned in; it is probably easiest to do it on a *copy* of this
file that you can throw away afterwards.) ☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Fold {.section}
----

<div class="paragraph">

</div>

An even more powerful higher-order function is called <span
class="inlinecode"><span class="id" type="var">fold</span></span>. This
function is the inspiration for the "<span class="inlinecode"><span
class="id" type="var">reduce</span></span>" operation that lies at the
heart of Google's map/reduce distributed programming framework.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">fold</span> {<span class="id" type="var">X</span> <span
class="id" type="var">Y</span>:<span class="id"
type="keyword">Type</span>} (<span class="id" type="var">f</span>: <span
class="id" type="var">X</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Y</span><span style="font-family: arial;">→</span><span
class="id" type="var">Y</span>) (<span class="id"
type="var">l</span>:<span class="id" type="var">list</span> <span
class="id" type="var">X</span>) (<span class="id"
type="var">b</span>:<span class="id" type="var">Y</span>) : <span
class="id" type="var">Y</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">b</span>\
   | <span class="id" type="var">h</span> :: <span class="id"
type="var">t</span> ⇒ <span class="id" type="var">f</span> <span
class="id" type="var">h</span> (<span class="id" type="var">fold</span>
<span class="id" type="var">f</span> <span class="id"
type="var">t</span> <span class="id" type="var">b</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

###  {.section}

<div class="paragraph">

</div>

Intuitively, the behavior of the <span class="inlinecode"><span
class="id" type="var">fold</span></span> operation is to insert a given
binary operator <span class="inlinecode"><span class="id"
type="var">f</span></span> between every pair of elements in a given
list. For example, <span class="inlinecode"></span> <span
class="inlinecode"><span class="id" type="var">fold</span></span> <span
class="inlinecode"><span class="id" type="var">plus</span></span> <span
class="inlinecode">[1;2;3;4]</span> <span class="inlinecode"></span>
intuitively means <span class="inlinecode">1+2+3+4</span>. To make this
precise, we also need a "starting element" that serves as the initial
second input to <span class="inlinecode"><span class="id"
type="var">f</span></span>. So, for example,
<div class="paragraph">

</div>

<div class="code code-tight">

   <span class="id" type="var">fold</span> <span class="id"
type="var">plus</span> [1;2;3;4] 0
<div class="paragraph">

</div>

</div>

yields
<div class="paragraph">

</div>

<div class="code code-tight">

   1 + (2 + (3 + (4 + 0))).
<div class="paragraph">

</div>

</div>

Here are some more examples:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> (<span class="id"
type="var">fold</span> <span class="id" type="var">andb</span>).\
 <span
class="comment">(\* ===\> fold andb : list bool -\> bool -\> bool \*)</span>\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">fold\_example1</span> : <span class="id"
type="var">fold</span> <span class="id" type="var">mult</span> [1;2;3;4]
1 = 24.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">fold\_example2</span> : <span class="id"
type="var">fold</span> <span class="id" type="var">andb</span> [<span
class="id" type="var">true</span>;<span class="id"
type="var">true</span>;<span class="id" type="var">false</span>;<span
class="id" type="var">true</span>] <span class="id"
type="var">true</span> = <span class="id" type="var">false</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">fold\_example3</span> : <span class="id"
type="var">fold</span> <span class="id" type="var">app</span>
[[1];[];[2;3];[4]] [] = [1;2;3;4].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star, advanced (fold\_types\_different) {.section}

Observe that the type of <span class="inlinecode"><span class="id"
type="var">fold</span></span> is parameterized by *two* type variables,
<span class="inlinecode"><span class="id" type="var">X</span></span> and
<span class="inlinecode"><span class="id" type="var">Y</span></span>,
and the parameter <span class="inlinecode"><span class="id"
type="var">f</span></span> is a binary operator that takes an <span
class="inlinecode"><span class="id" type="var">X</span></span> and a
<span class="inlinecode"><span class="id" type="var">Y</span></span> and
returns a <span class="inlinecode"><span class="id"
type="var">Y</span></span>. Can you think of a situation where it would
be useful for <span class="inlinecode"><span class="id"
type="var">X</span></span> and <span class="inlinecode"><span class="id"
type="var">Y</span></span> to be different?

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Functions For Constructing Functions {.section}
------------------------------------

<div class="paragraph">

</div>

Most of the higher-order functions we have talked about so far take
functions as *arguments*. Now let's look at some examples involving
*returning* functions as the results of other functions.
<div class="paragraph">

</div>

To begin, here is a function that takes a value <span
class="inlinecode"><span class="id" type="var">x</span></span> (drawn
from some type <span class="inlinecode"><span class="id"
type="var">X</span></span>) and returns a function from <span
class="inlinecode"><span class="id" type="var">nat</span></span> to
<span class="inlinecode"><span class="id" type="var">X</span></span>
that yields <span class="inlinecode"><span class="id"
type="var">x</span></span> whenever it is called, ignoring its <span
class="inlinecode"><span class="id" type="var">nat</span></span>
argument.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">constfun</span> {<span class="id" type="var">X</span>: <span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">x</span>: <span class="id" type="var">X</span>) : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id" type="var">X</span>
:=\
   <span class="id" type="keyword">fun</span> (<span class="id"
type="var">k</span>:<span class="id" type="var">nat</span>) ⇒ <span
class="id" type="var">x</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">ftrue</span> := <span class="id" type="var">constfun</span>
<span class="id" type="var">true</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">constfun\_example1</span> : <span class="id"
type="var">ftrue</span> 0 = <span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">constfun\_example2</span> : (<span class="id"
type="var">constfun</span> 5) 99 = 5.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

Similarly, but a bit more interestingly, here is a function that takes a
function <span class="inlinecode"><span class="id"
type="var">f</span></span> from numbers to some type <span
class="inlinecode"><span class="id" type="var">X</span></span>, a number
<span class="inlinecode"><span class="id" type="var">k</span></span>,
and a value <span class="inlinecode"><span class="id"
type="var">x</span></span>, and constructs a function that behaves
exactly like <span class="inlinecode"><span class="id"
type="var">f</span></span> except that, when called with the argument
<span class="inlinecode"><span class="id" type="var">k</span></span>, it
returns <span class="inlinecode"><span class="id"
type="var">x</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">override</span> {<span class="id" type="var">X</span>: <span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">f</span>: <span class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">X</span>) (<span class="id" type="var">k</span>:<span
class="id" type="var">nat</span>) (<span class="id"
type="var">x</span>:<span class="id" type="var">X</span>) : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">X</span>:=\
   <span class="id" type="keyword">fun</span> (<span class="id"
type="var">k'</span>:<span class="id" type="var">nat</span>) ⇒ <span
class="id" type="keyword">if</span> <span class="id"
type="var">beq\_nat</span> <span class="id" type="var">k</span> <span
class="id" type="var">k'</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">x</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">f</span> <span class="id" type="var">k'</span>.\
\

</div>

<div class="doc">

For example, we can apply <span class="inlinecode"><span class="id"
type="var">override</span></span> twice to obtain a function from
numbers to booleans that returns <span class="inlinecode"><span
class="id" type="var">false</span></span> on <span
class="inlinecode">1</span> and <span class="inlinecode">3</span> and
returns <span class="inlinecode"><span class="id"
type="var">true</span></span> on all other arguments.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">fmostlytrue</span> := <span class="id"
type="var">override</span> (<span class="id" type="var">override</span>
<span class="id" type="var">ftrue</span> 1 <span class="id"
type="var">false</span>) 3 <span class="id" type="var">false</span>.\
\

</div>

<div class="doc">

###  {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">override\_example1</span> : <span class="id"
type="var">fmostlytrue</span> 0 = <span class="id"
type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">override\_example2</span> : <span class="id"
type="var">fmostlytrue</span> 1 = <span class="id"
type="var">false</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">override\_example3</span> : <span class="id"
type="var">fmostlytrue</span> 2 = <span class="id"
type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">override\_example4</span> : <span class="id"
type="var">fmostlytrue</span> 3 = <span class="id"
type="var">false</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

###  {.section}

<div class="paragraph">

</div>

#### Exercise: 1 star (override\_example) {.section}

Before starting to work on the following proof, make sure you understand
exactly what the theorem is saying and can paraphrase it in your own
words. The proof itself is straightforward.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">override\_example</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">b</span>:<span class="id" type="var">bool</span>),\
   (<span class="id" type="var">override</span> (<span class="id"
type="var">constfun</span> <span class="id" type="var">b</span>) 3 <span
class="id" type="var">true</span>) 2 = <span class="id"
type="var">b</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

We'll use function overriding heavily in parts of the rest of the
course, and we will end up needing to know quite a bit about its
properties. To prove these properties, though, we need to know about a
few more of Coq's tactics; developing these is the main topic of the
next chapter. For now, though, let's introduce just one very useful
tactic that will also help us with proving properties of some of the
other functions we have introduced in this chapter.

</div>

<div class="code code-tight">

\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id" type="tactic">unfold</span></span> Tactic {.section}
=======================================================================================

<div class="paragraph">

</div>

Sometimes, a proof will get stuck because Coq doesn't automatically
expand a function call into its definition. (This is a feature, not a
bug: if Coq automatically expanded everything possible, our proof goals
would quickly become enormous — hard to read and slow for Coq to
manipulate!)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">unfold\_example\_bad</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">m</span>
<span class="id" type="var">n</span>,\
   3 + <span class="id" type="var">n</span> = <span class="id"
type="var">m</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">plus3</span> <span class="id"
type="var">n</span> + 1 = <span class="id" type="var">m</span> + 1.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">m</span> <span class="id" type="var">n</span> <span
class="id" type="var">H</span>.\
 <span class="comment">(\* At this point, we'd like to do <span
class="inlinecode"><span class="id" type="tactic">rewrite</span></span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">H</span></span>, since \
      <span class="inlinecode"><span class="id"
type="var">plus3</span></span> <span class="inlinecode"><span class="id"
type="var">n</span></span> is definitionally equal to <span
class="inlinecode">3</span> <span class="inlinecode">+</span> <span
class="inlinecode"><span class="id"
type="var">n</span></span>.  However, \
      Coq doesn't automatically expand <span class="inlinecode"><span
class="id" type="var">plus3</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> to its \
      definition. \*)</span>\
   <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="tactic">unfold</span></span> tactic can be used to explicitly
replace a defined name by the right-hand side of its definition.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">unfold\_example</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">m</span>
<span class="id" type="var">n</span>,\
   3 + <span class="id" type="var">n</span> = <span class="id"
type="var">m</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">plus3</span> <span class="id"
type="var">n</span> + 1 = <span class="id" type="var">m</span> + 1.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">m</span> <span class="id" type="var">n</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">plus3</span>.\
   <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Now we can prove a first property of <span class="inlinecode"><span
class="id" type="var">override</span></span>: If we override a function
at some argument <span class="inlinecode"><span class="id"
type="var">k</span></span> and then look up <span
class="inlinecode"><span class="id" type="var">k</span></span>, we get
back the overridden value.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">override\_eq</span> : <span
style="font-family: arial;">∀</span>{<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>} <span
class="id" type="var">x</span> <span class="id" type="var">k</span>
(<span class="id" type="var">f</span>:<span class="id"
type="var">nat</span><span style="font-family: arial;">→</span><span
class="id" type="var">X</span>),\
   (<span class="id" type="var">override</span> <span class="id"
type="var">f</span> <span class="id" type="var">k</span> <span
class="id" type="var">x</span>) <span class="id" type="var">k</span> =
<span class="id" type="var">x</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">X</span> <span class="id" type="var">x</span> <span
class="id" type="var">k</span> <span class="id" type="var">f</span>.\
   <span class="id" type="tactic">unfold</span> <span class="id"
type="var">override</span>.\
   <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">beq\_nat\_refl</span>.\
   <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

This proof was straightforward, but note that it requires <span
class="inlinecode"><span class="id" type="tactic">unfold</span></span>
to expand the definition of <span class="inlinecode"><span class="id"
type="var">override</span></span>.
<div class="paragraph">

</div>

#### Exercise: 2 stars (override\_neq) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">override\_neq</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) <span
class="id" type="var">x1</span> <span class="id" type="var">x2</span>
<span class="id" type="var">k1</span> <span class="id"
type="var">k2</span> (<span class="id" type="var">f</span> : <span
class="id" type="var">nat</span><span
style="font-family: arial;">→</span><span class="id"
type="var">X</span>),\
   <span class="id" type="var">f</span> <span class="id"
type="var">k1</span> = <span class="id" type="var">x1</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">k2</span> <span class="id" type="var">k1</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span>\
   (<span class="id" type="var">override</span> <span class="id"
type="var">f</span> <span class="id" type="var">k2</span> <span
class="id" type="var">x2</span>) <span class="id" type="var">k1</span> =
<span class="id" type="var">x1</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

As the inverse of <span class="inlinecode"><span class="id"
type="tactic">unfold</span></span>, Coq also provides a tactic <span
class="inlinecode"><span class="id" type="var">fold</span></span>, which
can be used to "unexpand" a definition. It is used much less often.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Additional Exercises {.section}
====================

<div class="paragraph">

</div>

#### Exercise: 2 stars (fold\_length) {.section}

Many common functions on lists can be implemented in terms of <span
class="inlinecode"><span class="id" type="var">fold</span></span>. For
example, here is an alternative definition of <span
class="inlinecode"><span class="id" type="var">length</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">fold\_length</span> {<span class="id" type="var">X</span> :
<span class="id" type="keyword">Type</span>} (<span class="id"
type="var">l</span> : <span class="id" type="var">list</span> <span
class="id" type="var">X</span>) : <span class="id" type="var">nat</span>
:=\
   <span class="id" type="var">fold</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">\_</span> <span
class="id" type="var">n</span> ⇒ <span class="id" type="var">S</span>
<span class="id" type="var">n</span>) <span class="id"
type="var">l</span> 0.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_fold\_length1</span> : <span class="id"
type="var">fold\_length</span> [4;7;0] = 3.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Prove the correctness of <span class="inlinecode"><span class="id"
type="var">fold\_length</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">fold\_length\_correct</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">X</span>
(<span class="id" type="var">l</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span>),\
   <span class="id" type="var">fold\_length</span> <span class="id"
type="var">l</span> = <span class="id" type="var">length</span> <span
class="id" type="var">l</span>.\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (fold\_map) {.section}

We can also define <span class="inlinecode"><span class="id"
type="var">map</span></span> in terms of <span class="inlinecode"><span
class="id" type="var">fold</span></span>. Finish <span
class="inlinecode"><span class="id" type="var">fold\_map</span></span>
below.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">fold\_map</span> {<span class="id" type="var">X</span> <span
class="id" type="var">Y</span>:<span class="id"
type="keyword">Type</span>} (<span class="id" type="var">f</span> :
<span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Y</span>) (<span class="id" type="var">l</span> : <span
class="id" type="var">list</span> <span class="id" type="var">X</span>)
: <span class="id" type="var">list</span> <span class="id"
type="var">Y</span> :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\

</div>

<div class="doc">

Write down a theorem <span class="inlinecode"><span class="id"
type="var">fold\_map\_correct</span></span> in Coq stating that <span
class="inlinecode"><span class="id" type="var">fold\_map</span></span>
is correct, and prove it.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, advanced (index\_informal) {.section}

Recall the definition of the <span class="inlinecode"><span class="id"
type="var">index</span></span> function:
<div class="paragraph">

</div>

<div class="code code-tight">

   <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">index</span> {<span class="id" type="var">X</span> : <span
class="id" type="keyword">Type</span>} (<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>) (<span
class="id" type="var">l</span> : <span class="id"
type="var">list</span> <span class="id" type="var">X</span>) : <span
class="id" type="var">option</span> <span class="id"
type="var">X</span> :=\
      <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
      | [] ⇒ <span class="id" type="var">None</span> \
      | <span class="id" type="var">a</span> :: <span class="id"
type="var">l'</span> ⇒ <span class="id" type="keyword">if</span> <span
class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">O</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">Some</span> <span class="id" type="var">a</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">index</span> (<span class="id" type="var">pred</span> <span
class="id" type="var">n</span>) <span class="id" type="var">l'</span>\
      <span class="id" type="keyword">end</span>.
<div class="paragraph">

</div>

</div>

Write an informal proof of the following theorem:
<div class="paragraph">

</div>

<div class="code code-tight">

   <span style="font-family: arial;">∀</span><span class="id"
type="var">X</span> <span class="id" type="var">n</span> <span
class="id" type="var">l</span>, <span class="id"
type="var">length</span> <span class="id" type="var">l</span> = <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> @<span class="id"
type="var">index</span> <span class="id" type="var">X</span> <span
class="id" type="var">n</span> <span class="id"
type="var">l</span> = <span class="id" type="var">None</span>.
<div class="paragraph">

</div>

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, advanced (church\_numerals) {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Church</span>.\
\

</div>

<div class="doc">

In this exercise, we will explore an alternative way of defining natural
numbers, using the so-called *Church numerals*, named after
mathematician Alonzo Church. We can represent a natural number <span
class="inlinecode"><span class="id" type="var">n</span></span> as a
function that takes a function <span class="inlinecode"><span class="id"
type="var">f</span></span> as a parameter and returns <span
class="inlinecode"><span class="id" type="var">f</span></span> iterated
<span class="inlinecode"><span class="id" type="var">n</span></span>
times. More formally,

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">nat</span> := <span style="font-family: arial;">∀</span><span
class="id" type="var">X</span> : <span class="id"
type="keyword">Type</span>, (<span class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">X</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">X</span>.\
\

</div>

<div class="doc">

Let's see how to write some numbers with this notation. Any function
<span class="inlinecode"><span class="id" type="var">f</span></span>
iterated once shouldn't change. Thus,

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">one</span> : <span class="id" type="var">nat</span> :=\
   <span class="id" type="keyword">fun</span> (<span class="id"
type="var">X</span> : <span class="id" type="keyword">Type</span>)
(<span class="id" type="var">f</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">x</span> :
<span class="id" type="var">X</span>) ⇒ <span class="id"
type="var">f</span> <span class="id" type="var">x</span>.\
\

</div>

<div class="doc">

<span class="inlinecode"><span class="id" type="var">two</span></span>
should apply <span class="inlinecode"><span class="id"
type="var">f</span></span> twice to its argument:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">two</span> : <span class="id" type="var">nat</span> :=\
   <span class="id" type="keyword">fun</span> (<span class="id"
type="var">X</span> : <span class="id" type="keyword">Type</span>)
(<span class="id" type="var">f</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">x</span> :
<span class="id" type="var">X</span>) ⇒ <span class="id"
type="var">f</span> (<span class="id" type="var">f</span> <span
class="id" type="var">x</span>).\
\

</div>

<div class="doc">

<span class="inlinecode"><span class="id" type="var">zero</span></span>
is somewhat trickier: how can we apply a function zero times? The answer
is simple: just leave the argument untouched.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">zero</span> : <span class="id" type="var">nat</span> :=\
   <span class="id" type="keyword">fun</span> (<span class="id"
type="var">X</span> : <span class="id" type="keyword">Type</span>)
(<span class="id" type="var">f</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">X</span>) (<span class="id" type="var">x</span> :
<span class="id" type="var">X</span>) ⇒ <span class="id"
type="var">x</span>.\
\

</div>

<div class="doc">

More generally, a number <span class="inlinecode"><span class="id"
type="var">n</span></span> will be written as <span
class="inlinecode"><span class="id" type="keyword">fun</span></span>
<span class="inlinecode"><span class="id" type="var">X</span></span>
<span class="inlinecode"><span class="id" type="var">f</span></span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode">⇒</span> <span class="inlinecode"><span
class="id" type="var">f</span></span> <span class="inlinecode">(<span
class="id" type="var">f</span></span> <span
class="inlinecode">...</span> <span class="inlinecode">(<span class="id"
type="var">f</span></span> <span class="inlinecode"><span class="id"
type="var">x</span>)</span> <span class="inlinecode">...)</span>, with
<span class="inlinecode"><span class="id" type="var">n</span></span>
occurrences of <span class="inlinecode"><span class="id"
type="var">f</span></span>. Notice in particular how the <span
class="inlinecode"><span class="id" type="var">doit3times</span></span>
function we've defined previously is actually just the representation of
<span class="inlinecode">3</span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">three</span> : <span class="id" type="var">nat</span> :=
@<span class="id" type="var">doit3times</span>.\
\

</div>

<div class="doc">

Complete the definitions of the following functions. Make sure that the
corresponding unit tests pass by proving them with <span
class="inlinecode"><span class="id"
type="tactic">reflexivity</span></span>.
<div class="paragraph">

</div>

Successor of a natural number

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">succ</span> (<span class="id" type="var">n</span> : <span
class="id" type="var">nat</span>) : <span class="id"
type="var">nat</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">succ\_1</span> : <span class="id" type="var">succ</span>
<span class="id" type="var">zero</span> = <span class="id"
type="var">one</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">succ\_2</span> : <span class="id" type="var">succ</span>
<span class="id" type="var">one</span> = <span class="id"
type="var">two</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">succ\_3</span> : <span class="id" type="var">succ</span>
<span class="id" type="var">two</span> = <span class="id"
type="var">three</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Addition of two natural numbers

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">plus</span> (<span class="id" type="var">n</span> <span
class="id" type="var">m</span> : <span class="id" type="var">nat</span>)
: <span class="id" type="var">nat</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">plus\_1</span> : <span class="id" type="var">plus</span>
<span class="id" type="var">zero</span> <span class="id"
type="var">one</span> = <span class="id" type="var">one</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">plus\_2</span> : <span class="id" type="var">plus</span>
<span class="id" type="var">two</span> <span class="id"
type="var">three</span> = <span class="id" type="var">plus</span> <span
class="id" type="var">three</span> <span class="id"
type="var">two</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">plus\_3</span> :\
   <span class="id" type="var">plus</span> (<span class="id"
type="var">plus</span> <span class="id" type="var">two</span> <span
class="id" type="var">two</span>) <span class="id"
type="var">three</span> = <span class="id" type="var">plus</span> <span
class="id" type="var">one</span> (<span class="id"
type="var">plus</span> <span class="id" type="var">three</span> <span
class="id" type="var">three</span>).\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Multiplication

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">mult</span> (<span class="id" type="var">n</span> <span
class="id" type="var">m</span> : <span class="id" type="var">nat</span>)
: <span class="id" type="var">nat</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">mult\_1</span> : <span class="id" type="var">mult</span>
<span class="id" type="var">one</span> <span class="id"
type="var">one</span> = <span class="id" type="var">one</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">mult\_2</span> : <span class="id" type="var">mult</span>
<span class="id" type="var">zero</span> (<span class="id"
type="var">plus</span> <span class="id" type="var">three</span> <span
class="id" type="var">three</span>) = <span class="id"
type="var">zero</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">mult\_3</span> : <span class="id" type="var">mult</span>
<span class="id" type="var">two</span> <span class="id"
type="var">three</span> = <span class="id" type="var">plus</span> <span
class="id" type="var">three</span> <span class="id"
type="var">three</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Exponentiation
<div class="paragraph">

</div>

Hint: Polymorphism plays a crucial role here. However, choosing the
right type to iterate over can be tricky. If you hit a "Universe
inconsistency" error, try iterating over a different type: <span
class="inlinecode"><span class="id" type="var">nat</span></span> itself
is usually problematic.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">exp</span> (<span class="id" type="var">n</span> <span
class="id" type="var">m</span> : <span class="id" type="var">nat</span>)
: <span class="id" type="var">nat</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">exp\_1</span> : <span class="id" type="var">exp</span> <span
class="id" type="var">two</span> <span class="id" type="var">two</span>
= <span class="id" type="var">plus</span> <span class="id"
type="var">two</span> <span class="id" type="var">two</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">exp\_2</span> : <span class="id" type="var">exp</span> <span
class="id" type="var">three</span> <span class="id"
type="var">two</span> = <span class="id" type="var">plus</span> (<span
class="id" type="var">mult</span> <span class="id" type="var">two</span>
(<span class="id" type="var">mult</span> <span class="id"
type="var">two</span> <span class="id" type="var">two</span>)) <span
class="id" type="var">one</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">exp\_3</span> : <span class="id" type="var">exp</span> <span
class="id" type="var">three</span> <span class="id"
type="var">zero</span> = <span class="id" type="var">one</span>.\
 <span class="id" type="keyword">Proof</span>. <span
class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Church</span>.\
\

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
