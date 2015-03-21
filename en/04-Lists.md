<div id="page">

<div id="header">

</div>

<div id="main">

Lists<span class="subtitle">Working with Structured Data</span> {.libtitle}
===============================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id"
type="keyword">Induction</span>.\
\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">NatList</span>.\
\

</div>

<div class="doc">

Pairs of Numbers {.section}
================

<div class="paragraph">

</div>

In an <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> type definition, each constructor
can take any number of arguments — none (as with <span
class="inlinecode"><span class="id" type="var">true</span></span> and
<span class="inlinecode"><span class="id" type="var">O</span></span>),
one (as with <span class="inlinecode"><span class="id"
type="var">S</span></span>), or more than one, as in this definition:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">natprod</span> : <span class="id" type="keyword">Type</span>
:=\
   <span class="id" type="var">pair</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">natprod</span>.\
\

</div>

<div class="doc">

This declaration can be read: "There is just one way to construct a pair
of numbers: by applying the constructor <span class="inlinecode"><span
class="id" type="var">pair</span></span> to two arguments of type <span
class="inlinecode"><span class="id" type="var">nat</span></span>."
<div class="paragraph">

</div>

We can construct an element of <span class="inlinecode"><span class="id"
type="var">natprod</span></span> like this:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> (<span class="id"
type="var">pair</span> 3 5).\
\

</div>

<div class="doc">

###  {.section}

<div class="paragraph">

</div>

Here are two simple function definitions for extracting the first and
second components of a pair. (The definitions also illustrate how to do
pattern matching on two-argument constructors.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">fst</span> (<span class="id" type="var">p</span> : <span
class="id" type="var">natprod</span>) : <span class="id"
type="var">nat</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">p</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">pair</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span> ⇒ <span
class="id" type="var">x</span>\
   <span class="id" type="keyword">end</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">snd</span> (<span class="id" type="var">p</span> : <span
class="id" type="var">natprod</span>) : <span class="id"
type="var">nat</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">p</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">pair</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span> ⇒ <span
class="id" type="var">y</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Eval</span> <span class="id"
type="tactic">compute</span> <span class="id" type="keyword">in</span>
(<span class="id" type="var">fst</span> (<span class="id"
type="var">pair</span> 3 5)).\
 <span class="comment">(\* ===\> 3 \*)</span>\
\

</div>

<div class="doc">

###  {.section}

<div class="paragraph">

</div>

Since pairs are used quite a bit, it is nice to be able to write them
with the standard mathematical notation <span class="inlinecode">(<span
class="id" type="var">x</span>,<span class="id"
type="var">y</span>)</span> instead of <span class="inlinecode"><span
class="id" type="var">pair</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="var">y</span></span>. We can tell Coq to allow this
with a <span class="inlinecode"><span class="id"
type="keyword">Notation</span></span> declaration.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "( x , y )" := (<span
class="id" type="var">pair</span> <span class="id" type="var">x</span>
<span class="id" type="var">y</span>).\
\

</div>

<div class="doc">

The new notation can be used both in expressions and in pattern matches
(indeed, we've seen it already in the previous chapter — this notation
is provided as part of the standard library):

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Eval</span> <span class="id"
type="tactic">compute</span> <span class="id" type="keyword">in</span>
(<span class="id" type="var">fst</span> (3,5)).\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">fst'</span> (<span class="id" type="var">p</span> : <span
class="id" type="var">natprod</span>) : <span class="id"
type="var">nat</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">p</span> <span class="id" type="keyword">with</span>\
   | (<span class="id" type="var">x</span>,<span class="id"
type="var">y</span>) ⇒ <span class="id" type="var">x</span>\
   <span class="id" type="keyword">end</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">snd'</span> (<span class="id" type="var">p</span> : <span
class="id" type="var">natprod</span>) : <span class="id"
type="var">nat</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">p</span> <span class="id" type="keyword">with</span>\
   | (<span class="id" type="var">x</span>,<span class="id"
type="var">y</span>) ⇒ <span class="id" type="var">y</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">swap\_pair</span> (<span class="id" type="var">p</span> :
<span class="id" type="var">natprod</span>) : <span class="id"
type="var">natprod</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">p</span> <span class="id" type="keyword">with</span>\
   | (<span class="id" type="var">x</span>,<span class="id"
type="var">y</span>) ⇒ (<span class="id" type="var">y</span>,<span
class="id" type="var">x</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

###  {.section}

<div class="paragraph">

</div>

Let's try and prove a few simple facts about pairs. If we state the
lemmas in a particular (and slightly peculiar) way, we can prove them
with just reflexivity (and its built-in simplification):

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">surjective\_pairing'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> <span class="id" type="var">m</span> : <span
class="id" type="var">nat</span>),\
   (<span class="id" type="var">n</span>,<span class="id"
type="var">m</span>) = (<span class="id" type="var">fst</span> (<span
class="id" type="var">n</span>,<span class="id" type="var">m</span>),
<span class="id" type="var">snd</span> (<span class="id"
type="var">n</span>,<span class="id" type="var">m</span>)).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Note that <span class="inlinecode"><span class="id"
type="tactic">reflexivity</span></span> is not enough if we state the
lemma in a more natural way:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">surjective\_pairing\_stuck</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">p</span> : <span class="id" type="var">natprod</span>),\
   <span class="id" type="var">p</span> = (<span class="id"
type="var">fst</span> <span class="id" type="var">p</span>, <span
class="id" type="var">snd</span> <span class="id" type="var">p</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">simpl</span>. <span
class="comment">(\* Doesn't reduce anything! \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

###  {.section}

We have to expose the structure of <span class="inlinecode"><span
class="id" type="var">p</span></span> so that <span
class="inlinecode"><span class="id" type="tactic">simpl</span></span>
can perform the pattern match in <span class="inlinecode"><span
class="id" type="var">fst</span></span> and <span
class="inlinecode"><span class="id" type="var">snd</span></span>. We can
do this with <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span>.
<div class="paragraph">

</div>

Notice that, unlike for <span class="inlinecode"><span class="id"
type="var">nat</span></span>s, <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> doesn't generate an extra subgoal
here. That's because <span class="inlinecode"><span class="id"
type="var">natprod</span></span>s can only be constructed in one way.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">surjective\_pairing</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">p</span> : <span class="id" type="var">natprod</span>),\
   <span class="id" type="var">p</span> = (<span class="id"
type="var">fst</span> <span class="id" type="var">p</span>, <span
class="id" type="var">snd</span> <span class="id" type="var">p</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">p</span>. <span class="id" type="tactic">destruct</span>
<span class="id" type="var">p</span> <span class="id"
type="keyword">as</span> [<span class="id" type="var">n</span> <span
class="id" type="var">m</span>]. <span class="id"
type="tactic">simpl</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star (snd\_fst\_is\_swap) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">snd\_fst\_is\_swap</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">p</span> : <span class="id" type="var">natprod</span>),\
   (<span class="id" type="var">snd</span> <span class="id"
type="var">p</span>, <span class="id" type="var">fst</span> <span
class="id" type="var">p</span>) = <span class="id"
type="var">swap\_pair</span> <span class="id" type="var">p</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (fst\_swap\_is\_snd) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Theorem</span> <span class="id"
type="var">fst\_swap\_is\_snd</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">p</span> : <span class="id" type="var">natprod</span>),\
   <span class="id" type="var">fst</span> (<span class="id"
type="var">swap\_pair</span> <span class="id" type="var">p</span>) =
<span class="id" type="var">snd</span> <span class="id"
type="var">p</span>.\
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

Lists of Numbers {.section}
================

<div class="paragraph">

</div>

Generalizing the definition of pairs a little, we can describe the type
of *lists* of numbers like this: "A list is either the empty list or
else a pair of a number and another list."

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">natlist</span> : <span class="id" type="keyword">Type</span>
:=\
   | <span class="id" type="var">nil</span> : <span class="id"
type="var">natlist</span>\
   | <span class="id" type="var">cons</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">natlist</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">natlist</span>.\
\

</div>

<div class="doc">

For example, here is a three-element list:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">mylist</span> := <span class="id" type="var">cons</span> 1
(<span class="id" type="var">cons</span> 2 (<span class="id"
type="var">cons</span> 3 <span class="id" type="var">nil</span>)).\
\

</div>

<div class="doc">

###  {.section}

As with pairs, it is more convenient to write lists in familiar
programming notation. The following two declarations allow us to use
<span class="inlinecode">::</span> as an infix <span
class="inlinecode"><span class="id" type="var">cons</span></span>
operator and square brackets as an "outfix" notation for constructing
lists.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "x :: l" := (<span
class="id" type="var">cons</span> <span class="id" type="var">x</span>
<span class="id" type="var">l</span>) (<span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 60,
<span class="id" type="var">right</span> <span class="id"
type="var">associativity</span>).\
 <span class="id" type="keyword">Notation</span> "[ ]" := <span
class="id" type="var">nil</span>.\
 <span class="id" type="keyword">Notation</span> "[ x ; .. ; y ]" :=
(<span class="id" type="var">cons</span> <span class="id"
type="var">x</span> .. (<span class="id" type="var">cons</span> <span
class="id" type="var">y</span> <span class="id" type="var">nil</span>)
..).\
\

</div>

<div class="doc">

It is not necessary to fully understand these declarations, but in case
you are interested, here is roughly what's going on.
<div class="paragraph">

</div>

The <span class="inlinecode"><span class="id"
type="var">right</span></span> <span class="inlinecode"><span class="id"
type="var">associativity</span></span> annotation tells Coq how to
parenthesize expressions involving several uses of <span
class="inlinecode">::</span> so that, for example, the next three
declarations mean exactly the same thing:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">mylist1</span> := 1 :: (2 :: (3 :: <span class="id"
type="var">nil</span>)).\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">mylist2</span> := 1 :: 2 :: 3 :: <span class="id"
type="var">nil</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">mylist3</span> := [1;2;3].\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="tactic">at</span></span> <span class="inlinecode"><span class="id"
type="var">level</span></span> <span class="inlinecode">60</span> part
tells Coq how to parenthesize expressions that involve both <span
class="inlinecode">::</span> and some other infix operator. For example,
since we defined <span class="inlinecode">+</span> as infix notation for
the <span class="inlinecode"><span class="id"
type="var">plus</span></span> function at level 50,
<div class="paragraph">

</div>

<div class="code code-tight">

<span class="id" type="keyword">Notation</span> "x + y" := (<span
class="id" type="var">plus</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span>)  \
                     (<span class="id" type="tactic">at</span> <span
class="id" type="var">level</span> 50, <span class="id"
type="var">left</span> <span class="id"
type="var">associativity</span>).
<div class="paragraph">

</div>

</div>

The <span class="inlinecode">+</span> operator will bind tighter than
<span class="inlinecode">::</span>, so <span class="inlinecode">1</span>
<span class="inlinecode">+</span> <span class="inlinecode">2</span>
<span class="inlinecode">::</span> <span class="inlinecode">[3]</span>
will be parsed, as we'd expect, as <span class="inlinecode">(1</span>
<span class="inlinecode">+</span> <span class="inlinecode">2)</span>
<span class="inlinecode">::</span> <span class="inlinecode">[3]</span>
rather than <span class="inlinecode">1</span> <span
class="inlinecode">+</span> <span class="inlinecode">(2</span> <span
class="inlinecode">::</span> <span class="inlinecode">[3])</span>.
<div class="paragraph">

</div>

(By the way, it's worth noting in passing that expressions like "<span
class="inlinecode">1</span> <span class="inlinecode">+</span> <span
class="inlinecode">2</span> <span class="inlinecode">::</span> <span
class="inlinecode">[3]</span>" can be a little confusing when you read
them in a .v file. The inner brackets, around 3, indicate a list, but
the outer brackets, which are invisible in the HTML rendering, are there
to instruct the "coqdoc" tool that the bracketed part should be
displayed as Coq code rather than running text.)
<div class="paragraph">

</div>

The second and third <span class="inlinecode"><span class="id"
type="keyword">Notation</span></span> declarations above introduce the
standard square-bracket notation for lists; the right-hand side of the
third one illustrates Coq's syntax for declaring n-ary notations and
translating them to nested sequences of binary constructors.
<div class="paragraph">

</div>

### Repeat {.section}

A number of functions are useful for manipulating lists. For example,
the <span class="inlinecode"><span class="id"
type="tactic">repeat</span></span> function takes a number <span
class="inlinecode"><span class="id" type="var">n</span></span> and a
<span class="inlinecode"><span class="id" type="var">count</span></span>
and returns a list of length <span class="inlinecode"><span class="id"
type="var">count</span></span> where every element is <span
class="inlinecode"><span class="id" type="var">n</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="tactic">repeat</span> (<span class="id" type="var">n</span> <span
class="id" type="var">count</span> : <span class="id"
type="var">nat</span>) : <span class="id" type="var">natlist</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">count</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">O</span> ⇒ <span class="id"
type="var">nil</span>\
   | <span class="id" type="var">S</span> <span class="id"
type="var">count'</span> ⇒ <span class="id" type="var">n</span> ::
(<span class="id" type="tactic">repeat</span> <span class="id"
type="var">n</span> <span class="id" type="var">count'</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

### Length {.section}

The <span class="inlinecode"><span class="id"
type="var">length</span></span> function calculates the length of a
list.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">length</span> (<span class="id" type="var">l</span>:<span
class="id" type="var">natlist</span>) : <span class="id"
type="var">nat</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">O</span>\
   | <span class="id" type="var">h</span> :: <span class="id"
type="var">t</span> ⇒ <span class="id" type="var">S</span> (<span
class="id" type="var">length</span> <span class="id"
type="var">t</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

### Append {.section}

The <span class="inlinecode"><span class="id"
type="var">app</span></span> ("append") function concatenates two lists.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">app</span> (<span class="id" type="var">l1</span> <span
class="id" type="var">l2</span> : <span class="id"
type="var">natlist</span>) : <span class="id" type="var">natlist</span>
:=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l1</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">l2</span>\
   | <span class="id" type="var">h</span> :: <span class="id"
type="var">t</span> ⇒ <span class="id" type="var">h</span> :: (<span
class="id" type="var">app</span> <span class="id" type="var">t</span>
<span class="id" type="var">l2</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Actually, <span class="inlinecode"><span class="id"
type="var">app</span></span> will be used a lot in some parts of what
follows, so it is convenient to have an infix operator for it.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "x ++ y" := (<span
class="id" type="var">app</span> <span class="id" type="var">x</span>
<span class="id" type="var">y</span>)\
                      (<span class="id" type="var">right</span> <span
class="id" type="var">associativity</span>, <span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 60).\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_app1</span>: [1;2;3] ++ [4;5] = [1;2;3;4;5].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_app2</span>: <span class="id" type="var">nil</span> ++
[4;5] = [4;5].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_app3</span>: [1;2;3] ++ <span class="id"
type="var">nil</span> = [1;2;3].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Here are two smaller examples of programming with lists. The <span
class="inlinecode"><span class="id" type="var">hd</span></span> function
returns the first element (the "head") of the list, while <span
class="inlinecode"><span class="id" type="var">tl</span></span> returns
everything but the first element (the "tail"). Of course, the empty list
has no first element, so we must pass a default value to be returned in
that case.
<div class="paragraph">

</div>

### Head (with default) and Tail {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Definition</span> <span class="id"
type="var">hd</span> (<span class="id" type="var">default</span>:<span
class="id" type="var">nat</span>) (<span class="id"
type="var">l</span>:<span class="id" type="var">natlist</span>) : <span
class="id" type="var">nat</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">default</span>\
   | <span class="id" type="var">h</span> :: <span class="id"
type="var">t</span> ⇒ <span class="id" type="var">h</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">tl</span> (<span class="id" type="var">l</span>:<span
class="id" type="var">natlist</span>) : <span class="id"
type="var">natlist</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">nil</span>\
   | <span class="id" type="var">h</span> :: <span class="id"
type="var">t</span> ⇒ <span class="id" type="var">t</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_hd1</span>: <span class="id" type="var">hd</span> 0
[1;2;3] = 1.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_hd2</span>: <span class="id" type="var">hd</span> 0 []
= 0.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_tl</span>: <span class="id" type="var">tl</span>
[1;2;3] = [2;3].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (list\_funs) {.section}

Complete the definitions of <span class="inlinecode"><span class="id"
type="var">nonzeros</span></span>, <span class="inlinecode"><span
class="id" type="var">oddmembers</span></span> and <span
class="inlinecode"><span class="id"
type="var">countoddmembers</span></span> below. Have a look at the tests
to understand what these functions should do.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">nonzeros</span> (<span class="id" type="var">l</span>:<span
class="id" type="var">natlist</span>) : <span class="id"
type="var">natlist</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_nonzeros</span>: <span class="id"
type="var">nonzeros</span> [0;1;0;2;3;0;0] = [1;2;3].\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">oddmembers</span> (<span class="id" type="var">l</span>:<span
class="id" type="var">natlist</span>) : <span class="id"
type="var">natlist</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_oddmembers</span>: <span class="id"
type="var">oddmembers</span> [0;1;0;2;3;0;0] = [1;3].\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">countoddmembers</span> (<span class="id"
type="var">l</span>:<span class="id" type="var">natlist</span>) : <span
class="id" type="var">nat</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_countoddmembers1</span>: <span class="id"
type="var">countoddmembers</span> [1;0;3;1;4;5] = 4.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_countoddmembers2</span>: <span class="id"
type="var">countoddmembers</span> [0;2;4] = 0.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_countoddmembers3</span>: <span class="id"
type="var">countoddmembers</span> <span class="id" type="var">nil</span>
= 0.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (alternate) {.section}

Complete the definition of <span class="inlinecode"><span class="id"
type="var">alternate</span></span>, which "zips up" two lists into one,
alternating between elements taken from the first list and elements from
the second. See the tests below for more specific examples.
<div class="paragraph">

</div>

Note: one natural and elegant way of writing <span
class="inlinecode"><span class="id" type="var">alternate</span></span>
will fail to satisfy Coq's requirement that all <span
class="inlinecode"><span class="id"
type="keyword">Fixpoint</span></span> definitions be "obviously
terminating." If you find yourself in this rut, look for a slightly more
verbose solution that considers elements of both lists at the same time.
(One possible solution requires defining a new kind of pairs, but this
is not the only way.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">alternate</span> (<span class="id" type="var">l1</span> <span
class="id" type="var">l2</span> : <span class="id"
type="var">natlist</span>) : <span class="id" type="var">natlist</span>
:=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_alternate1</span>: <span class="id"
type="var">alternate</span> [1;2;3] [4;5;6] = [1;4;2;5;3;6].\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_alternate2</span>: <span class="id"
type="var">alternate</span> [1] [4;5;6] = [1;4;5;6].\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_alternate3</span>: <span class="id"
type="var">alternate</span> [1;2;3] [4] = [1;4;2;3].\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_alternate4</span>: <span class="id"
type="var">alternate</span> [] [20;30] = [20;30].\
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

Bags via Lists {.section}
--------------

<div class="paragraph">

</div>

A <span class="inlinecode"><span class="id" type="var">bag</span></span>
(or <span class="inlinecode"><span class="id"
type="var">multiset</span></span>) is like a set, but each element can
appear multiple times instead of just once. One reasonable
implementation of bags is to represent a bag of numbers as a list.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">bag</span> := <span class="id" type="var">natlist</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars (bag\_functions) {.section}

Complete the following definitions for the functions <span
class="inlinecode"><span class="id" type="var">count</span></span>,
<span class="inlinecode"><span class="id" type="var">sum</span></span>,
<span class="inlinecode"><span class="id" type="var">add</span></span>,
and <span class="inlinecode"><span class="id"
type="var">member</span></span> for bags.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">count</span> (<span class="id" type="var">v</span>:<span
class="id" type="var">nat</span>) (<span class="id"
type="var">s</span>:<span class="id" type="var">bag</span>) : <span
class="id" type="var">nat</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\

</div>

<div class="doc">

All these proofs can be done just by <span class="inlinecode"><span
class="id" type="tactic">reflexivity</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_count1</span>: <span class="id" type="var">count</span>
1 [1;2;3;1;4;1] = 3.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_count2</span>: <span class="id" type="var">count</span>
6 [1;2;3;1;4;1] = 0.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Multiset <span class="inlinecode"><span class="id"
type="var">sum</span></span> is similar to set <span
class="inlinecode"><span class="id" type="var">union</span></span>:
<span class="inlinecode"><span class="id" type="var">sum</span></span>
<span class="inlinecode"><span class="id" type="var">a</span></span>
<span class="inlinecode"><span class="id" type="var">b</span></span>
contains all the elements of <span class="inlinecode"><span class="id"
type="var">a</span></span> and of <span class="inlinecode"><span
class="id" type="var">b</span></span>. (Mathematicians usually define
<span class="inlinecode"><span class="id" type="var">union</span></span>
on multisets a little bit differently, which is why we don't use that
name for this operation.) For <span class="inlinecode"><span class="id"
type="var">sum</span></span> we're giving you a header that does not
give explicit names to the arguments. Moreover, it uses the keyword
<span class="inlinecode"><span class="id"
type="keyword">Definition</span></span> instead of <span
class="inlinecode"><span class="id"
type="keyword">Fixpoint</span></span>, so even if you had names for the
arguments, you wouldn't be able to process them recursively. The point
of stating the question this way is to encourage you to think about
whether <span class="inlinecode"><span class="id"
type="var">sum</span></span> can be implemented in another way — perhaps
by using functions that have already been defined.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">sum</span> : <span class="id" type="var">bag</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">bag</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">bag</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_sum1</span>: <span class="id" type="var">count</span> 1
(<span class="id" type="var">sum</span> [1;2;3] [1;4;1]) = 3.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">add</span> (<span class="id" type="var">v</span>:<span
class="id" type="var">nat</span>) (<span class="id"
type="var">s</span>:<span class="id" type="var">bag</span>) : <span
class="id" type="var">bag</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_add1</span>: <span class="id" type="var">count</span> 1
(<span class="id" type="var">add</span> 1 [1;4;1]) = 3.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_add2</span>: <span class="id" type="var">count</span> 5
(<span class="id" type="var">add</span> 1 [1;4;1]) = 0.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">member</span> (<span class="id" type="var">v</span>:<span
class="id" type="var">nat</span>) (<span class="id"
type="var">s</span>:<span class="id" type="var">bag</span>) : <span
class="id" type="var">bool</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_member1</span>: <span class="id"
type="var">member</span> 1 [1;4;1] = <span class="id"
type="var">true</span>.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_member2</span>: <span class="id"
type="var">member</span> 2 [1;4;1] = <span class="id"
type="var">false</span>.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (bag\_more\_functions) {.section}

Here are some more bag functions for you to practice with.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">remove\_one</span> (<span class="id"
type="var">v</span>:<span class="id" type="var">nat</span>) (<span
class="id" type="var">s</span>:<span class="id" type="var">bag</span>) :
<span class="id" type="var">bag</span> :=\
   <span
class="comment">(\* When remove\_one is applied to a bag without the number to remove,\
      it should return the same bag unchanged. \*)</span>\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_remove\_one1</span>: <span class="id"
type="var">count</span> 5 (<span class="id"
type="var">remove\_one</span> 5 [2;1;5;4;1]) = 0.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_remove\_one2</span>: <span class="id"
type="var">count</span> 5 (<span class="id"
type="var">remove\_one</span> 5 [2;1;4;1]) = 0.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_remove\_one3</span>: <span class="id"
type="var">count</span> 4 (<span class="id"
type="var">remove\_one</span> 5 [2;1;4;5;1;4]) = 2.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_remove\_one4</span>: <span class="id"
type="var">count</span> 5 (<span class="id"
type="var">remove\_one</span> 5 [2;1;5;4;5;1;4]) = 1.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">remove\_all</span> (<span class="id"
type="var">v</span>:<span class="id" type="var">nat</span>) (<span
class="id" type="var">s</span>:<span class="id" type="var">bag</span>) :
<span class="id" type="var">bag</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_remove\_all1</span>: <span class="id"
type="var">count</span> 5 (<span class="id"
type="var">remove\_all</span> 5 [2;1;5;4;1]) = 0.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_remove\_all2</span>: <span class="id"
type="var">count</span> 5 (<span class="id"
type="var">remove\_all</span> 5 [2;1;4;1]) = 0.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_remove\_all3</span>: <span class="id"
type="var">count</span> 4 (<span class="id"
type="var">remove\_all</span> 5 [2;1;4;5;1;4]) = 2.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_remove\_all4</span>: <span class="id"
type="var">count</span> 5 (<span class="id"
type="var">remove\_all</span> 5 [2;1;5;4;5;1;4;5;1;4]) = 0.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">subset</span> (<span class="id" type="var">s~1~</span>:<span
class="id" type="var">bag</span>) (<span class="id"
type="var">s~2~</span>:<span class="id" type="var">bag</span>) : <span
class="id" type="var">bool</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_subset1</span>: <span class="id"
type="var">subset</span> [1;2] [2;1;4;1] = <span class="id"
type="var">true</span>.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_subset2</span>: <span class="id"
type="var">subset</span> [1;2;2] [2;1;4;1] = <span class="id"
type="var">false</span>.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars (bag\_theorem) {.section}

Write down an interesting theorem <span class="inlinecode"><span
class="id" type="var">bag\_theorem</span></span> about bags involving
the functions <span class="inlinecode"><span class="id"
type="var">count</span></span> and <span class="inlinecode"><span
class="id" type="var">add</span></span>, and prove it. Note that, since
this problem is somewhat open-ended, it's possible that you may come up
with a theorem which is true, but whose proof requires techniques you
haven't learned yet. Feel free to ask for help if you get stuck!

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

Reasoning About Lists {.section}
=====================

<div class="paragraph">

</div>

Just as with numbers, simple facts about list-processing functions can
sometimes be proved entirely by simplification. For example, the
simplification performed by <span class="inlinecode"><span class="id"
type="tactic">reflexivity</span></span> is enough for this theorem...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">nil\_app</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l</span>:<span class="id" type="var">natlist</span>,\
   [] ++ <span class="id" type="var">l</span> = <span class="id"
type="var">l</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

... because the <span class="inlinecode">[]</span> is substituted into
the match position in the definition of <span class="inlinecode"><span
class="id" type="var">app</span></span>, allowing the match itself to be
simplified.
<div class="paragraph">

</div>

Also, as with numbers, it is sometimes helpful to perform case analysis
on the possible shapes (empty or non-empty) of an unknown list.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">tl\_length\_pred</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l</span>:<span class="id" type="var">natlist</span>,\
   <span class="id" type="var">pred</span> (<span class="id"
type="var">length</span> <span class="id" type="var">l</span>) = <span
class="id" type="var">length</span> (<span class="id"
type="var">tl</span> <span class="id" type="var">l</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">l</span>. <span class="id" type="tactic">destruct</span>
<span class="id" type="var">l</span> <span class="id"
type="keyword">as</span> [| <span class="id" type="var">n</span> <span
class="id" type="var">l'</span>].\
   <span class="id" type="var">Case</span> "l = nil".\
     <span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "l = cons n l'".\
     <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Here, the <span class="inlinecode"><span class="id"
type="var">nil</span></span> case works because we've chosen to define
<span class="inlinecode"><span class="id" type="var">tl</span></span>
<span class="inlinecode"><span class="id" type="var">nil</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">nil</span></span>. Notice that the <span
class="inlinecode"><span class="id" type="keyword">as</span></span>
annotation on the <span class="inlinecode"><span class="id"
type="tactic">destruct</span></span> tactic here introduces two names,
<span class="inlinecode"><span class="id" type="var">n</span></span> and
<span class="inlinecode"><span class="id" type="var">l'</span></span>,
corresponding to the fact that the <span class="inlinecode"><span
class="id" type="var">cons</span></span> constructor for lists takes two
arguments (the head and tail of the list it is constructing).
<div class="paragraph">

</div>

Usually, though, interesting theorems about lists require induction for
their proofs.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Micro-Sermon {.section}
------------

<div class="paragraph">

</div>

Simply reading example proof scripts will not get you very far! It is
very important to work through the details of each one, using Coq and
thinking about what each step achieves. Otherwise it is more or less
guaranteed that the exercises will make no sense...

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Induction on Lists {.section}
------------------

<div class="paragraph">

</div>

Proofs by induction over datatypes like <span class="inlinecode"><span
class="id" type="var">natlist</span></span> are perhaps a little less
familiar than standard natural number induction, but the basic idea is
equally simple. Each <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> declaration defines a set of data
values that can be built up from the declared constructors: a boolean
can be either <span class="inlinecode"><span class="id"
type="var">true</span></span> or <span class="inlinecode"><span
class="id" type="var">false</span></span>; a number can be either <span
class="inlinecode"><span class="id" type="var">O</span></span> or <span
class="inlinecode"><span class="id" type="var">S</span></span> applied
to a number; a list can be either <span class="inlinecode"><span
class="id" type="var">nil</span></span> or <span
class="inlinecode"><span class="id" type="var">cons</span></span>
applied to a number and a list.
<div class="paragraph">

</div>

Moreover, applications of the declared constructors to one another are
the *only* possible shapes that elements of an inductively defined set
can have, and this fact directly gives rise to a way of reasoning about
inductively defined sets: a number is either <span
class="inlinecode"><span class="id" type="var">O</span></span> or else
it is <span class="inlinecode"><span class="id"
type="var">S</span></span> applied to some *smaller* number; a list is
either <span class="inlinecode"><span class="id"
type="var">nil</span></span> or else it is <span
class="inlinecode"><span class="id" type="var">cons</span></span>
applied to some number and some *smaller* list; etc. So, if we have in
mind some proposition <span class="inlinecode"><span class="id"
type="var">P</span></span> that mentions a list <span
class="inlinecode"><span class="id" type="var">l</span></span> and we
want to argue that <span class="inlinecode"><span class="id"
type="var">P</span></span> holds for *all* lists, we can reason as
follows:
<div class="paragraph">

</div>

-   First, show that <span class="inlinecode"><span class="id"
    type="var">P</span></span> is true of <span class="inlinecode"><span
    class="id" type="var">l</span></span> when <span
    class="inlinecode"><span class="id" type="var">l</span></span> is
    <span class="inlinecode"><span class="id"
    type="var">nil</span></span>.
    <div class="paragraph">

    </div>

-   Then show that <span class="inlinecode"><span class="id"
    type="var">P</span></span> is true of <span class="inlinecode"><span
    class="id" type="var">l</span></span> when <span
    class="inlinecode"><span class="id" type="var">l</span></span> is
    <span class="inlinecode"><span class="id"
    type="var">cons</span></span> <span class="inlinecode"><span
    class="id" type="var">n</span></span> <span class="inlinecode"><span
    class="id" type="var">l'</span></span> for some number <span
    class="inlinecode"><span class="id" type="var">n</span></span> and
    some smaller list <span class="inlinecode"><span class="id"
    type="var">l'</span></span>, assuming that <span
    class="inlinecode"><span class="id" type="var">P</span></span> is
    true for <span class="inlinecode"><span class="id"
    type="var">l'</span></span>.

<div class="paragraph">

</div>

Since larger lists can only be built up from smaller ones, eventually
reaching <span class="inlinecode"><span class="id"
type="var">nil</span></span>, these two things together establish the
truth of <span class="inlinecode"><span class="id"
type="var">P</span></span> for all lists <span class="inlinecode"><span
class="id" type="var">l</span></span>. Here's a concrete example:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">app\_assoc</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l1</span> <span class="id" type="var">l2</span> <span
class="id" type="var">l3</span> : <span class="id"
type="var">natlist</span>,\
   (<span class="id" type="var">l1</span> ++ <span class="id"
type="var">l2</span>) ++ <span class="id" type="var">l3</span> = <span
class="id" type="var">l1</span> ++ (<span class="id"
type="var">l2</span> ++ <span class="id" type="var">l3</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">l1</span> <span class="id" type="var">l2</span> <span
class="id" type="var">l3</span>. <span class="id"
type="tactic">induction</span> <span class="id" type="var">l1</span>
<span class="id" type="keyword">as</span> [| <span class="id"
type="var">n</span> <span class="id" type="var">l1'</span>].\
   <span class="id" type="var">Case</span> "l1 = nil".\
     <span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "l1 = cons n l1'".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">IHl1'</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Again, this Coq proof is not especially illuminating as a static written
document — it is easy to see what's going on if you are reading the
proof in an interactive Coq session and you can see the current goal and
context at each point, but this state is not visible in the written-down
parts of the Coq proof. So a natural-language proof — one written for
human readers — will need to include more explicit signposts; in
particular, it will help the reader stay oriented if we remind them
exactly what the induction hypothesis is in the second case.
<div class="paragraph">

</div>

### Informal version {.section}

<div class="paragraph">

</div>

*Theorem*: For all lists <span class="inlinecode"><span class="id"
type="var">l1</span></span>, <span class="inlinecode"><span class="id"
type="var">l2</span></span>, and <span class="inlinecode"><span
class="id" type="var">l3</span></span>, <span class="inlinecode">(<span
class="id" type="var">l1</span></span> <span
class="inlinecode">++</span> <span class="inlinecode"><span class="id"
type="var">l2</span>)</span> <span class="inlinecode">++</span> <span
class="inlinecode"><span class="id" type="var">l3</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">l1</span></span> <span class="inlinecode">++</span> <span
class="inlinecode">(<span class="id" type="var">l2</span></span> <span
class="inlinecode">++</span> <span class="inlinecode"><span class="id"
type="var">l3</span>)</span>.
<div class="paragraph">

</div>

*Proof*: By induction on <span class="inlinecode"><span class="id"
type="var">l1</span></span>.
<div class="paragraph">

</div>

-   First, suppose <span class="inlinecode"><span class="id"
    type="var">l1</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode">[]</span>. We must show
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      ([] ++ <span class="id" type="var">l2</span>) ++ <span class="id"
    type="var">l3</span> = [] ++ (<span class="id"
    type="var">l2</span> ++ <span class="id" type="var">l3</span>),
    <div class="paragraph">

    </div>

    </div>

    which follows directly from the definition of <span
    class="inlinecode">++</span>.
    <div class="paragraph">

    </div>

-   Next, suppose <span class="inlinecode"><span class="id"
    type="var">l1</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">n</span>::<span
    class="id" type="var">l1'</span></span>, with
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      (<span class="id" type="var">l1'</span> ++ <span class="id"
    type="var">l2</span>) ++ <span class="id"
    type="var">l3</span> = <span class="id"
    type="var">l1'</span> ++ (<span class="id"
    type="var">l2</span> ++ <span class="id" type="var">l3</span>)
    <div class="paragraph">

    </div>

    </div>

    (the induction hypothesis). We must show
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      ((<span class="id" type="var">n</span> :: <span class="id"
    type="var">l1'</span>) ++ <span class="id"
    type="var">l2</span>) ++ <span class="id"
    type="var">l3</span> = (<span class="id"
    type="var">n</span> :: <span class="id"
    type="var">l1'</span>) ++ (<span class="id"
    type="var">l2</span> ++ <span class="id" type="var">l3</span>).
    <div class="paragraph">

    </div>

    </div>

    By the definition of <span class="inlinecode">++</span>, this
    follows from
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">n</span> :: ((<span class="id"
    type="var">l1'</span> ++ <span class="id"
    type="var">l2</span>) ++ <span class="id"
    type="var">l3</span>) = <span class="id"
    type="var">n</span> :: (<span class="id"
    type="var">l1'</span> ++ (<span class="id"
    type="var">l2</span> ++ <span class="id" type="var">l3</span>)),
    <div class="paragraph">

    </div>

    </div>

    which is immediate from the induction hypothesis. ☐

<div class="paragraph">

</div>

### Another example {.section}

<div class="paragraph">

</div>

Here is a similar example to be worked together in class:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">app\_length</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l1</span> <span class="id" type="var">l2</span> : <span
class="id" type="var">natlist</span>,\
   <span class="id" type="var">length</span> (<span class="id"
type="var">l1</span> ++ <span class="id" type="var">l2</span>) = (<span
class="id" type="var">length</span> <span class="id"
type="var">l1</span>) + (<span class="id" type="var">length</span> <span
class="id" type="var">l2</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* WORKED IN CLASS \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">l1</span> <span class="id" type="var">l2</span>. <span
class="id" type="tactic">induction</span> <span class="id"
type="var">l1</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">n</span> <span class="id" type="var">l1'</span>].\
   <span class="id" type="var">Case</span> "l1 = nil".\
     <span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "l1 = cons".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">IHl1'</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Reversing a list {.section}

For a slightly more involved example of an inductive proof over lists,
suppose we define a "cons on the right" function <span
class="inlinecode"><span class="id" type="var">snoc</span></span> like
this...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">snoc</span> (<span class="id" type="var">l</span>:<span
class="id" type="var">natlist</span>) (<span class="id"
type="var">v</span>:<span class="id" type="var">nat</span>) : <span
class="id" type="var">natlist</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ [<span class="id"
type="var">v</span>]\
   | <span class="id" type="var">h</span> :: <span class="id"
type="var">t</span> ⇒ <span class="id" type="var">h</span> :: (<span
class="id" type="var">snoc</span> <span class="id" type="var">t</span>
<span class="id" type="var">v</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

... and use it to define a list-reversing function <span
class="inlinecode"><span class="id" type="var">rev</span></span> like
this:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">rev</span> (<span class="id" type="var">l</span>:<span
class="id" type="var">natlist</span>) : <span class="id"
type="var">natlist</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">nil</span>\
   | <span class="id" type="var">h</span> :: <span class="id"
type="var">t</span> ⇒ <span class="id" type="var">snoc</span> (<span
class="id" type="var">rev</span> <span class="id" type="var">t</span>)
<span class="id" type="var">h</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_rev1</span>: <span class="id" type="var">rev</span>
[1;2;3] = [3;2;1].\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_rev2</span>: <span class="id" type="var">rev</span>
<span class="id" type="var">nil</span> = <span class="id"
type="var">nil</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Proofs about reverse {.section}

Now let's prove some more list theorems using our newly defined <span
class="inlinecode"><span class="id" type="var">snoc</span></span> and
<span class="inlinecode"><span class="id" type="var">rev</span></span>.
For something a little more challenging than the inductive proofs we've
seen so far, let's prove that reversing a list does not change its
length. Our first attempt at this proof gets stuck in the successor
case...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">rev\_length\_firsttry</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">l</span>
: <span class="id" type="var">natlist</span>,\
   <span class="id" type="var">length</span> (<span class="id"
type="var">rev</span> <span class="id" type="var">l</span>) = <span
class="id" type="var">length</span> <span class="id"
type="var">l</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">l</span>. <span class="id" type="tactic">induction</span>
<span class="id" type="var">l</span> <span class="id"
type="keyword">as</span> [| <span class="id" type="var">n</span> <span
class="id" type="var">l'</span>].\
   <span class="id" type="var">Case</span> "l = []".\
     <span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "l = n :: l'".\
     <span
class="comment">(\* This is the tricky case.  Let's begin as usual \
        by simplifying. \*)</span>\
     <span class="id" type="tactic">simpl</span>.\
     <span
class="comment">(\* Now we seem to be stuck: the goal is an equality \
        involving <span class="inlinecode"><span class="id"
type="var">snoc</span></span>, but we don't have any equations \
        in either the immediate context or the global \
        environment that have anything to do with <span
class="inlinecode"><span class="id" type="var">snoc</span></span>! \
\
        We can make a little progress by using the IH to \
        rewrite the goal... \*)</span>\
     <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">IHl'</span>.\
     <span
class="comment">(\* ... but now we can't go any further. \*)</span>\
 <span class="id" type="keyword">Abort</span>.\
\

</div>

<div class="doc">

So let's take the equation about <span class="inlinecode"><span
class="id" type="var">snoc</span></span> that would have enabled us to
make progress and prove it as a separate lemma.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">length\_snoc</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
: <span class="id" type="var">nat</span>, <span
style="font-family: arial;">∀</span><span class="id" type="var">l</span>
: <span class="id" type="var">natlist</span>,\
   <span class="id" type="var">length</span> (<span class="id"
type="var">snoc</span> <span class="id" type="var">l</span> <span
class="id" type="var">n</span>) = <span class="id" type="var">S</span>
(<span class="id" type="var">length</span> <span class="id"
type="var">l</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">l</span>. <span
class="id" type="tactic">induction</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">n'</span> <span class="id" type="var">l'</span>].\
   <span class="id" type="var">Case</span> "l = nil".\
     <span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "l = cons n' l'".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">IHl'</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Note that we make the lemma as *general* as possible: in particular, we
quantify over *all* <span class="inlinecode"><span class="id"
type="var">natlist</span></span>s, not just those that result from an
application of <span class="inlinecode"><span class="id"
type="var">rev</span></span>. This should seem natural, because the
truth of the goal clearly doesn't depend on the list having been
reversed. Moreover, it is much easier to prove the more general
property.
<div class="paragraph">

</div>

Now we can complete the original proof.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">rev\_length</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">l</span>
: <span class="id" type="var">natlist</span>,\
   <span class="id" type="var">length</span> (<span class="id"
type="var">rev</span> <span class="id" type="var">l</span>) = <span
class="id" type="var">length</span> <span class="id"
type="var">l</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">l</span>. <span class="id" type="tactic">induction</span>
<span class="id" type="var">l</span> <span class="id"
type="keyword">as</span> [| <span class="id" type="var">n</span> <span
class="id" type="var">l'</span>].\
   <span class="id" type="var">Case</span> "l = nil".\
     <span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "l = cons".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">length\_snoc</span>.\
     <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">IHl'</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

For comparison, here are informal proofs of these two theorems:
<div class="paragraph">

</div>

*Theorem*: For all numbers <span class="inlinecode"><span class="id"
type="var">n</span></span> and lists <span class="inlinecode"><span
class="id" type="var">l</span></span>, <span class="inlinecode"><span
class="id" type="var">length</span></span> <span
class="inlinecode">(<span class="id" type="var">snoc</span></span> <span
class="inlinecode"><span class="id" type="var">l</span></span> <span
class="inlinecode"><span class="id" type="var">n</span>)</span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">S</span></span> <span class="inlinecode">(<span class="id"
type="var">length</span></span> <span class="inlinecode"><span
class="id" type="var">l</span>)</span>.
<div class="paragraph">

</div>

*Proof*: By induction on <span class="inlinecode"><span class="id"
type="var">l</span></span>.
<div class="paragraph">

</div>

-   First, suppose <span class="inlinecode"><span class="id"
    type="var">l</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode">[]</span>. We must show
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">length</span> (<span class="id"
    type="var">snoc</span> [] <span class="id"
    type="var">n</span>) = <span class="id" type="var">S</span> (<span
    class="id" type="var">length</span> []),
    <div class="paragraph">

    </div>

    </div>

    which follows directly from the definitions of <span
    class="inlinecode"><span class="id" type="var">length</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">snoc</span></span>.
    <div class="paragraph">

    </div>

-   Next, suppose <span class="inlinecode"><span class="id"
    type="var">l</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">n'</span>::<span
    class="id" type="var">l'</span></span>, with
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">length</span> (<span class="id"
    type="var">snoc</span> <span class="id" type="var">l'</span> <span
    class="id" type="var">n</span>) = <span class="id"
    type="var">S</span> (<span class="id" type="var">length</span> <span
    class="id" type="var">l'</span>).
    <div class="paragraph">

    </div>

    </div>

    We must show
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">length</span> (<span class="id"
    type="var">snoc</span> (<span class="id"
    type="var">n'</span> :: <span class="id" type="var">l'</span>) <span
    class="id" type="var">n</span>) = <span class="id"
    type="var">S</span> (<span class="id"
    type="var">length</span> (<span class="id"
    type="var">n'</span> :: <span class="id" type="var">l'</span>)).
    <div class="paragraph">

    </div>

    </div>

    By the definitions of <span class="inlinecode"><span class="id"
    type="var">length</span></span> and <span class="inlinecode"><span
    class="id" type="var">snoc</span></span>, this follows from
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">S</span> (<span class="id"
    type="var">length</span> (<span class="id"
    type="var">snoc</span> <span class="id" type="var">l'</span> <span
    class="id" type="var">n</span>)) = <span class="id"
    type="var">S</span> (<span class="id" type="var">S</span> (<span
    class="id" type="var">length</span> <span class="id"
    type="var">l'</span>)),
    <div class="paragraph">

    </div>

    </div>

    which is immediate from the induction hypothesis. ☐

<div class="paragraph">

</div>

*Theorem*: For all lists <span class="inlinecode"><span class="id"
type="var">l</span></span>, <span class="inlinecode"><span class="id"
type="var">length</span></span> <span class="inlinecode">(<span
class="id" type="var">rev</span></span> <span class="inlinecode"><span
class="id" type="var">l</span>)</span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">length</span></span> <span class="inlinecode"><span
class="id" type="var">l</span></span>.
<div class="paragraph">

</div>

*Proof*: By induction on <span class="inlinecode"><span class="id"
type="var">l</span></span>.
<div class="paragraph">

</div>

-   First, suppose <span class="inlinecode"><span class="id"
    type="var">l</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode">[]</span>. We must show
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">length</span> (<span class="id"
    type="var">rev</span> []) = <span class="id"
    type="var">length</span> [],
    <div class="paragraph">

    </div>

    </div>

    which follows directly from the definitions of <span
    class="inlinecode"><span class="id" type="var">length</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">rev</span></span>.
    <div class="paragraph">

    </div>

-   Next, suppose <span class="inlinecode"><span class="id"
    type="var">l</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">n</span>::<span
    class="id" type="var">l'</span></span>, with
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">length</span> (<span class="id"
    type="var">rev</span> <span class="id" type="var">l'</span>) = <span
    class="id" type="var">length</span> <span class="id"
    type="var">l'</span>.
    <div class="paragraph">

    </div>

    </div>

    We must show
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">length</span> (<span class="id"
    type="var">rev</span> (<span class="id" type="var">n</span> :: <span
    class="id" type="var">l'</span>)) = <span class="id"
    type="var">length</span> (<span class="id"
    type="var">n</span> :: <span class="id" type="var">l'</span>).
    <div class="paragraph">

    </div>

    </div>

    By the definition of <span class="inlinecode"><span class="id"
    type="var">rev</span></span>, this follows from
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">length</span> (<span class="id"
    type="var">snoc</span> (<span class="id" type="var">rev</span> <span
    class="id" type="var">l'</span>) <span class="id"
    type="var">n</span>) = <span class="id" type="var">S</span> (<span
    class="id" type="var">length</span> <span class="id"
    type="var">l'</span>)
    <div class="paragraph">

    </div>

    </div>

    which, by the previous lemma, is the same as
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">S</span> (<span class="id"
    type="var">length</span> (<span class="id"
    type="var">rev</span> <span class="id"
    type="var">l'</span>)) = <span class="id" type="var">S</span> (<span
    class="id" type="var">length</span> <span class="id"
    type="var">l'</span>).
    <div class="paragraph">

    </div>

    </div>

    This is immediate from the induction hypothesis. ☐

<div class="paragraph">

</div>

Obviously, the style of these proofs is rather longwinded and pedantic.
After the first few, we might find it easier to follow proofs that give
fewer details (since we can easily work them out in our own minds or on
scratch paper if necessary) and just highlight the non-obvious steps. In
this more compressed style, the above proof might look more like this:
<div class="paragraph">

</div>

*Theorem*: For all lists <span class="inlinecode"><span class="id"
type="var">l</span></span>, <span class="inlinecode"><span class="id"
type="var">length</span></span> <span class="inlinecode">(<span
class="id" type="var">rev</span></span> <span class="inlinecode"><span
class="id" type="var">l</span>)</span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">length</span></span> <span class="inlinecode"><span
class="id" type="var">l</span></span>.
<div class="paragraph">

</div>

*Proof*: First, observe that
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="var">length</span> (<span class="id"
type="var">snoc</span> <span class="id" type="var">l</span> <span
class="id" type="var">n</span>) = <span class="id"
type="var">S</span> (<span class="id" type="var">length</span> <span
class="id" type="var">l</span>)
<div class="paragraph">

</div>

</div>

for any <span class="inlinecode"><span class="id"
type="var">l</span></span>. This follows by a straightforward induction
on <span class="inlinecode"><span class="id" type="var">l</span></span>.
The main property now follows by another straightforward induction on
<span class="inlinecode"><span class="id" type="var">l</span></span>,
using the observation together with the induction hypothesis in the case
where <span class="inlinecode"><span class="id"
type="var">l</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">n'</span>::<span
class="id" type="var">l'</span></span>. ☐
<div class="paragraph">

</div>

Which style is preferable in a given situation depends on the
sophistication of the expected audience and on how similar the proof at
hand is to ones that the audience will already be familiar with. The
more pedantic style is a good default for present purposes.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

<span class="inlinecode"><span class="id" type="var">SearchAbout</span></span> {.section}
------------------------------------------------------------------------------

<div class="paragraph">

</div>

We've seen that proofs can make use of other theorems we've already
proved, using <span class="inlinecode"><span class="id"
type="tactic">rewrite</span></span>, and later we will see other ways of
reusing previous theorems. But in order to refer to a theorem, we need
to know its name, and remembering the names of all the theorems we might
ever want to use can become quite difficult! It is often hard even to
remember what theorems have been proven, much less what they are named.
<div class="paragraph">

</div>

Coq's <span class="inlinecode"><span class="id"
type="var">SearchAbout</span></span> command is quite helpful with this.
Typing <span class="inlinecode"><span class="id"
type="var">SearchAbout</span></span> <span class="inlinecode"><span
class="id" type="var">foo</span></span> will cause Coq to display a list
of all theorems involving <span class="inlinecode"><span class="id"
type="var">foo</span></span>. For example, try uncommenting the
following to see a list of theorems that we have proved about <span
class="inlinecode"><span class="id" type="var">rev</span></span>:

</div>

<div class="code code-tight">

\
 <span class="comment">(\*  SearchAbout rev. \*)</span>\
\

</div>

<div class="doc">

Keep <span class="inlinecode"><span class="id"
type="var">SearchAbout</span></span> in mind as you do the following
exercises and throughout the rest of the course; it can save you a lot
of time!
<div class="paragraph">

</div>

Also, if you are using ProofGeneral, you can run <span
class="inlinecode"><span class="id" type="var">SearchAbout</span></span>
with <span class="inlinecode"><span class="id" type="var">C</span>-<span
class="id" type="var">c</span></span> <span class="inlinecode"><span
class="id" type="var">C</span>-<span class="id"
type="var">a</span></span> <span class="inlinecode"><span class="id"
type="var">C</span>-<span class="id" type="var">a</span></span>. Pasting
its response into your buffer can be accomplished with <span
class="inlinecode"><span class="id" type="var">C</span>-<span class="id"
type="var">c</span></span> <span class="inlinecode"><span class="id"
type="var">C</span>-;</span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

List Exercises, Part 1 {.section}
----------------------

<div class="paragraph">

</div>

#### Exercise: 3 stars (list\_exercises) {.section}

More practice with lists.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">app\_nil\_end</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">l</span>
: <span class="id" type="var">natlist</span>,\
   <span class="id" type="var">l</span> ++ [] = <span class="id"
type="var">l</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">rev\_involutive</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">l</span>
: <span class="id" type="var">natlist</span>,\
   <span class="id" type="var">rev</span> (<span class="id"
type="var">rev</span> <span class="id" type="var">l</span>) = <span
class="id" type="var">l</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

There is a short solution to the next exercise. If you find yourself
getting tangled up, step back and try to look for a simpler way.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">app\_assoc4</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l1</span> <span class="id" type="var">l2</span> <span
class="id" type="var">l3</span> <span class="id" type="var">l4</span> :
<span class="id" type="var">natlist</span>,\
   <span class="id" type="var">l1</span> ++ (<span class="id"
type="var">l2</span> ++ (<span class="id" type="var">l3</span> ++ <span
class="id" type="var">l4</span>)) = ((<span class="id"
type="var">l1</span> ++ <span class="id" type="var">l2</span>) ++ <span
class="id" type="var">l3</span>) ++ <span class="id"
type="var">l4</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">snoc\_append</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">l</span>:<span class="id" type="var">natlist</span>) (<span
class="id" type="var">n</span>:<span class="id" type="var">nat</span>),\
   <span class="id" type="var">snoc</span> <span class="id"
type="var">l</span> <span class="id" type="var">n</span> = <span
class="id" type="var">l</span> ++ [<span class="id"
type="var">n</span>].\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">distr\_rev</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l1</span> <span class="id" type="var">l2</span> : <span
class="id" type="var">natlist</span>,\
   <span class="id" type="var">rev</span> (<span class="id"
type="var">l1</span> ++ <span class="id" type="var">l2</span>) = (<span
class="id" type="var">rev</span> <span class="id"
type="var">l2</span>) ++ (<span class="id" type="var">rev</span> <span
class="id" type="var">l1</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

An exercise about your implementation of <span class="inlinecode"><span
class="id" type="var">nonzeros</span></span>:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">nonzeros\_app</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l1</span> <span class="id" type="var">l2</span> : <span
class="id" type="var">natlist</span>,\
   <span class="id" type="var">nonzeros</span> (<span class="id"
type="var">l1</span> ++ <span class="id" type="var">l2</span>) = (<span
class="id" type="var">nonzeros</span> <span class="id"
type="var">l1</span>) ++ (<span class="id" type="var">nonzeros</span>
<span class="id" type="var">l2</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (beq\_natlist) {.section}

Fill in the definition of <span class="inlinecode"><span class="id"
type="var">beq\_natlist</span></span>, which compares lists of numbers
for equality. Prove that <span class="inlinecode"><span class="id"
type="var">beq\_natlist</span></span> <span class="inlinecode"><span
class="id" type="var">l</span></span> <span class="inlinecode"><span
class="id" type="var">l</span></span> yields <span
class="inlinecode"><span class="id" type="var">true</span></span> for
every list <span class="inlinecode"><span class="id"
type="var">l</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">beq\_natlist</span> (<span class="id" type="var">l1</span>
<span class="id" type="var">l2</span> : <span class="id"
type="var">natlist</span>) : <span class="id" type="var">bool</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_beq\_natlist1</span> : (<span class="id"
type="var">beq\_natlist</span> <span class="id" type="var">nil</span>
<span class="id" type="var">nil</span> = <span class="id"
type="var">true</span>).\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_beq\_natlist2</span> : <span class="id"
type="var">beq\_natlist</span> [1;2;3] [1;2;3] = <span class="id"
type="var">true</span>.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_beq\_natlist3</span> : <span class="id"
type="var">beq\_natlist</span> [1;2;3] [1;2;4] = <span class="id"
type="var">false</span>.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">beq\_natlist\_refl</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l</span>:<span class="id" type="var">natlist</span>,\
   <span class="id" type="var">true</span> = <span class="id"
type="var">beq\_natlist</span> <span class="id" type="var">l</span>
<span class="id" type="var">l</span>.\
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

List Exercises, Part 2 {.section}
----------------------

<div class="paragraph">

</div>

#### Exercise: 2 stars (list\_design) {.section}

Design exercise:
<div class="paragraph">

</div>

-   Write down a non-trivial theorem <span class="inlinecode"><span
    class="id" type="var">cons\_snoc\_app</span></span> involving <span
    class="inlinecode"><span class="id" type="var">cons</span></span>
    (<span class="inlinecode">::</span>), <span class="inlinecode"><span
    class="id" type="var">snoc</span></span>, and <span
    class="inlinecode"><span class="id" type="var">app</span></span>
    (<span class="inlinecode">++</span>).
-   Prove it.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, advanced (bag\_proofs) {.section}

Here are a couple of little theorems to prove about your definitions
about bags earlier in the file.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">count\_member\_nonzero</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">s</span> : <span class="id" type="var">bag</span>),\
   <span class="id" type="var">ble\_nat</span> 1 (<span class="id"
type="var">count</span> 1 (1 :: <span class="id" type="var">s</span>)) =
<span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

The following lemma about <span class="inlinecode"><span class="id"
type="var">ble\_nat</span></span> might help you in the next proof.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ble\_n\_Sn</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
   <span class="id" type="var">ble\_nat</span> <span class="id"
type="var">n</span> (<span class="id" type="var">S</span> <span
class="id" type="var">n</span>) = <span class="id"
type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span>. <span class="id" type="tactic">induction</span>
<span class="id" type="var">n</span> <span class="id"
type="keyword">as</span> [| <span class="id" type="var">n'</span>].\
   <span class="id" type="var">Case</span> "0".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "S n'".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHn'</span>.
<span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">remove\_decreases\_count</span>: <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">s</span> : <span class="id" type="var">bag</span>),\
   <span class="id" type="var">ble\_nat</span> (<span class="id"
type="var">count</span> 0 (<span class="id"
type="var">remove\_one</span> 0 <span class="id" type="var">s</span>))
(<span class="id" type="var">count</span> 0 <span class="id"
type="var">s</span>) = <span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (bag\_count\_sum) {.section}

Write down an interesting theorem <span class="inlinecode"><span
class="id" type="var">bag\_count\_sum</span></span> about bags involving
the functions <span class="inlinecode"><span class="id"
type="var">count</span></span> and <span class="inlinecode"><span
class="id" type="var">sum</span></span>, and prove it.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars, advanced (rev\_injective) {.section}

Prove that the <span class="inlinecode"><span class="id"
type="var">rev</span></span> function is injective, that is,
<div class="paragraph">

</div>

<div class="paragraph">

</div>

<div class="code code-tight">

    <span style="font-family: arial;">∀</span>(<span class="id"
type="var">l1</span> <span class="id" type="var">l2</span> : <span
class="id" type="var">natlist</span>), <span class="id"
type="var">rev</span> <span class="id" type="var">l1</span> = <span
class="id" type="var">rev</span> <span class="id"
type="var">l2</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">l1</span> = <span class="id" type="var">l2</span>.
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

There is a hard way and an easy way to solve this exercise.

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

Options {.section}
=======

<div class="paragraph">

</div>

One use of <span class="inlinecode"><span class="id"
type="var">natoption</span></span> is as a way of returning "error
codes" from functions. For example, suppose we want to write a function
that returns the <span class="inlinecode"><span class="id"
type="var">n</span></span>th element of some list. If we give it type
<span class="inlinecode"><span class="id" type="var">nat</span></span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">natlist</span></span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">nat</span></span>, then
we'll have to return some number when the list is too short!

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">index\_bad</span> (<span class="id" type="var">n</span>:<span
class="id" type="var">nat</span>) (<span class="id"
type="var">l</span>:<span class="id" type="var">natlist</span>) : <span
class="id" type="var">nat</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ 42 <span
class="comment">(\* arbitrary! \*)</span>\
   | <span class="id" type="var">a</span> :: <span class="id"
type="var">l'</span> ⇒ <span class="id" type="keyword">match</span>
<span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">O</span> <span
class="id" type="keyword">with</span>\
                | <span class="id" type="var">true</span> ⇒ <span
class="id" type="var">a</span>\
                | <span class="id" type="var">false</span> ⇒ <span
class="id" type="var">index\_bad</span> (<span class="id"
type="var">pred</span> <span class="id" type="var">n</span>) <span
class="id" type="var">l'</span>\
                <span class="id" type="keyword">end</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

###  {.section}

On the other hand, if we give it type <span class="inlinecode"><span
class="id" type="var">nat</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">natlist</span></span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">natoption</span></span>,
then we can return <span class="inlinecode"><span class="id"
type="var">None</span></span> when the list is too short and <span
class="inlinecode"><span class="id" type="var">Some</span></span> <span
class="inlinecode"><span class="id" type="var">a</span></span> when the
list has enough members and <span class="inlinecode"><span class="id"
type="var">a</span></span> appears at position <span
class="inlinecode"><span class="id" type="var">n</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">natoption</span> : <span class="id"
type="keyword">Type</span> :=\
   | <span class="id" type="var">Some</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">natoption</span>\
   | <span class="id" type="var">None</span> : <span class="id"
type="var">natoption</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">index</span> (<span class="id" type="var">n</span>:<span
class="id" type="var">nat</span>) (<span class="id"
type="var">l</span>:<span class="id" type="var">natlist</span>) : <span
class="id" type="var">natoption</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">None</span>\
   | <span class="id" type="var">a</span> :: <span class="id"
type="var">l'</span> ⇒ <span class="id" type="keyword">match</span>
<span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">O</span> <span
class="id" type="keyword">with</span>\
                | <span class="id" type="var">true</span> ⇒ <span
class="id" type="var">Some</span> <span class="id" type="var">a</span>\
                | <span class="id" type="var">false</span> ⇒ <span
class="id" type="var">index</span> (<span class="id"
type="var">pred</span> <span class="id" type="var">n</span>) <span
class="id" type="var">l'</span>\
                <span class="id" type="keyword">end</span>\
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
type="var">index</span> 3 [4;5;6;7] = <span class="id"
type="var">Some</span> 7.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_index3</span> : <span class="id"
type="var">index</span> 10 [4;5;6;7] = <span class="id"
type="var">None</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

This example is also an opportunity to introduce one more small feature
of Coq's programming language: conditional expressions...
<div class="paragraph">

</div>

###  {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">index'</span> (<span class="id" type="var">n</span>:<span
class="id" type="var">nat</span>) (<span class="id"
type="var">l</span>:<span class="id" type="var">natlist</span>) : <span
class="id" type="var">natoption</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">l</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">nil</span> ⇒ <span class="id"
type="var">None</span>\
   | <span class="id" type="var">a</span> :: <span class="id"
type="var">l'</span> ⇒ <span class="id" type="keyword">if</span> <span
class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">O</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">Some</span> <span class="id" type="var">a</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">index'</span> (<span class="id" type="var">pred</span> <span
class="id" type="var">n</span>) <span class="id" type="var">l'</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Coq's conditionals are exactly like those found in any other language,
with one small generalization. Since the boolean type is not built in,
Coq actually allows conditional expressions over *any* inductively
defined type with exactly two constructors. The guard is considered true
if it evaluates to the first constructor in the <span
class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> definition and false if it
evaluates to the second.
<div class="paragraph">

</div>

The function below pulls the <span class="inlinecode"><span class="id"
type="var">nat</span></span> out of a <span class="inlinecode"><span
class="id" type="var">natoption</span></span>, returning a supplied
default in the <span class="inlinecode"><span class="id"
type="var">None</span></span> case.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">option\_elim</span> (<span class="id" type="var">d</span> :
<span class="id" type="var">nat</span>) (<span class="id"
type="var">o</span> : <span class="id" type="var">natoption</span>) :
<span class="id" type="var">nat</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">o</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">Some</span> <span class="id"
type="var">n'</span> ⇒ <span class="id" type="var">n'</span>\
   | <span class="id" type="var">None</span> ⇒ <span class="id"
type="var">d</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (hd\_opt) {.section}

Using the same idea, fix the <span class="inlinecode"><span class="id"
type="var">hd</span></span> function from earlier so we don't have to
pass a default element for the <span class="inlinecode"><span class="id"
type="var">nil</span></span> case.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">hd\_opt</span> (<span class="id" type="var">l</span> : <span
class="id" type="var">natlist</span>) : <span class="id"
type="var">natoption</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_hd\_opt1</span> : <span class="id"
type="var">hd\_opt</span> [] = <span class="id" type="var">None</span>.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_hd\_opt2</span> : <span class="id"
type="var">hd\_opt</span> [1] = <span class="id" type="var">Some</span>
1.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">test\_hd\_opt3</span> : <span class="id"
type="var">hd\_opt</span> [5;6] = <span class="id"
type="var">Some</span> 5.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (option\_elim\_hd) {.section}

This exercise relates your new <span class="inlinecode"><span class="id"
type="var">hd\_opt</span></span> to the old <span
class="inlinecode"><span class="id" type="var">hd</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">option\_elim\_hd</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">l</span>:<span class="id" type="var">natlist</span>) (<span
class="id" type="var">default</span>:<span class="id"
type="var">nat</span>),\
   <span class="id" type="var">hd</span> <span class="id"
type="var">default</span> <span class="id" type="var">l</span> = <span
class="id" type="var">option\_elim</span> <span class="id"
type="var">default</span> (<span class="id" type="var">hd\_opt</span>
<span class="id" type="var">l</span>).\
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

Dictionaries {.section}
============

<div class="paragraph">

</div>

As a final illustration of how fundamental data structures can be
defined in Coq, here is the declaration of a simple <span
class="inlinecode"><span class="id" type="var">dictionary</span></span>
data type, using numbers for both the keys and the values stored under
these keys. (That is, a dictionary represents a finite map from numbers
to numbers.)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Dictionary</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">dictionary</span> : <span class="id"
type="keyword">Type</span> :=\
   | <span class="id" type="var">empty</span> : <span class="id"
type="var">dictionary</span>\
   | <span class="id" type="var">record</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">dictionary</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">dictionary</span>.\
\

</div>

<div class="doc">

This declaration can be read: "There are two ways to construct a <span
class="inlinecode"><span class="id" type="var">dictionary</span></span>:
either using the constructor <span class="inlinecode"><span class="id"
type="var">empty</span></span> to represent an empty dictionary, or by
applying the constructor <span class="inlinecode"><span class="id"
type="var">record</span></span> to a key, a value, and an existing <span
class="inlinecode"><span class="id" type="var">dictionary</span></span>
to construct a <span class="inlinecode"><span class="id"
type="var">dictionary</span></span> with an additional key to value
mapping."

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">insert</span> (<span class="id" type="var">key</span> <span
class="id" type="var">value</span> : <span class="id"
type="var">nat</span>) (<span class="id" type="var">d</span> : <span
class="id" type="var">dictionary</span>) : <span class="id"
type="var">dictionary</span> :=\
   (<span class="id" type="var">record</span> <span class="id"
type="var">key</span> <span class="id" type="var">value</span> <span
class="id" type="var">d</span>).\
\

</div>

<div class="doc">

Here is a function <span class="inlinecode"><span class="id"
type="var">find</span></span> that searches a <span
class="inlinecode"><span class="id" type="var">dictionary</span></span>
for a given key. It evaluates evaluates to <span
class="inlinecode"><span class="id" type="var">None</span></span> if the
key was not found and <span class="inlinecode"><span class="id"
type="var">Some</span></span> <span class="inlinecode"><span class="id"
type="var">val</span></span> if the key was mapped to <span
class="inlinecode"><span class="id" type="var">val</span></span> in the
dictionary. If the same key is mapped to multiple values, <span
class="inlinecode"><span class="id" type="var">find</span></span> will
return the first one it finds.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">find</span> (<span class="id" type="var">key</span> : <span
class="id" type="var">nat</span>) (<span class="id" type="var">d</span>
: <span class="id" type="var">dictionary</span>) : <span class="id"
type="var">natoption</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">d</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">empty</span> ⇒ <span class="id"
type="var">None</span>\
   | <span class="id" type="var">record</span> <span class="id"
type="var">k</span> <span class="id" type="var">v</span> <span
class="id" type="var">d'</span> ⇒ <span class="id"
type="keyword">if</span> (<span class="id" type="var">beq\_nat</span>
<span class="id" type="var">key</span> <span class="id"
type="var">k</span>)\
                        <span class="id" type="keyword">then</span>
(<span class="id" type="var">Some</span> <span class="id"
type="var">v</span>)\
                        <span class="id" type="keyword">else</span>
(<span class="id" type="var">find</span> <span class="id"
type="var">key</span> <span class="id" type="var">d'</span>)\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star (dictionary\_invariant1) {.section}

Complete the following proof.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">dictionary\_invariant1'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">d</span> : <span class="id" type="var">dictionary</span>)
(<span class="id" type="var">k</span> <span class="id"
type="var">v</span>: <span class="id" type="var">nat</span>),\
   (<span class="id" type="var">find</span> <span class="id"
type="var">k</span> (<span class="id" type="var">insert</span> <span
class="id" type="var">k</span> <span class="id" type="var">v</span>
<span class="id" type="var">d</span>)) = <span class="id"
type="var">Some</span> <span class="id" type="var">v</span>.\
 <span class="id" type="keyword">Proof</span>.\
  <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star (dictionary\_invariant2) {.section}

Complete the following proof.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">dictionary\_invariant2'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">d</span> : <span class="id" type="var">dictionary</span>)
(<span class="id" type="var">m</span> <span class="id"
type="var">n</span> <span class="id" type="var">o</span>: <span
class="id" type="var">nat</span>),\
   <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">m</span> <span class="id" type="var">n</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">find</span> <span class="id" type="var">m</span> <span
class="id" type="var">d</span> = <span class="id" type="var">find</span>
<span class="id" type="var">m</span> (<span class="id"
type="var">insert</span> <span class="id" type="var">n</span> <span
class="id" type="var">o</span> <span class="id" type="var">d</span>).\
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
type="var">Dictionary</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">NatList</span>.\
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
