<div id="page">

<div id="header">

</div>

<div id="main">

ProofObjects<span class="subtitle">Working with Explicit Evidence in Coq</span> {.libtitle}
===============================================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id"
type="var">MoreLogic</span>.\
\
\

</div>

<div class="doc">

We have seen that Coq has mechanisms both for *programming*, using
inductive data types (like <span class="inlinecode"><span class="id"
type="var">nat</span></span> or <span class="inlinecode"><span
class="id" type="var">list</span></span>) and functions over these
types, and for *proving* properties of these programs, using inductive
propositions (like <span class="inlinecode"><span class="id"
type="var">ev</span></span> or <span class="inlinecode"><span class="id"
type="var">eq</span></span>), implication, and universal quantification.
So far, we have treated these mechanisms as if they were quite separate,
and for many purposes this is a good way to think. But we have also seen
hints that Coq's programming and proving facilities are closely related.
For example, the keyword <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> is used to declare both data
types and propositions, and <span class="inlinecode"><span
style="font-family: arial;">→</span></span> is used both to describe the
type of functions on data and logical implication. This is not just a
syntactic accident! In fact, programs and proofs in Coq are almost the
same thing. In this chapter we will study how this works.
<div class="paragraph">

</div>

We have already seen the fundamental idea: provability in Coq is
represented by concrete *evidence*. When we construct the proof of a
basic proposition, we are actually building a tree of evidence, which
can be thought of as a data structure. If the proposition is an
implication like <span class="inlinecode"><span class="id"
type="var">A</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">B</span></span>, then its
proof will be an evidence *transformer*: a recipe for converting
evidence for A into evidence for B. So at a fundamental level, proofs
are simply programs that manipulate evidence.
<div class="paragraph">

</div>

Q. If evidence is data, what are propositions themselves?
<div class="paragraph">

</div>

A. They are types!
<div class="paragraph">

</div>

Look again at the formal definition of the <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>
property.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">beautiful</span>.\
 <span class="comment">(\* ==\>\
   Inductive beautiful : nat -\> Prop :=\
       b\_0 : beautiful 0\
     | b\_3 : beautiful 3\
     | b\_5 : beautiful 5\

    | b\_sum : forall n m : nat, beautiful n -\> beautiful m -\> beautiful (n + m)\
 \*)</span>\
\

</div>

<div class="doc">

###  {.section}

<div class="paragraph">

</div>

The trick is to introduce an alternative pronunciation of "<span
class="inlinecode">:</span>". Instead of "has type," we can also say "is
a proof of." For example, the second line in the definition of <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>
declares that <span class="inlinecode"><span class="id"
type="var">b\_0</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>
<span class="inlinecode">0</span>. Instead of "<span
class="inlinecode"><span class="id" type="var">b\_0</span></span> has
type <span class="inlinecode"><span class="id"
type="var">beautiful</span></span> <span class="inlinecode">0</span>,"
we can say that "<span class="inlinecode"><span class="id"
type="var">b\_0</span></span> is a proof of <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>
<span class="inlinecode">0</span>." Similarly for <span
class="inlinecode"><span class="id" type="var">b\_3</span></span> and
<span class="inlinecode"><span class="id" type="var">b\_5</span></span>.
<div class="paragraph">

</div>

###  {.section}

<div class="paragraph">

</div>

This pun between types and propositions (between <span
class="inlinecode">:</span> as "has type" and <span
class="inlinecode">:</span> as "is a proof of" or "is evidence for") is
called the *Curry-Howard correspondence*. It proposes a deep connection
between the world of logic and the world of computation.
                     propositions  ~  types
                     proofs        ~  data values

Many useful insights follow from this connection. To begin with, it
gives us a natural interpretation of the type of <span
class="inlinecode"><span class="id" type="var">b\_sum</span></span>
constructor:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">b\_sum</span>.\
 <span class="comment">(\* ===\> b\_sum : forall n m, \
                   beautiful n -\> \
                   beautiful m -\> \
                   beautiful (n+m) \*)</span>\

</div>

<div class="doc">

This can be read "<span class="inlinecode"><span class="id"
type="var">b\_sum</span></span> is a constructor that takes four
arguments — two numbers, <span class="inlinecode"><span class="id"
type="var">n</span></span> and <span class="inlinecode"><span class="id"
type="var">m</span></span>, and two pieces of evidence, for the
propositions <span class="inlinecode"><span class="id"
type="var">beautiful</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> and <span class="inlinecode"><span
class="id" type="var">beautiful</span></span> <span
class="inlinecode"><span class="id" type="var">m</span></span>,
respectively — and yields evidence for the proposition <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>
<span class="inlinecode">(<span class="id" type="var">n</span>+<span
class="id" type="var">m</span>)</span>."
<div class="paragraph">

</div>

Now let's look again at a previous proof involving <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">eight\_is\_beautiful</span>: <span class="id"
type="var">beautiful</span> 8.\
 <span class="id" type="keyword">Proof</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_sum</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">n</span> := 3) (<span class="id"
type="var">m</span> := 5).\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_3</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_5</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Just as with ordinary data values and functions, we can use the <span
class="inlinecode"><span class="id" type="keyword">Print</span></span>
command to see the *proof object* that results from this proof script.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">eight\_is\_beautiful</span>.\
 <span
class="comment">(\* ===\> eight\_is\_beautiful = b\_sum 3 5 b\_3 b\_5  \
      : beautiful 8  \*)</span>\
\

</div>

<div class="doc">

In view of this, we might wonder whether we can write such an expression
ourselves. Indeed, we can:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> (<span class="id"
type="var">b\_sum</span> 3 5 <span class="id" type="var">b\_3</span>
<span class="id" type="var">b\_5</span>).\
 <span class="comment">(\* ===\> beautiful (3 + 5) \*)</span>\
\

</div>

<div class="doc">

The expression <span class="inlinecode"><span class="id"
type="var">b\_sum</span></span> <span class="inlinecode">3</span> <span
class="inlinecode">5</span> <span class="inlinecode"><span class="id"
type="var">b\_3</span></span> <span class="inlinecode"><span class="id"
type="var">b\_5</span></span> can be thought of as instantiating the
parameterized constructor <span class="inlinecode"><span class="id"
type="var">b\_sum</span></span> with the specific arguments <span
class="inlinecode">3</span> <span class="inlinecode">5</span> and the
corresponding proof objects for its premises <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>
<span class="inlinecode">3</span> and <span class="inlinecode"><span
class="id" type="var">beautiful</span></span> <span
class="inlinecode">5</span> (Coq is smart enough to figure out that
3+5=8). Alternatively, we can think of <span class="inlinecode"><span
class="id" type="var">b\_sum</span></span> as a primitive "evidence
constructor" that, when applied to two particular numbers, wants to be
further applied to evidence that those two numbers are beautiful; its
type,
<div class="paragraph">

</div>

<div class="code code-tight">

    <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span> <span class="id" type="var">m</span>, <span
class="id" type="var">beautiful</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">beautiful</span> <span class="id"
type="var">m</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">beautiful</span> (<span class="id"
type="var">n</span>+<span class="id" type="var">m</span>),
<div class="paragraph">

</div>

</div>

expresses this functionality, in the same way that the polymorphic type
<span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">X</span>,</span> <span
class="inlinecode"><span class="id" type="var">list</span></span> <span
class="inlinecode"><span class="id" type="var">X</span></span> in the
previous chapter expressed the fact that the constructor <span
class="inlinecode"><span class="id" type="var">nil</span></span> can be
thought of as a function from types to empty lists with elements of that
type.
<div class="paragraph">

</div>

This gives us an alternative way to write the proof that <span
class="inlinecode">8</span> is beautiful:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">eight\_is\_beautiful'</span>: <span class="id"
type="var">beautiful</span> 8.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">apply</span> (<span class="id"
type="var">b\_sum</span> 3 5 <span class="id" type="var">b\_3</span>
<span class="id" type="var">b\_5</span>).\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Notice that we're using <span class="inlinecode"><span class="id"
type="tactic">apply</span></span> here in a new way: instead of just
supplying the *name* of a hypothesis or previously proved theorem whose
type matches the current goal, we are supplying an *expression* that
directly builds evidence with the required type.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Proof Scripts and Proof Objects {.section}
===============================

<div class="paragraph">

</div>

These proof objects lie at the core of how Coq operates.
<div class="paragraph">

</div>

When Coq is following a proof script, what is happening internally is
that it is gradually constructing a proof object — a term whose type is
the proposition being proved. The tactics between the <span
class="inlinecode"><span class="id" type="keyword">Proof</span></span>
command and the <span class="inlinecode"><span class="id"
type="keyword">Qed</span></span> instruct Coq how to build up a term of
the required type. To see this process in action, let's use the <span
class="inlinecode"><span class="id" type="keyword">Show</span></span>
<span class="inlinecode"><span class="id"
type="keyword">Proof</span></span> command to display the current state
of the proof tree at various points in the following tactic proof.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">eight\_is\_beautiful''</span>: <span class="id"
type="var">beautiful</span> 8.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="keyword">Show</span> <span class="id"
type="keyword">Proof</span>.\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_sum</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">n</span>:=3) (<span class="id"
type="var">m</span>:=5).\
    <span class="id" type="keyword">Show</span> <span class="id"
type="keyword">Proof</span>.\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_3</span>.\
    <span class="id" type="keyword">Show</span> <span class="id"
type="keyword">Proof</span>.\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_5</span>.\
    <span class="id" type="keyword">Show</span> <span class="id"
type="keyword">Proof</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

At any given moment, Coq has constructed a term with some "holes"
(indicated by <span class="inlinecode">?1</span>, <span
class="inlinecode">?2</span>, and so on), and it knows what type of
evidence is needed at each hole.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

Each of the holes corresponds to a subgoal, and the proof is finished
when there are no more subgoals. At this point, the <span
class="inlinecode"><span class="id" type="keyword">Theorem</span></span>
command gives a name to the evidence we've built and stores it in the
global context.
<div class="paragraph">

</div>

Tactic proofs are useful and convenient, but they are not essential: in
principle, we can always construct the required evidence by hand, as
shown above. Then we can use <span class="inlinecode"><span class="id"
type="keyword">Definition</span></span> (rather than <span
class="inlinecode"><span class="id"
type="keyword">Theorem</span></span>) to give a global name directly to
a piece of evidence.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">eight\_is\_beautiful'''</span> : <span class="id"
type="var">beautiful</span> 8 :=\
   <span class="id" type="var">b\_sum</span> 3 5 <span class="id"
type="var">b\_3</span> <span class="id" type="var">b\_5</span>.\
\

</div>

<div class="doc">

All these different ways of building the proof lead to exactly the same
evidence being saved in the global environment.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">eight\_is\_beautiful</span>.\
 <span
class="comment">(\* ===\> eight\_is\_beautiful    = b\_sum 3 5 b\_3 b\_5 : beautiful 8 \*)</span>\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">eight\_is\_beautiful'</span>.\
 <span
class="comment">(\* ===\> eight\_is\_beautiful'   = b\_sum 3 5 b\_3 b\_5 : beautiful 8 \*)</span>\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">eight\_is\_beautiful''</span>.\
 <span
class="comment">(\* ===\> eight\_is\_beautiful''  = b\_sum 3 5 b\_3 b\_5 : beautiful 8 \*)</span>\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">eight\_is\_beautiful'''</span>.\
 <span
class="comment">(\* ===\> eight\_is\_beautiful''' = b\_sum 3 5 b\_3 b\_5 : beautiful 8 \*)</span>\
\

</div>

<div class="doc">

#### Exercise: 1 star (six\_is\_beautiful) {.section}

Give a tactic proof and a proof object showing that <span
class="inlinecode">6</span> is <span class="inlinecode"><span class="id"
type="var">beautiful</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">six\_is\_beautiful</span> :\
   <span class="id" type="var">beautiful</span> 6.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">six\_is\_beautiful'</span> : <span class="id"
type="var">beautiful</span> 6 :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star (nine\_is\_beautiful) {.section}

Give a tactic proof and a proof object showing that <span
class="inlinecode">9</span> is <span class="inlinecode"><span class="id"
type="var">beautiful</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">nine\_is\_beautiful</span> :\
   <span class="id" type="var">beautiful</span> 9.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">nine\_is\_beautiful'</span> : <span class="id"
type="var">beautiful</span> 9 :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Quantification, Implications and Functions {.section}
==========================================

<div class="paragraph">

</div>

In Coq's computational universe (where we've mostly been living until
this chapter), there are two sorts of values with arrows in their types:
*constructors* introduced by <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span>-ly defined data types, and
*functions*.
<div class="paragraph">

</div>

Similarly, in Coq's logical universe, there are two ways of giving
evidence for an implication: constructors introduced by <span
class="inlinecode"><span class="id"
type="keyword">Inductive</span></span>-ly defined propositions, and...
functions!
<div class="paragraph">

</div>

For example, consider this statement:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">b\_plus3</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">beautiful</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">beautiful</span> (3+<span class="id" type="var">n</span>).\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">intros</span> <span class="id"
type="var">n</span> <span class="id" type="var">H</span>.\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_sum</span>.\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">b\_3</span>.\
    <span class="id" type="tactic">apply</span> <span class="id"
type="var">H</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

What is the proof object corresponding to <span class="inlinecode"><span
class="id" type="var">b\_plus3</span></span>?
<div class="paragraph">

</div>

We're looking for an expression whose *type* is <span
class="inlinecode"><span style="font-family: arial;">∀</span></span>
<span class="inlinecode"><span class="id" type="var">n</span>,</span>
<span class="inlinecode"><span class="id"
type="var">beautiful</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>
<span class="inlinecode">(3+<span class="id" type="var">n</span>)</span>
— that is, a *function* that takes two arguments (one number and a piece
of evidence) and returns a piece of evidence! Here it is:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">b\_plus3'</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">beautiful</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">beautiful</span> (3+<span class="id" type="var">n</span>) :=\
   <span class="id" type="keyword">fun</span> (<span class="id"
type="var">n</span> : <span class="id" type="var">nat</span>) ⇒ <span
class="id" type="keyword">fun</span> (<span class="id"
type="var">H</span> : <span class="id" type="var">beautiful</span> <span
class="id" type="var">n</span>) ⇒\
     <span class="id" type="var">b\_sum</span> 3 <span class="id"
type="var">n</span> <span class="id" type="var">b\_3</span> <span
class="id" type="var">H</span>.\
\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">b\_plus3'</span>.\
 <span
class="comment">(\* ===\> b\_plus3' : forall n : nat, beautiful n -\> beautiful (3+n) \*)</span>\
\

</div>

<div class="doc">

Recall that <span class="inlinecode"><span class="id"
type="keyword">fun</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode">⇒</span>
<span class="inlinecode"><span class="id" type="var">blah</span></span>
means "the function that, given <span class="inlinecode"><span
class="id" type="var">n</span></span>, yields <span
class="inlinecode"><span class="id" type="var">blah</span></span>."
Another equivalent way to write this definition is:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">b\_plus3''</span> (<span class="id" type="var">n</span> :
<span class="id" type="var">nat</span>) (<span class="id"
type="var">H</span> : <span class="id" type="var">beautiful</span> <span
class="id" type="var">n</span>) : <span class="id"
type="var">beautiful</span> (3+<span class="id" type="var">n</span>) :=\
   <span class="id" type="var">b\_sum</span> 3 <span class="id"
type="var">n</span> <span class="id" type="var">b\_3</span> <span
class="id" type="var">H</span>.\
\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">b\_plus3''</span>.\
 <span
class="comment">(\* ===\> b\_plus3'' : forall n, beautiful n -\> beautiful (3+n) \*)</span>\
\

</div>

<div class="doc">

When we view the proposition being proved by <span
class="inlinecode"><span class="id" type="var">b\_plus3</span></span> as
a function type, one aspect of it may seem a little unusual. The second
argument's type, <span class="inlinecode"><span class="id"
type="var">beautiful</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span>, mentions the *value* of the first
argument, <span class="inlinecode"><span class="id"
type="var">n</span></span>. While such *dependent types* are not
commonly found in programming languages, even functional ones like ML or
Haskell, they can be useful there too.
<div class="paragraph">

</div>

Notice that both implication (<span class="inlinecode"><span
style="font-family: arial;">→</span></span>) and quantification (<span
class="inlinecode"><span style="font-family: arial;">∀</span></span>)
correspond to functions on evidence. In fact, they are really the same
thing: <span class="inlinecode"><span
style="font-family: arial;">→</span></span> is just a shorthand for a
degenerate use of <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> where there is no
dependency, i.e., no need to give a name to the type on the LHS of the
arrow.
<div class="paragraph">

</div>

For example, consider this proposition:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">beautiful\_plus3</span> : <span class="id"
type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span style="font-family: arial;">∀</span>(<span
class="id" type="var">E</span> : <span class="id"
type="var">beautiful</span> <span class="id" type="var">n</span>), <span
class="id" type="var">beautiful</span> (<span class="id"
type="var">n</span>+3).\
\

</div>

<div class="doc">

A proof term inhabiting this proposition would be a function with two
arguments: a number <span class="inlinecode"><span class="id"
type="var">n</span></span> and some evidence <span
class="inlinecode"><span class="id" type="var">E</span></span> that
<span class="inlinecode"><span class="id" type="var">n</span></span> is
beautiful. But the name <span class="inlinecode"><span class="id"
type="var">E</span></span> for this evidence is not used in the rest of
the statement of <span class="inlinecode"><span class="id"
type="var">funny\_prop1</span></span>, so it's a bit silly to bother
making up a name for it. We could write it like this instead, using the
dummy identifier <span class="inlinecode"><span class="id"
type="var">\_</span></span> in place of a real name:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">beautiful\_plus3'</span> : <span class="id"
type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span style="font-family: arial;">∀</span>(<span
class="id" type="var">\_</span> : <span class="id"
type="var">beautiful</span> <span class="id" type="var">n</span>), <span
class="id" type="var">beautiful</span> (<span class="id"
type="var">n</span>+3).\
\

</div>

<div class="doc">

Or, equivalently, we can write it in more familiar notation:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">beatiful\_plus3''</span> : <span class="id"
type="keyword">Prop</span> :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">beautiful</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">beautiful</span> (<span class="id" type="var">n</span>+3).\
\

</div>

<div class="doc">

In general, "<span class="inlinecode"><span class="id"
type="var">P</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">Q</span></span>" is just
syntactic sugar for "<span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode">(<span class="id" type="var">\_</span>:<span
class="id" type="var">P</span>),</span> <span class="inlinecode"><span
class="id" type="var">Q</span></span>".
<div class="paragraph">

</div>

#### Exercise: 2 stars b\_times2 {.section}

<div class="paragraph">

</div>

Give a proof object corresponding to the theorem <span
class="inlinecode"><span class="id" type="var">b\_times2</span></span>
from Prop.v

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">b\_times2'</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">beautiful</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">beautiful</span> (2×<span class="id" type="var">n</span>) :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (gorgeous\_plus13\_po) {.section}

Give a proof object corresponding to the theorem <span
class="inlinecode"><span class="id"
type="var">gorgeous\_plus13</span></span> from Prop.v

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">gorgeous\_plus13\_po</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">gorgeous</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">gorgeous</span> (13+<span class="id" type="var">n</span>):=\
    <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

It is particularly revealing to look at proof objects involving the
logical connectives that we defined with inductive propositions in
Logic.v.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">and\_example</span> :\
   (<span class="id" type="var">beautiful</span> 0) <span
style="font-family: arial;">∧</span> (<span class="id"
type="var">beautiful</span> 3).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">conj</span>.\
    <span class="comment">(\* Case "left". \*)</span> <span class="id"
type="tactic">apply</span> <span class="id" type="var">b\_0</span>.\
    <span class="comment">(\* Case "right". \*)</span> <span class="id"
type="tactic">apply</span> <span class="id" type="var">b\_3</span>.
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Let's take a look at the proof object for the above theorem.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">and\_example</span>.\
 <span
class="comment">(\* ===\>  conj (beautiful 0) (beautiful 3) b\_0 b\_3\
             : beautiful 0 /\\ beautiful 3 \*)</span>\
\

</div>

<div class="doc">

Note that the proof is of the form
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="var">conj</span> (<span class="id"
type="var">beautiful</span> 0) (<span class="id"
type="var">beautiful</span> 3) \
          (...<span class="id" type="var">pf</span> <span class="id"
type="var">of</span> <span class="id"
type="var">beautiful</span> 3...) (...<span class="id"
type="var">pf</span> <span class="id" type="var">of</span> <span
class="id" type="var">beautiful</span> 3...)
<div class="paragraph">

</div>

</div>

as you'd expect, given the type of <span class="inlinecode"><span
class="id" type="var">conj</span></span>.
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (case\_proof\_objects) {.section}

The <span class="inlinecode"><span class="id"
type="var">Case</span></span> tactics were commented out in the proof of
<span class="inlinecode"><span class="id"
type="var">and\_example</span></span> to avoid cluttering the proof
object. What would you guess the proof object will look like if we
uncomment them? Try it and see. ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">and\_commut</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> : <span class="id"
type="keyword">Prop</span>,\
   <span class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">HP</span> <span class="id" type="var">HQ</span>].\
   <span class="id" type="tactic">split</span>.\
     <span class="comment">(\* Case "left". \*)</span> <span class="id"
type="tactic">apply</span> <span class="id" type="var">HQ</span>.\
     <span class="comment">(\* Case "right". \*)</span> <span class="id"
type="tactic">apply</span> <span class="id" type="var">HP</span>. <span
class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Once again, we have commented out the <span class="inlinecode"><span
class="id" type="var">Case</span></span> tactics to make the proof
object for this theorem easier to understand. It is still a little
complicated, but after performing some simple reduction steps, we can
see that all that is really happening is taking apart a record
containing evidence for <span class="inlinecode"><span class="id"
type="var">P</span></span> and <span class="inlinecode"><span class="id"
type="var">Q</span></span> and rebuilding it in the opposite order:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">and\_commut</span>.\
 <span class="comment">(\* ===\>\
     and\_commut = \
       fun (P Q : Prop) (H : P /\\ Q) =\>\
         (fun H0 : Q /\\ P =\> H0)\
             match H with\

            | conj HP HQ =\> (fun (HP0 : P) (HQ0 : Q) =\> conj Q P HQ0 HP0) HP HQ\
             end\
       : forall P Q : Prop, P /\\ Q -\> Q /\\ P \*)</span>\
\

</div>

<div class="doc">

After simplifying some direct application of <span
class="inlinecode"><span class="id" type="keyword">fun</span></span>
expressions to arguments, we get:

</div>

<div class="code code-tight">

\
 <span class="comment">(\* ===\> \
    and\_commut = \
      fun (P Q : Prop) (H : P /\\ Q) =\>\
      match H with\
      | conj HP HQ =\> conj Q P HQ HP\
      end \
      : forall P Q : Prop, P /\\ Q -\> Q /\\ P \*)</span>\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (conj\_fact) {.section}

Construct a proof object demonstrating the following proposition.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">conj\_fact</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> <span class="id"
type="var">R</span>, <span class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">Q</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">R</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">P</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">R</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, advanced, optional (beautiful\_iff\_gorgeous) {.section}

<div class="paragraph">

</div>

We have seen that the families of propositions <span
class="inlinecode"><span class="id" type="var">beautiful</span></span>
and <span class="inlinecode"><span class="id"
type="var">gorgeous</span></span> actually characterize the same set of
numbers. Prove that <span class="inlinecode"><span class="id"
type="var">beautiful</span></span> <span class="inlinecode"><span
class="id" type="var">n</span></span> <span class="inlinecode"><span
style="font-family: arial;">↔</span></span> <span
class="inlinecode"><span class="id" type="var">gorgeous</span></span>
<span class="inlinecode"><span class="id" type="var">n</span></span> for
all <span class="inlinecode"><span class="id"
type="var">n</span></span>. Just for fun, write your proof as an
explicit proof object, rather than using tactics. (*Hint*: if you make
use of previously defined theorems, you should only need a single line!)

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">beautiful\_iff\_gorgeous</span> :\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">n</span>, <span class="id" type="var">beautiful</span> <span
class="id" type="var">n</span> <span
style="font-family: arial;">↔</span> <span class="id"
type="var">gorgeous</span> <span class="id" type="var">n</span> :=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (or\_commut'') {.section}

Try to write down an explicit proof object for <span
class="inlinecode"><span class="id" type="var">or\_commut</span></span>
(without using <span class="inlinecode"><span class="id"
type="keyword">Print</span></span> to peek at the ones we already
defined!).

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Recall that we model an existential for a property as a pair consisting
of a witness value and a proof that the witness obeys that property. We
can choose to construct the proof explicitly.
<div class="paragraph">

</div>

For example, consider this existentially quantified proposition:

</div>

<div class="code code-tight">

<span class="id" type="keyword">Check</span> <span class="id"
type="var">ex</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">some\_nat\_is\_even</span> : <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">ex</span> <span class="id"
type="var">\_</span> <span class="id" type="var">ev</span>.\
\

</div>

<div class="doc">

To prove this proposition, we need to choose a particular number as
witness — say, 4 — and give some evidence that that number is even.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">snie</span> : <span class="id"
type="var">some\_nat\_is\_even</span> :=\
   <span class="id" type="var">ex\_intro</span> <span class="id"
type="var">\_</span> <span class="id" type="var">ev</span> 4 (<span
class="id" type="var">ev\_SS</span> 2 (<span class="id"
type="var">ev\_SS</span> 0 <span class="id" type="var">ev\_0</span>)).\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (ex\_beautiful\_Sn) {.section}

Complete the definition of the following proof object:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">p</span> : <span class="id" type="var">ex</span> <span
class="id" type="var">\_</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">n</span> ⇒ <span
class="id" type="var">beautiful</span> (<span class="id"
type="var">S</span> <span class="id" type="var">n</span>)) :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Giving Explicit Arguments to Lemmas and Hypotheses {.section}
==================================================

<div class="paragraph">

</div>

Even when we are using tactic-based proof, it can be very useful to
understand the underlying functional nature of implications and
quantification.
<div class="paragraph">

</div>

For example, it is often convenient to <span class="inlinecode"><span
class="id" type="tactic">apply</span></span> or <span
class="inlinecode"><span class="id" type="tactic">rewrite</span></span>
using a lemma or hypothesis with one or more quantifiers or assumptions
already instantiated in order to direct what happens. For example:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Check</span> <span class="id"
type="var">plus\_comm</span>.\
 <span class="comment">(\* ==\> \
     plus\_comm\
      : forall n m : nat, n + m = m + n \*)</span>\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">plus\_comm\_r</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">a</span>
<span class="id" type="var">b</span> <span class="id"
type="var">c</span>, <span class="id" type="var">c</span> + (<span
class="id" type="var">b</span> + <span class="id" type="var">a</span>) =
<span class="id" type="var">c</span> + (<span class="id"
type="var">a</span> + <span class="id" type="var">b</span>).\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">intros</span> <span class="id"
type="var">a</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span>.\
    <span class="comment">(\* rewrite plus\_comm. \*)</span>\
       <span
class="comment">(\* rewrites in the first possible spot; not what we want \*)</span>\
    <span class="id" type="tactic">rewrite</span> (<span class="id"
type="var">plus\_comm</span> <span class="id" type="var">b</span> <span
class="id" type="var">a</span>). <span
class="comment">(\* directs rewriting to the right spot \*)</span>\
    <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

In this case, giving just one argument would be sufficient.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">plus\_comm\_r'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">a</span>
<span class="id" type="var">b</span> <span class="id"
type="var">c</span>, <span class="id" type="var">c</span> + (<span
class="id" type="var">b</span> + <span class="id" type="var">a</span>) =
<span class="id" type="var">c</span> + (<span class="id"
type="var">a</span> + <span class="id" type="var">b</span>).\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">intros</span> <span class="id"
type="var">a</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span>.\
    <span class="id" type="tactic">rewrite</span> (<span class="id"
type="var">plus\_comm</span> <span class="id" type="var">b</span>).\
    <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Arguments must be given in order, but wildcards (\_) may be used to skip
arguments that Coq can infer.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">plus\_comm\_r''</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">a</span>
<span class="id" type="var">b</span> <span class="id"
type="var">c</span>, <span class="id" type="var">c</span> + (<span
class="id" type="var">b</span> + <span class="id" type="var">a</span>) =
<span class="id" type="var">c</span> + (<span class="id"
type="var">a</span> + <span class="id" type="var">b</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">a</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span>.\
   <span class="id" type="tactic">rewrite</span> (<span class="id"
type="var">plus\_comm</span> <span class="id" type="var">\_</span> <span
class="id" type="var">a</span>).\
   <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The author of a lemma can choose to declare easily inferable arguments
to be implicit, just as with functions and constructors.
<div class="paragraph">

</div>

The <span class="inlinecode"><span class="id"
type="keyword">with</span></span> clauses we've already seen is really
just a way of specifying selected arguments by name rather than
position:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">plus\_comm\_r'''</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">a</span>
<span class="id" type="var">b</span> <span class="id"
type="var">c</span>, <span class="id" type="var">c</span> + (<span
class="id" type="var">b</span> + <span class="id" type="var">a</span>) =
<span class="id" type="var">c</span> + (<span class="id"
type="var">a</span> + <span class="id" type="var">b</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">a</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span>.\
   <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">plus\_comm</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">n</span> := <span class="id"
type="var">b</span>).\
   <span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 2 stars (trans\_eq\_example\_redux) {.section}

Redo the proof of the following theorem (from MoreCoq.v) using an <span
class="inlinecode"><span class="id" type="tactic">apply</span></span> of
<span class="inlinecode"><span class="id"
type="var">trans\_eq</span></span> but *not* using a <span
class="inlinecode"><span class="id" type="keyword">with</span></span>
clause.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">trans\_eq\_example'</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">a</span> <span class="id" type="var">b</span> <span
class="id" type="var">c</span> <span class="id" type="var">d</span>
<span class="id" type="var">e</span> <span class="id"
type="var">f</span> : <span class="id" type="var">nat</span>),\
      [<span class="id" type="var">a</span>;<span class="id"
type="var">b</span>] = [<span class="id" type="var">c</span>;<span
class="id" type="var">d</span>] <span
style="font-family: arial;">→</span>\
      [<span class="id" type="var">c</span>;<span class="id"
type="var">d</span>] = [<span class="id" type="var">e</span>;<span
class="id" type="var">f</span>] <span
style="font-family: arial;">→</span>\
      [<span class="id" type="var">a</span>;<span class="id"
type="var">b</span>] = [<span class="id" type="var">e</span>;<span
class="id" type="var">f</span>].\
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

Programming with Tactics (Advanced) {.section}
===================================

<div class="paragraph">

</div>

If we can build proofs with explicit terms rather than tactics, you may
be wondering if we can build programs using tactics rather than explicit
terms. Sure!

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">add1</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">nat</span>.\
 <span class="id" type="tactic">intro</span> <span class="id"
type="var">n</span>.\
 <span class="id" type="keyword">Show</span> <span class="id"
type="keyword">Proof</span>.\
 <span class="id" type="tactic">apply</span> <span class="id"
type="var">S</span>.\
 <span class="id" type="keyword">Show</span> <span class="id"
type="keyword">Proof</span>.\
 <span class="id" type="tactic">apply</span> <span class="id"
type="var">n</span>. <span class="id" type="keyword">Defined</span>.\
\
 <span class="id" type="keyword">Print</span> <span class="id"
type="var">add1</span>.\
 <span class="comment">(\* ==\>\
     add1 = fun n : nat =\> S n\
          : nat -\> nat\
 \*)</span>\
\
 <span class="id" type="keyword">Eval</span> <span class="id"
type="tactic">compute</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">add1</span> 2.\
 <span class="comment">(\* ==\> 3 : nat \*)</span>\
\

</div>

<div class="doc">

Notice that we terminate the <span class="inlinecode"><span class="id"
type="keyword">Definition</span></span> with a <span
class="inlinecode">.</span> rather than with <span
class="inlinecode">:=</span> followed by a term. This tells Coq to enter
proof scripting mode to build an object of type <span
class="inlinecode"><span class="id" type="var">nat</span></span> <span
class="inlinecode"><span style="font-family: arial;">→</span></span>
<span class="inlinecode"><span class="id" type="var">nat</span></span>.
Also, we terminate the proof with <span class="inlinecode"><span
class="id" type="keyword">Defined</span></span> rather than <span
class="inlinecode"><span class="id" type="keyword">Qed</span></span>;
this makes the definition *transparent* so that it can be used in
computation like a normally-defined function.
<div class="paragraph">

</div>

This feature is mainly useful for writing functions with dependent
types, which we won't explore much further in this book. But it does
illustrate the uniformity and orthogonality of the basic ideas in Coq.
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
