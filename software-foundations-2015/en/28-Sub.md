<div id="page">

<div id="header">

</div>

<div id="main">

Sub<span class="subtitle">Subtyping</span> {.libtitle}
==========================================

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

Concepts {.section}
========

<div class="paragraph">

</div>

We now turn to the study of *subtyping*, perhaps the most characteristic
feature of the static type systems of recently designed programming
languages and a key feature needed to support the object-oriented
programming style.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

A Motivating Example {.section}
--------------------

<div class="paragraph">

</div>

Suppose we are writing a program involving two record types defined as
follows:
        Person  = {name:String, age:Nat}
        Student = {name:String, age:Nat, gpa:Nat}

<div class="paragraph">

</div>

In the simply typed lamdba-calculus with records, the term
        (\r:Person. (r.age)+1) {name="Pat",age=21,gpa=1}

is not typable: it involves an application of a function that wants a
one-field record to an argument that actually provides two fields, while
the <span class="inlinecode"><span class="id"
type="var">T\_App</span></span> rule demands that the domain type of the
function being applied must match the type of the argument precisely.
<div class="paragraph">

</div>

But this is silly: we're passing the function a *better* argument than
it needs! The only thing the body of the function can possibly do with
its record argument <span class="inlinecode"><span class="id"
type="var">r</span></span> is project the field <span
class="inlinecode"><span class="id" type="var">age</span></span> from
it: nothing else is allowed by the type, and the presence or absence of
an extra <span class="inlinecode"><span class="id"
type="var">gpa</span></span> field makes no difference at all. So,
intuitively, it seems that this function should be applicable to any
record value that has at least an <span class="inlinecode"><span
class="id" type="var">age</span></span> field.
<div class="paragraph">

</div>

Looking at the same thing from another point of view, a record with more
fields is "at least as good in any context" as one with just a subset of
these fields, in the sense that any value belonging to the longer record
type can be used *safely* in any context expecting the shorter record
type. If the context expects something with the shorter type but we
actually give it something with the longer type, nothing bad will happen
(formally, the program will not get stuck).
<div class="paragraph">

</div>

The general principle at work here is called *subtyping*. We say that
"<span class="inlinecode"><span class="id" type="var">S</span></span> is
a subtype of <span class="inlinecode"><span class="id"
type="var">T</span></span>", informally written <span
class="inlinecode"><span class="id" type="var">S</span></span> <span
class="inlinecode">\<:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>, if a value of type <span
class="inlinecode"><span class="id" type="var">S</span></span> can
safely be used in any context where a value of type <span
class="inlinecode"><span class="id" type="var">T</span></span> is
expected. The idea of subtyping applies not only to records, but to all
of the type constructors in the language — functions, pairs, etc.
<div class="paragraph">

</div>

Subtyping and Object-Oriented Languages {.section}
---------------------------------------

<div class="paragraph">

</div>

Subtyping plays a fundamental role in many programming languages — in
particular, it is closely related to the notion of *subclassing* in
object-oriented languages.
<div class="paragraph">

</div>

An *object* in Java, C<span class="inlinecode">\#</span>, etc. can be
thought of as a record, some of whose fields are functions ("methods")
and some of whose fields are data values ("fields" or "instance
variables"). Invoking a method <span class="inlinecode"><span class="id"
type="var">m</span></span> of an object <span class="inlinecode"><span
class="id" type="var">o</span></span> on some arguments <span
class="inlinecode"><span class="id" type="var">a1</span>..<span
class="id" type="var">an</span></span> consists of projecting out the
<span class="inlinecode"><span class="id" type="var">m</span></span>
field of <span class="inlinecode"><span class="id"
type="var">o</span></span> and applying it to <span
class="inlinecode"><span class="id" type="var">a1</span>..<span
class="id" type="var">an</span></span>.
<div class="paragraph">

</div>

The type of an object can be given as either a *class* or an
*interface*. Both of these provide a description of which methods and
which data fields the object offers.
<div class="paragraph">

</div>

Classes and interfaces are related by the *subclass* and *subinterface*
relations. An object belonging to a subclass (or subinterface) is
required to provide all the methods and fields of one belonging to a
superclass (or superinterface), plus possibly some more.
<div class="paragraph">

</div>

The fact that an object from a subclass (or sub-interface) can be used
in place of one from a superclass (or super-interface) provides a degree
of flexibility that is is extremely handy for organizing complex
libraries. For example, a GUI toolkit like Java's Swing framework might
define an abstract interface <span class="inlinecode"><span class="id"
type="var">Component</span></span> that collects together the common
fields and methods of all objects having a graphical representation that
can be displayed on the screen and that can interact with the user.
Examples of such object would include the buttons, checkboxes, and
scrollbars of a typical GUI. A method that relies only on this common
interface can now be applied to any of these objects.
<div class="paragraph">

</div>

Of course, real object-oriented languages include many other features
besides these. For example, fields can be updated. Fields and methods
can be declared <span class="inlinecode"><span class="id"
type="var">private</span></span>. Classes also give *code* that is used
when constructing objects and implementing their methods, and the code
in subclasses cooperate with code in superclasses via *inheritance*.
Classes can have static methods and fields, initializers, etc., etc.
<div class="paragraph">

</div>

To keep things simple here, we won't deal with any of these issues — in
fact, we won't even talk any more about objects or classes. (There is a
lot of discussion in *Types and Programming Languages*, if you are
interested.) Instead, we'll study the core concepts behind the subclass
/ subinterface relation in the simplified setting of the STLC.
<div class="paragraph">

</div>

###  {.section}

Of course, real OO languages have lots of other features...
<div class="paragraph">

</div>

-   mutable fields
-   <span class="inlinecode"><span class="id"
    type="var">private</span></span> and other visibility modifiers
-   method inheritance
-   static components
-   etc., etc.

<div class="paragraph">

</div>

We'll ignore all these and focus on core mechanisms.
<div class="paragraph">

</div>

The Subsumption Rule {.section}
--------------------

<div class="paragraph">

</div>

Our goal for this chapter is to add subtyping to the simply typed
lambda-calculus (with some of the basic extensions from <span
class="inlinecode"><span class="id" type="var">MoreStlc</span></span>).
This involves two steps:
<div class="paragraph">

</div>

-   Defining a binary *subtype relation* between types.
    <div class="paragraph">

    </div>

-   Enriching the typing relation to take subtyping into account.

<div class="paragraph">

</div>

The second step is actually very simple. We add just a single rule to
the typing relation: the so-called *rule of subsumption*:
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t : S     S \<: T
(T\_Sub)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t : T
This rule says, intuitively, that it is OK to "forget" some of what we
know about a term. For example, we may know that <span
class="inlinecode"><span class="id" type="var">t</span></span> is a
record with two fields (e.g., <span class="inlinecode"><span class="id"
type="var">S</span></span> <span class="inlinecode">=</span> <span
class="inlinecode">{<span class="id" type="var">x</span>:<span
class="id" type="var">A</span><span
style="font-family: arial;">→</span><span class="id"
type="var">A</span>,</span> <span class="inlinecode"><span class="id"
type="var">y</span>:<span class="id" type="var">B</span><span
style="font-family: arial;">→</span><span class="id"
type="var">B</span>}</span>), but choose to forget about one of the
fields (<span class="inlinecode"><span class="id"
type="var">T</span></span> <span class="inlinecode">=</span> <span
class="inlinecode">{<span class="id" type="var">y</span>:<span
class="id" type="var">B</span><span
style="font-family: arial;">→</span><span class="id"
type="var">B</span>}</span>) so that we can pass <span
class="inlinecode"><span class="id" type="var">t</span></span> to a
function that requires just a single-field record.
<div class="paragraph">

</div>

The Subtype Relation {.section}
--------------------

<div class="paragraph">

</div>

The first step — the definition of the relation <span
class="inlinecode"><span class="id" type="var">S</span></span> <span
class="inlinecode">\<:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span> — is where all the action is. Let's look at
each of the clauses of its definition.
<div class="paragraph">

</div>

### Structural Rules {.section}

<div class="paragraph">

</div>

To start off, we impose two "structural rules" that are independent of
any particular type constructor: a rule of *transitivity*, which says
intuitively that, if <span class="inlinecode"><span class="id"
type="var">S</span></span> is better than <span class="inlinecode"><span
class="id" type="var">U</span></span> and <span class="inlinecode"><span
class="id" type="var">U</span></span> is better than <span
class="inlinecode"><span class="id" type="var">T</span></span>, then
<span class="inlinecode"><span class="id" type="var">S</span></span> is
better than <span class="inlinecode"><span class="id"
type="var">T</span></span>...
S \<: U    U \<: T
(S\_Trans)  

------------------------------------------------------------------------

S \<: T
... and a rule of *reflexivity*, since certainly any type <span
class="inlinecode"><span class="id" type="var">T</span></span> is as
good as itself:
  
(S\_Refl)  

------------------------------------------------------------------------

T \<: T
<div class="paragraph">

</div>

### Products {.section}

<div class="paragraph">

</div>

Now we consider the individual type constructors, one by one, beginning
with product types. We consider one pair to be "better than" another if
each of its components is.
S~1~ \<: T~1~    S~2~ \<: T~2~
(S\_Prod)  

------------------------------------------------------------------------

S~1~ × S~2~ \<: T~1~ × T~2~
<div class="paragraph">

</div>

### Arrows {.section}

<div class="paragraph">

</div>

Suppose we have two functions <span class="inlinecode"><span class="id"
type="var">f</span></span> and <span class="inlinecode"><span class="id"
type="var">g</span></span> with these types:
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="var">f</span> : <span class="id"
type="var">C</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Student</span> \
        <span class="id" type="var">g</span> : (<span class="id"
type="var">C</span><span style="font-family: arial;">→</span><span
class="id" type="var">Person</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">D</span>
<div class="paragraph">

</div>

</div>

That is, <span class="inlinecode"><span class="id"
type="var">f</span></span> is a function that yields a record of type
<span class="inlinecode"><span class="id"
type="var">Student</span></span>, and <span class="inlinecode"><span
class="id" type="var">g</span></span> is a (higher-order) function that
expects its (function) argument to yield a record of type <span
class="inlinecode"><span class="id" type="var">Person</span></span>.
Also suppose, even though we haven't yet discussed subtyping for
records, that <span class="inlinecode"><span class="id"
type="var">Student</span></span> is a subtype of <span
class="inlinecode"><span class="id" type="var">Person</span></span>.
Then the application <span class="inlinecode"><span class="id"
type="var">g</span></span> <span class="inlinecode"><span class="id"
type="var">f</span></span> is safe even though their types do not match
up precisely, because the only thing <span class="inlinecode"><span
class="id" type="var">g</span></span> can do with <span
class="inlinecode"><span class="id" type="var">f</span></span> is to
apply it to some argument (of type <span class="inlinecode"><span
class="id" type="var">C</span></span>); the result will actually be a
<span class="inlinecode"><span class="id"
type="var">Student</span></span>, while <span class="inlinecode"><span
class="id" type="var">g</span></span> will be expecting a <span
class="inlinecode"><span class="id" type="var">Person</span></span>, but
this is safe because the only thing <span class="inlinecode"><span
class="id" type="var">g</span></span> can then do is to project out the
two fields that it knows about (<span class="inlinecode"><span
class="id" type="var">name</span></span> and <span
class="inlinecode"><span class="id" type="var">age</span></span>), and
these will certainly be among the fields that are present.
<div class="paragraph">

</div>

This example suggests that the subtyping rule for arrow types should say
that two arrow types are in the subtype relation if their results are:
S~2~ \<: T~2~
(S\_Arrow\_Co)  

------------------------------------------------------------------------

S~1~ <span style="font-family: arial;">→</span> S~2~ \<: S~1~ <span
style="font-family: arial;">→</span> T~2~
We can generalize this to allow the arguments of the two arrow types to
be in the subtype relation as well:
T~1~ \<: S~1~    S~2~ \<: T~2~
(S\_Arrow)  

------------------------------------------------------------------------

S~1~ <span style="font-family: arial;">→</span> S~2~ \<: T~1~ <span
style="font-family: arial;">→</span> T~2~
Notice that the argument types are subtypes "the other way round": in
order to conclude that <span class="inlinecode"><span class="id"
type="var">S~1~</span><span style="font-family: arial;">→</span><span
class="id" type="var">S~2~</span></span> to be a subtype of <span
class="inlinecode"><span class="id" type="var">T~1~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T~2~</span></span>, it must be the case that <span
class="inlinecode"><span class="id" type="var">T~1~</span></span> is a
subtype of <span class="inlinecode"><span class="id"
type="var">S~1~</span></span>. The arrow constructor is said to be
*contravariant* in its first argument and *covariant* in its second.
<div class="paragraph">

</div>

Here is an example that illustrates this:
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="var">f</span> : <span class="id"
type="var">Person</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">C</span>\
        <span class="id" type="var">g</span> : (<span class="id"
type="var">Student</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">C</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">D</span>
<div class="paragraph">

</div>

</div>

The application <span class="inlinecode"><span class="id"
type="var">g</span></span> <span class="inlinecode"><span class="id"
type="var">f</span></span> is safe, because the only thing the body of
<span class="inlinecode"><span class="id" type="var">g</span></span> can
do with <span class="inlinecode"><span class="id"
type="var">f</span></span> is to apply it to some argument of type <span
class="inlinecode"><span class="id" type="var">Student</span></span>.
Since <span class="inlinecode"><span class="id"
type="var">f</span></span> requires records having (at least) the fields
of a <span class="inlinecode"><span class="id"
type="var">Person</span></span>, this will always work. So <span
class="inlinecode"><span class="id" type="var">Person</span></span>
<span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">C</span></span> is a
subtype of <span class="inlinecode"><span class="id"
type="var">Student</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">C</span></span> since
<span class="inlinecode"><span class="id"
type="var">Student</span></span> is a subtype of <span
class="inlinecode"><span class="id" type="var">Person</span></span>.
<div class="paragraph">

</div>

The intuition is that, if we have a function <span
class="inlinecode"><span class="id" type="var">f</span></span> of type
<span class="inlinecode"><span class="id" type="var">S~1~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">S~2~</span></span>, then we know that <span
class="inlinecode"><span class="id" type="var">f</span></span> accepts
elements of type <span class="inlinecode"><span class="id"
type="var">S~1~</span></span>; clearly, <span class="inlinecode"><span
class="id" type="var">f</span></span> will also accept elements of any
subtype <span class="inlinecode"><span class="id"
type="var">T~1~</span></span> of <span class="inlinecode"><span
class="id" type="var">S~1~</span></span>. The type of <span
class="inlinecode"><span class="id" type="var">f</span></span> also
tells us that it returns elements of type <span class="inlinecode"><span
class="id" type="var">S~2~</span></span>; we can also view these results
belonging to any supertype <span class="inlinecode"><span class="id"
type="var">T~2~</span></span> of <span class="inlinecode"><span
class="id" type="var">S~2~</span></span>. That is, any function <span
class="inlinecode"><span class="id" type="var">f</span></span> of type
<span class="inlinecode"><span class="id" type="var">S~1~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">S~2~</span></span> can also be viewed as having type <span
class="inlinecode"><span class="id" type="var">T~1~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T~2~</span></span>.
<div class="paragraph">

</div>

### Records {.section}

<div class="paragraph">

</div>

What about subtyping for record types?
<div class="paragraph">

</div>

The basic intuition about subtyping for record types is that it is
always safe to use a "bigger" record in place of a "smaller" one. That
is, given a record type, adding extra fields will always result in a
subtype. If some code is expecting a record with fields <span
class="inlinecode"><span class="id" type="var">x</span></span> and <span
class="inlinecode"><span class="id" type="var">y</span></span>, it is
perfectly safe for it to receive a record with fields <span
class="inlinecode"><span class="id" type="var">x</span></span>, <span
class="inlinecode"><span class="id" type="var">y</span></span>, and
<span class="inlinecode"><span class="id" type="var">z</span></span>;
the <span class="inlinecode"><span class="id" type="var">z</span></span>
field will simply be ignored. For example,
<div class="paragraph">

</div>

<div class="code code-tight">

       {<span class="id" type="var">name</span>:<span class="id"
type="var">String</span>, <span class="id" type="var">age</span>:<span
class="id" type="var">Nat</span>, <span class="id"
type="var">gpa</span>:<span class="id" type="var">Nat</span>} \<: {<span
class="id" type="var">name</span>:<span class="id"
type="var">String</span>, <span class="id" type="var">age</span>:<span
class="id" type="var">Nat</span>}\
        {<span class="id" type="var">name</span>:<span class="id"
type="var">String</span>, <span class="id" type="var">age</span>:<span
class="id" type="var">Nat</span>} \<: {<span class="id"
type="var">name</span>:<span class="id" type="var">String</span>}\
        {<span class="id" type="var">name</span>:<span class="id"
type="var">String</span>} \<: {}
<div class="paragraph">

</div>

</div>

This is known as "width subtyping" for records.
<div class="paragraph">

</div>

We can also create a subtype of a record type by replacing the type of
one of its fields with a subtype. If some code is expecting a record
with a field <span class="inlinecode"><span class="id"
type="var">x</span></span> of type <span class="inlinecode"><span
class="id" type="var">T</span></span>, it will be happy with a record
having a field <span class="inlinecode"><span class="id"
type="var">x</span></span> of type <span class="inlinecode"><span
class="id" type="var">S</span></span> as long as <span
class="inlinecode"><span class="id" type="var">S</span></span> is a
subtype of <span class="inlinecode"><span class="id"
type="var">T</span></span>. For example,
<div class="paragraph">

</div>

<div class="code code-tight">

       {<span class="id" type="var">x</span>:<span class="id"
type="var">Student</span>} \<: {<span class="id"
type="var">x</span>:<span class="id" type="var">Person</span>}
<div class="paragraph">

</div>

</div>

This is known as "depth subtyping".
<div class="paragraph">

</div>

Finally, although the fields of a record type are written in a
particular order, the order does not really matter. For example,
<div class="paragraph">

</div>

<div class="code code-tight">

       {<span class="id" type="var">name</span>:<span class="id"
type="var">String</span>,<span class="id" type="var">age</span>:<span
class="id" type="var">Nat</span>} \<: {<span class="id"
type="var">age</span>:<span class="id" type="var">Nat</span>,<span
class="id" type="var">name</span>:<span class="id"
type="var">String</span>}
<div class="paragraph">

</div>

</div>

This is known as "permutation subtyping".
<div class="paragraph">

</div>

We could formalize these requirements in a single subtyping rule for
records as follows:
for each jk in j1..jn,
<span style="font-family: arial;">∃</span>ip in i1..im, such that
jk=ip and Sp \<: Tk
(S\_Rcd)  

------------------------------------------------------------------------

{i1:S~1~...im:Sm} \<: {j1:T~1~...jn:Tn}
That is, the record on the left should have all the field labels of the
one on the right (and possibly more), while the types of the common
fields should be in the subtype relation. However, this rule is rather
heavy and hard to read. If we like, we can decompose it into three
simpler rules, which can be combined using <span
class="inlinecode"><span class="id" type="var">S\_Trans</span></span> to
achieve all the same effects.
<div class="paragraph">

</div>

First, adding fields to the end of a record type gives a subtype:
n \> m
(S\_RcdWidth)  

------------------------------------------------------------------------

{i1:T~1~...in:Tn} \<: {i1:T~1~...im:Tm}
We can use <span class="inlinecode"><span class="id"
type="var">S\_RcdWidth</span></span> to drop later fields of a
multi-field record while keeping earlier fields, showing for example
that <span class="inlinecode">{<span class="id"
type="var">age</span>:<span class="id" type="var">Nat</span>,<span
class="id" type="var">name</span>:<span class="id"
type="var">String</span>}</span> <span class="inlinecode">\<:</span>
<span class="inlinecode">{<span class="id" type="var">name</span>:<span
class="id" type="var">String</span>}</span>.
<div class="paragraph">

</div>

Second, we can apply subtyping inside the components of a compound
record type:
S~1~ \<: T~1~  ...  Sn \<: Tn
(S\_RcdDepth)  

------------------------------------------------------------------------

{i1:S~1~...in:Sn} \<: {i1:T~1~...in:Tn}
For example, we can use <span class="inlinecode"><span class="id"
type="var">S\_RcdDepth</span></span> and <span class="inlinecode"><span
class="id" type="var">S\_RcdWidth</span></span> together to show that
<span class="inlinecode">{<span class="id" type="var">y</span>:<span
class="id" type="var">Student</span>,</span> <span
class="inlinecode"><span class="id" type="var">x</span>:<span class="id"
type="var">Nat</span>}</span> <span class="inlinecode">\<:</span> <span
class="inlinecode">{<span class="id" type="var">y</span>:<span
class="id" type="var">Person</span>}</span>.
<div class="paragraph">

</div>

Third, we need to be able to reorder fields. For example, we might
expect that <span class="inlinecode">{<span class="id"
type="var">name</span>:<span class="id" type="var">String</span>,</span>
<span class="inlinecode"><span class="id" type="var">gpa</span>:<span
class="id" type="var">Nat</span>,</span> <span class="inlinecode"><span
class="id" type="var">age</span>:<span class="id"
type="var">Nat</span>}</span> <span class="inlinecode">\<:</span> <span
class="inlinecode"><span class="id" type="var">Person</span></span>. We
haven't quite achieved this yet: using just <span
class="inlinecode"><span class="id" type="var">S\_RcdDepth</span></span>
and <span class="inlinecode"><span class="id"
type="var">S\_RcdWidth</span></span> we can only drop fields from the
*end* of a record type. So we need:
{i1:S~1~...in:Sn} is a permutation of {i1:T~1~...in:Tn}
(S\_RcdPerm)  

------------------------------------------------------------------------

{i1:S~1~...in:Sn} \<: {i1:T~1~...in:Tn}
<div class="paragraph">

</div>

It is worth noting that full-blown language designs may choose not to
adopt all of these subtyping rules. For example, in Java:
<div class="paragraph">

</div>

-   A subclass may not change the argument or result types of a method
    of its superclass (i.e., no depth subtyping or no arrow subtyping,
    depending how you look at it).
    <div class="paragraph">

    </div>

-   Each class has just one superclass ("single inheritance" of
    classes).
    <div class="paragraph">

    </div>

-   Each class member (field or method) can be assigned a single index,
    adding new indices "on the right" as more members are added in
    subclasses (i.e., no permutation for classes).
    <div class="paragraph">

    </div>

-   A class may implement multiple interfaces — so-called "multiple
    inheritance" of interfaces (i.e., permutation is allowed for
    interfaces).

<div class="paragraph">

</div>

#### Exercise: 2 stars (arrow\_sub\_wrong) {.section}

Suppose we had incorrectly defined subtyping as covariant on both the
right and the left of arrow types:
S~1~ \<: T~1~    S~2~ \<: T~2~
(S\_Arrow\_wrong)  

------------------------------------------------------------------------

S~1~ <span style="font-family: arial;">→</span> S~2~ \<: T~1~ <span
style="font-family: arial;">→</span> T~2~
Give a concrete example of functions <span class="inlinecode"><span
class="id" type="var">f</span></span> and <span class="inlinecode"><span
class="id" type="var">g</span></span> with the following types...
<div class="paragraph">

</div>

<div class="code code-tight">

       <span class="id" type="var">f</span> : <span class="id"
type="var">Student</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Nat</span>\
        <span class="id" type="var">g</span> : (<span class="id"
type="var">Person</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Nat</span>) <span style="font-family: arial;">→</span> <span
class="id" type="var">Nat</span>
<div class="paragraph">

</div>

</div>

... such that the application <span class="inlinecode"><span class="id"
type="var">g</span></span> <span class="inlinecode"><span class="id"
type="var">f</span></span> will get stuck during execution.
<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

### Top {.section}

<div class="paragraph">

</div>

Finally, it is natural to give the subtype relation a maximal element —
a type that lies above every other type and is inhabited by all
(well-typed) values. We do this by adding to the language one new type
constant, called <span class="inlinecode"><span class="id"
type="var">Top</span></span>, together with a subtyping rule that places
it above every other type in the subtype relation:
  
(S\_Top)  

------------------------------------------------------------------------

S \<: Top
The <span class="inlinecode"><span class="id"
type="var">Top</span></span> type is an analog of the <span
class="inlinecode"><span class="id" type="var">Object</span></span> type
in Java and C<span class="inlinecode">\#</span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Summary {.section}

<div class="paragraph">

</div>

In summary, we form the STLC with subtyping by starting with the pure
STLC (over some set of base types) and...
<div class="paragraph">

</div>

-   adding a base type <span class="inlinecode"><span class="id"
    type="var">Top</span></span>,
    <div class="paragraph">

    </div>

-   adding the rule of subsumption
    <span style="font-family: serif; font-size:85%;">Γ</span> <span
    style="font-family: arial;">⊢</span> t : S     S \<: T
    (T\_Sub)  

    ------------------------------------------------------------------------

    <span style="font-family: serif; font-size:85%;">Γ</span> <span
    style="font-family: arial;">⊢</span> t : T
    to the typing relation, and
    <div class="paragraph">

    </div>

-   defining a subtype relation as follows:
    S \<: U    U \<: T
    (S\_Trans)  

    ------------------------------------------------------------------------

    S \<: T
      
    (S\_Refl)  

    ------------------------------------------------------------------------

    T \<: T
      
    (S\_Top)  

    ------------------------------------------------------------------------

    S \<: Top
    S~1~ \<: T~1~    S~2~ \<: T~2~
    (S\_Prod)  

    ------------------------------------------------------------------------

    S~1~ × S~2~ \<: T~1~ × T~2~
    T~1~ \<: S~1~    S~2~ \<: T~2~
    (S\_Arrow)  

    ------------------------------------------------------------------------

    S~1~ <span style="font-family: arial;">→</span> S~2~ \<: T~1~ <span
    style="font-family: arial;">→</span> T~2~
    n \> m
    (S\_RcdWidth)  

    ------------------------------------------------------------------------

    {i1:T~1~...in:Tn} \<: {i1:T~1~...im:Tm}
    S~1~ \<: T~1~  ...  Sn \<: Tn
    (S\_RcdDepth)  

    ------------------------------------------------------------------------

    {i1:S~1~...in:Sn} \<: {i1:T~1~...in:Tn}
    {i1:S~1~...in:Sn} is a permutation of {i1:T~1~...in:Tn}
    (S\_RcdPerm)  

    ------------------------------------------------------------------------

    {i1:S~1~...in:Sn} \<: {i1:T~1~...in:Tn}

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Exercises {.section}
---------

<div class="paragraph">

</div>

#### Exercise: 1 star, optional (subtype\_instances\_tf\_1) {.section}

Suppose we have types <span class="inlinecode"><span class="id"
type="var">S</span></span>, <span class="inlinecode"><span class="id"
type="var">T</span></span>, <span class="inlinecode"><span class="id"
type="var">U</span></span>, and <span class="inlinecode"><span
class="id" type="var">V</span></span> with <span
class="inlinecode"><span class="id" type="var">S</span></span> <span
class="inlinecode">\<:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span> and <span class="inlinecode"><span class="id"
type="var">U</span></span> <span class="inlinecode">\<:</span> <span
class="inlinecode"><span class="id" type="var">V</span></span>. Which of
the following subtyping assertions are then true? Write *true* or
*false* after each one. (<span class="inlinecode"><span class="id"
type="var">A</span></span>, <span class="inlinecode"><span class="id"
type="var">B</span></span>, and <span class="inlinecode"><span
class="id" type="var">C</span></span> here are base types.)
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id" type="var">T</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">S</span></span> <span class="inlinecode">\<:</span> <span
    class="inlinecode"><span class="id" type="var">T</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">S</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id" type="var">Top</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">U</span></span> <span class="inlinecode">\<:</span> <span
    class="inlinecode"><span class="id" type="var">S</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">Top</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">(<span class="id" type="var">C</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">C</span>)</span> <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode">(<span class="id" type="var">A</span>×<span
    class="id" type="var">B</span>)</span> <span
    class="inlinecode">\<:</span> <span class="inlinecode">(<span
    class="id" type="var">C</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">C</span>)</span> <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode">(<span class="id" type="var">Top</span>×<span
    class="id" type="var">B</span>)</span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id" type="var">T</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">T</span><span style="font-family: arial;">→</span><span
    class="id" type="var">U</span></span> <span
    class="inlinecode">\<:</span> <span class="inlinecode"><span
    class="id" type="var">S</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">S</span><span style="font-family: arial;">→</span><span
    class="id" type="var">V</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">(<span class="id" type="var">T</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">T</span>)<span style="font-family: arial;">→</span><span
    class="id" type="var">U</span></span> <span
    class="inlinecode">\<:</span> <span class="inlinecode">(<span
    class="id" type="var">S</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">S</span>)<span style="font-family: arial;">→</span><span
    class="id" type="var">V</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode">((<span class="id" type="var">T</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">S</span>)<span style="font-family: arial;">→</span><span
    class="id" type="var">T</span>)<span
    style="font-family: arial;">→</span><span class="id"
    type="var">U</span></span> <span class="inlinecode">\<:</span> <span
    class="inlinecode">((<span class="id" type="var">S</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">T</span>)<span style="font-family: arial;">→</span><span
    class="id" type="var">S</span>)<span
    style="font-family: arial;">→</span><span class="id"
    type="var">V</span></span>
    <div class="paragraph">

    </div>

-   <span class="inlinecode"><span class="id" type="var">S</span>×<span
    class="id" type="var">V</span></span> <span
    class="inlinecode">\<:</span> <span class="inlinecode"><span
    class="id" type="var">T</span>×<span class="id"
    type="var">U</span></span>

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (subtype\_order) {.section}

The following types happen to form a linear order with respect to
subtyping:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">Top</span></span>
-   <span class="inlinecode"><span class="id"
    type="var">Top</span></span> <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">Student</span></span>
-   <span class="inlinecode"><span class="id"
    type="var">Student</span></span> <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">Person</span></span>
-   <span class="inlinecode"><span class="id"
    type="var">Student</span></span> <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">Top</span></span>
-   <span class="inlinecode"><span class="id"
    type="var">Person</span></span> <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">Student</span></span>

<div class="paragraph">

</div>

Write these types in order from the most specific to the most general.
<div class="paragraph">

</div>

Where does the type <span class="inlinecode"><span class="id"
type="var">Top</span><span style="font-family: arial;">→</span><span
class="id" type="var">Top</span><span
style="font-family: arial;">→</span><span class="id"
type="var">Student</span></span> fit into this order?
<div class="paragraph">

</div>

<div class="paragraph">

</div>

#### Exercise: 1 star (subtype\_instances\_tf\_2) {.section}

Which of the following statements are true? Write *true* or *false*
after each one.
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="font-family: arial;">∀</span><span class="id"
type="var">S</span> <span class="id" type="var">T</span>,\
           <span class="id" type="var">S</span> \<: <span class="id"
type="var">T</span>  <span style="font-family: arial;">→</span>\
           <span class="id" type="var">S</span><span
style="font-family: arial;">→</span><span class="id"
type="var">S</span>   \<:  <span class="id" type="var">T</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T</span>\
\
       <span style="font-family: arial;">∀</span><span class="id"
type="var">S</span>,\
            <span class="id" type="var">S</span> \<: <span class="id"
type="var">A</span><span style="font-family: arial;">→</span><span
class="id" type="var">A</span> <span
style="font-family: arial;">→</span>\
            <span style="font-family: arial;">∃</span><span class="id"
type="var">T</span>,\
               <span class="id" type="var">S</span> = <span class="id"
type="var">T</span><span style="font-family: arial;">→</span><span
class="id" type="var">T</span>  <span
style="font-family: arial;">∧</span>  <span class="id"
type="var">T</span> \<: <span class="id" type="var">A</span>\
\
       <span style="font-family: arial;">∀</span><span class="id"
type="var">S</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
            (<span class="id" type="var">S</span> \<: <span class="id"
type="var">T~1~</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">T~2~</span>) <span
style="font-family: arial;">→</span>\
            <span style="font-family: arial;">∃</span><span class="id"
type="var">S~1~</span> <span class="id" type="var">S~2~</span>,\
               <span class="id" type="var">S</span> = <span class="id"
type="var">S~1~</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">S~2~</span>  <span
style="font-family: arial;">∧</span>  <span class="id"
type="var">T~1~</span> \<: <span class="id"
type="var">S~1~</span>  <span
style="font-family: arial;">∧</span>  <span class="id"
type="var">S~2~</span> \<: <span class="id" type="var">T~2~</span> \
\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">S</span>,\
            <span class="id" type="var">S</span> \<: <span class="id"
type="var">S</span><span style="font-family: arial;">→</span><span
class="id" type="var">S</span> \
\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">S</span>,\
            <span class="id" type="var">S</span><span
style="font-family: arial;">→</span><span class="id"
type="var">S</span> \<: <span class="id" type="var">S</span>   \
\
       <span style="font-family: arial;">∀</span><span class="id"
type="var">S</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
            <span class="id" type="var">S</span> \<: <span class="id"
type="var">T~1~</span>×<span class="id" type="var">T~2~</span> <span
style="font-family: arial;">→</span>\
            <span style="font-family: arial;">∃</span><span class="id"
type="var">S~1~</span> <span class="id" type="var">S~2~</span>,\
               <span class="id" type="var">S</span> = <span class="id"
type="var">S~1~</span>×<span class="id" type="var">S~2~</span>  <span
style="font-family: arial;">∧</span>  <span class="id"
type="var">S~1~</span> \<: <span class="id"
type="var">T~1~</span>  <span
style="font-family: arial;">∧</span>  <span class="id"
type="var">S~2~</span> \<: <span class="id" type="var">T~2~</span>  
<div class="paragraph">

</div>

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 1 star (subtype\_concepts\_tf) {.section}

Which of the following statements are true, and which are false?
<div class="paragraph">

</div>

-   There exists a type that is a supertype of every other type.
    <div class="paragraph">

    </div>

-   There exists a type that is a subtype of every other type.
    <div class="paragraph">

    </div>

-   There exists a pair type that is a supertype of every other pair
    type.
    <div class="paragraph">

    </div>

-   There exists a pair type that is a subtype of every other pair type.
    <div class="paragraph">

    </div>

-   There exists an arrow type that is a supertype of every other arrow
    type.
    <div class="paragraph">

    </div>

-   There exists an arrow type that is a subtype of every other arrow
    type.
    <div class="paragraph">

    </div>

-   There is an infinite descending chain of distinct types in the
    subtype relation—-that is, an infinite sequence of types <span
    class="inlinecode"><span class="id" type="var">S0</span></span>,
    <span class="inlinecode"><span class="id"
    type="var">S~1~</span></span>, etc., such that all the <span
    class="inlinecode"><span class="id" type="var">Si</span></span>'s
    are different and each <span class="inlinecode"><span class="id"
    type="var">S</span>(<span class="id" type="var">i</span>+1)</span>
    is a subtype of <span class="inlinecode"><span class="id"
    type="var">Si</span></span>.
    <div class="paragraph">

    </div>

-   There is an infinite *ascending* chain of distinct types in the
    subtype relation—-that is, an infinite sequence of types <span
    class="inlinecode"><span class="id" type="var">S0</span></span>,
    <span class="inlinecode"><span class="id"
    type="var">S~1~</span></span>, etc., such that all the <span
    class="inlinecode"><span class="id" type="var">Si</span></span>'s
    are different and each <span class="inlinecode"><span class="id"
    type="var">S</span>(<span class="id" type="var">i</span>+1)</span>
    is a supertype of <span class="inlinecode"><span class="id"
    type="var">Si</span></span>.

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (proper\_subtypes) {.section}

Is the following statement true or false? Briefly explain your answer.
<div class="paragraph">

</div>

<div class="code code-tight">

    <span style="font-family: arial;">∀</span><span class="id"
type="var">T</span>,\
          \~(<span style="font-family: arial;">∃</span><span class="id"
type="var">n</span>, <span class="id" type="var">T</span> = <span
class="id" type="var">TBase</span> <span class="id"
type="var">n</span>) <span style="font-family: arial;">→</span>\
          <span style="font-family: arial;">∃</span><span class="id"
type="var">S</span>,\
             <span class="id" type="var">S</span> \<: <span class="id"
type="var">T</span>  <span style="font-family: arial;">∧</span>  <span
class="id" type="var">S</span> ≠ <span class="id" type="var">T</span>
<div class="paragraph">

</div>

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (small\_large\_1) {.section}

<div class="paragraph">

</div>

-   What is the *smallest* type <span class="inlinecode"><span
    class="id" type="var">T</span></span> ("smallest" in the subtype
    relation) that makes the following assertion true? (Assume we have
    <span class="inlinecode"><span class="id"
    type="var">Unit</span></span> among the base types and <span
    class="inlinecode"><span class="id" type="var">unit</span></span> as
    a constant of this type.)
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">empty</span> <span
    style="font-family: arial;">⊢</span> (\\<span class="id"
    type="var">p</span>:<span class="id" type="var">T</span>×<span
    class="id" type="var">Top</span>. <span class="id"
    type="var">p.fst</span>) ((\\<span class="id"
    type="var">z</span>:<span class="id" type="var">A.z</span>), <span
    class="id" type="var">unit</span>) : <span class="id"
    type="var">A</span><span style="font-family: arial;">→</span><span
    class="id" type="var">A</span>
    <div class="paragraph">

    </div>

    </div>

    <div class="paragraph">

    </div>

-   What is the *largest* type <span class="inlinecode"><span class="id"
    type="var">T</span></span> that makes the same assertion true?

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (small\_large\_2) {.section}

<div class="paragraph">

</div>

-   What is the *smallest* type <span class="inlinecode"><span
    class="id" type="var">T</span></span> that makes the following
    assertion true?
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">empty</span> <span
    style="font-family: arial;">⊢</span> (\\<span class="id"
    type="var">p</span>:(<span class="id" type="var">A</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">A</span> × <span class="id" type="var">B</span><span
    style="font-family: arial;">→</span><span class="id"
    type="var">B</span>). <span class="id"
    type="var">p</span>) ((\\<span class="id" type="var">z</span>:<span
    class="id" type="var">A.z</span>), (\\<span class="id"
    type="var">z</span>:<span class="id" type="var">B.z</span>)) : <span
    class="id" type="var">T</span>
    <div class="paragraph">

    </div>

    </div>

    <div class="paragraph">

    </div>

-   What is the *largest* type <span class="inlinecode"><span class="id"
    type="var">T</span></span> that makes the same assertion true?

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (small\_large\_3) {.section}

<div class="paragraph">

</div>

-   What is the *smallest* type <span class="inlinecode"><span
    class="id" type="var">T</span></span> that makes the following
    assertion true?
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span class="id" type="var">a</span>:<span class="id"
    type="var">A</span> <span
    style="font-family: arial;">⊢</span> (\\<span class="id"
    type="var">p</span>:(<span class="id" type="var">A</span>×<span
    class="id" type="var">T</span>). (<span class="id"
    type="var">p.snd</span>) (<span class="id"
    type="var">p.fst</span>)) (<span class="id"
    type="var">a</span> , \\<span class="id" type="var">z</span>:<span
    class="id" type="var">A.z</span>) : <span class="id"
    type="var">A</span>
    <div class="paragraph">

    </div>

    </div>

    <div class="paragraph">

    </div>

-   What is the *largest* type <span class="inlinecode"><span class="id"
    type="var">T</span></span> that makes the same assertion true?

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (small\_large\_4) {.section}

<div class="paragraph">

</div>

-   What is the *smallest* type <span class="inlinecode"><span
    class="id" type="var">T</span></span> that makes the following
    assertion true?
    <div class="paragraph">

    </div>

    <div class="code code-tight">

      <span style="font-family: arial;">∃</span><span class="id"
    type="var">S</span>,\
         <span class="id" type="var">empty</span> <span
    style="font-family: arial;">⊢</span> (\\<span class="id"
    type="var">p</span>:(<span class="id" type="var">A</span>×<span
    class="id" type="var">T</span>). (<span class="id"
    type="var">p.snd</span>) (<span class="id"
    type="var">p.fst</span>)) : <span class="id" type="var">S</span>
    <div class="paragraph">

    </div>

    </div>

    <div class="paragraph">

    </div>

-   What is the *largest* type <span class="inlinecode"><span class="id"
    type="var">T</span></span> that makes the same assertion true?

<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (smallest\_1) {.section}

What is the *smallest* type <span class="inlinecode"><span class="id"
type="var">T</span></span> that makes the following assertion true?
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="font-family: arial;">∃</span><span class="id"
type="var">S</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">t</span>, \
         <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> (\\<span class="id"
type="var">x</span>:<span class="id" type="var">T</span>. <span
class="id" type="var">x</span> <span class="id"
type="var">x</span>) <span class="id" type="var">t</span> : <span
class="id" type="var">S</span>
<div class="paragraph">

</div>

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (smallest\_2) {.section}

What is the *smallest* type <span class="inlinecode"><span class="id"
type="var">T</span></span> that makes the following assertion true?
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> (\\<span class="id"
type="var">x</span>:<span class="id" type="var">Top</span>. <span
class="id" type="var">x</span>) ((\\<span class="id"
type="var">z</span>:<span class="id" type="var">A.z</span>) , (\\<span
class="id" type="var">z</span>:<span class="id"
type="var">B.z</span>)) : <span class="id" type="var">T</span>
<div class="paragraph">

</div>

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (count\_supertypes) {.section}

How many supertypes does the record type <span class="inlinecode">{<span
class="id" type="var">x</span>:<span class="id"
type="var">A</span>,</span> <span class="inlinecode"><span class="id"
type="var">y</span>:<span class="id" type="var">C</span><span
style="font-family: arial;">→</span><span class="id"
type="var">C</span>}</span> have? That is, how many different types
<span class="inlinecode"><span class="id" type="var">T</span></span> are
there such that <span class="inlinecode">{<span class="id"
type="var">x</span>:<span class="id" type="var">A</span>,</span> <span
class="inlinecode"><span class="id" type="var">y</span>:<span class="id"
type="var">C</span><span style="font-family: arial;">→</span><span
class="id" type="var">C</span>}</span> <span
class="inlinecode">\<:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>? (We consider two types to be different if
they are written differently, even if each is a subtype of the other.
For example, <span class="inlinecode">{<span class="id"
type="var">x</span>:<span class="id" type="var">A</span>,<span
class="id" type="var">y</span>:<span class="id"
type="var">B</span>}</span> and <span class="inlinecode">{<span
class="id" type="var">y</span>:<span class="id"
type="var">B</span>,<span class="id" type="var">x</span>:<span
class="id" type="var">A</span>}</span> are different.)
<div class="paragraph">

</div>

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars (pair\_permutation) {.section}

The subtyping rule for product types
S~1~ \<: T~1~    S~2~ \<: T~2~
(S\_Prod)  

------------------------------------------------------------------------

S~1~\*S~2~ \<: T~1~\*T~2~
intuitively corresponds to the "depth" subtyping rule for records.
Extending the analogy, we might consider adding a "permutation" rule
  
 

------------------------------------------------------------------------

T~1~\*T~2~ \<: T~2~\*T~1~
for products. Is this a good idea? Briefly explain why or why not.
<div class="paragraph">

</div>

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Formal Definitions {.section}
==================

<div class="paragraph">

</div>

Most of the definitions — in particular, the syntax and operational
semantics of the language — are identical to what we saw in the last
chapter. We just need to extend the typing relation with the subsumption
rule and add a new <span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> definition for the subtyping
relation. Let's first do the identical bits.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Core Definitions {.section}
----------------

</div>

<div class="code code-space">

\

</div>

<div class="doc">

### Syntax {.section}

<div class="paragraph">

</div>

For the sake of more interesting examples below, we'll allow an
arbitrary set of additional base types like <span
class="inlinecode"><span class="id" type="var">String</span></span>,
<span class="inlinecode"><span class="id"
type="var">Float</span></span>, etc. We won't bother adding any
constants belonging to these types or any operators on them, but we
could easily do so.
<div class="paragraph">

</div>

In the rest of the chapter, we formalize just base types, booleans,
arrow types, <span class="inlinecode"><span class="id"
type="var">Unit</span></span>, and <span class="inlinecode"><span
class="id" type="var">Top</span></span>, omitting record types and
leaving product types as an exercise.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ty</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">TTop</span> : <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TBool</span> : <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TBase</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span>\
   | <span class="id" type="var">TArrow</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TUnit</span> : <span class="id"
type="var">ty</span>\
 .\
\
 <span class="id" type="keyword">Tactic Notation</span> "T\_cases" <span
class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "TTop" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"TBool"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "TBase" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"TArrow"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "TUnit" |\
   ].\
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
class="id" type="var">tm</span>\
   | <span class="id" type="var">tunit</span> : <span class="id"
type="var">tm</span>\
 .\
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
"ttrue"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tfalse" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tif"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tunit"\
   ].\
\

</div>

<div class="doc">

### Substitution {.section}

<div class="paragraph">

</div>

The definition of substitution remains exactly the same as for the pure
STLC.

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
type="var">y</span> ⇒\
       <span class="id" type="keyword">if</span> <span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">s</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">t</span>\
   | <span class="id" type="var">tabs</span> <span class="id"
type="var">y</span> <span class="id" type="var">T</span> <span
class="id" type="var">t~1~</span> ⇒\
       <span class="id" type="var">tabs</span> <span class="id"
type="var">y</span> <span class="id" type="var">T</span> (<span
class="id" type="keyword">if</span> <span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">t~1~</span> <span
class="id" type="keyword">else</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id"
type="var">t~1~</span>))\
   | <span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒\
       <span class="id" type="var">tapp</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">ttrue</span> ⇒\
       <span class="id" type="var">ttrue</span>\
   | <span class="id" type="var">tfalse</span> ⇒\
       <span class="id" type="var">tfalse</span>\
   | <span class="id" type="var">tif</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> ⇒\
       <span class="id" type="var">tif</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>) (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~3~</span>)\
   | <span class="id" type="var">tunit</span> ⇒\
       <span class="id" type="var">tunit</span>\
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

### Reduction {.section}

<div class="paragraph">

</div>

Likewise the definitions of the <span class="inlinecode"><span
class="id" type="var">value</span></span> property and the <span
class="inlinecode"><span class="id" type="var">step</span></span>
relation.

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
type="var">tfalse</span>\
   | <span class="id" type="var">v\_unit</span> :\
       <span class="id" type="var">value</span> <span class="id"
type="var">tunit</span>\
 .\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">value</span>.\
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
          (<span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">ST\_App2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~2~'</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
          <span class="id" type="var">t~2~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~2~'</span> <span style="font-family: arial;">→</span>\
          (<span class="id" type="var">tapp</span> <span class="id"
type="var">v~1~</span> <span class="id" type="var">t~2~</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">t~2~'</span>)\
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
"ST\_If"\
   ].\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id" type="var">step</span>.\
\

</div>

<div class="doc">

Subtyping {.section}
---------

<div class="paragraph">

</div>

Now we come to the most interesting part. We begin by defining the
subtyping relation and developing some of its important technical
properties.
<div class="paragraph">

</div>

The definition of subtyping is just what we sketched in the motivating
discussion.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Reserved Notation</span> "T '\<:' U"
(<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 40).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">subtype</span> : <span class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">S\_Refl</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T</span>,\
       <span class="id" type="var">T</span> \<: <span class="id"
type="var">T</span>\
   | <span class="id" type="var">S\_Trans</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">S</span>
<span class="id" type="var">U</span> <span class="id"
type="var">T</span>,\
       <span class="id" type="var">S</span> \<: <span class="id"
type="var">U</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">U</span> \<: <span class="id"
type="var">T</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">S</span> \<: <span class="id"
type="var">T</span>\
   | <span class="id" type="var">S\_Top</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">S</span>,\
       <span class="id" type="var">S</span> \<: <span class="id"
type="var">TTop</span>\
   | <span class="id" type="var">S\_Arrow</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">S~1~</span> <span class="id" type="var">S~2~</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>,\
       <span class="id" type="var">T~1~</span> \<: <span class="id"
type="var">S~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">S~2~</span> \<: <span class="id"
type="var">T~2~</span> <span style="font-family: arial;">→</span>\
       (<span class="id" type="var">TArrow</span> <span class="id"
type="var">S~1~</span> <span class="id" type="var">S~2~</span>) \<:
(<span class="id" type="var">TArrow</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span>)\
 <span class="id" type="keyword">where</span> "T '\<:' U" := (<span
class="id" type="var">subtype</span> <span class="id"
type="var">T</span> <span class="id" type="var">U</span>).\
\

</div>

<div class="doc">

Note that we don't need any special rules for base types: they are
automatically subtypes of themselves (by <span class="inlinecode"><span
class="id" type="var">S\_Refl</span></span>) and <span
class="inlinecode"><span class="id" type="var">Top</span></span> (by
<span class="inlinecode"><span class="id"
type="var">S\_Top</span></span>), and that's all we want.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">subtype</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span> "subtype\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "S\_Refl" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"S\_Trans"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "S\_Top" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"S\_Arrow"\
   ].\
\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Examples</span>.\
\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">x</span> := (<span class="id" type="var">Id</span> 0).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">y</span> := (<span class="id" type="var">Id</span> 1).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">z</span> := (<span class="id" type="var">Id</span> 2).\
\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">A</span> := (<span class="id" type="var">TBase</span> (<span
class="id" type="var">Id</span> 6)).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">B</span> := (<span class="id" type="var">TBase</span> (<span
class="id" type="var">Id</span> 7)).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">C</span> := (<span class="id" type="var">TBase</span> (<span
class="id" type="var">Id</span> 8)).\
\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">String</span> := (<span class="id" type="var">TBase</span>
(<span class="id" type="var">Id</span> 9)).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">Float</span> := (<span class="id" type="var">TBase</span>
(<span class="id" type="var">Id</span> 10)).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">Integer</span> := (<span class="id" type="var">TBase</span>
(<span class="id" type="var">Id</span> 11)).\
\

</div>

<div class="doc">

#### Exercise: 2 stars, optional (subtyping\_judgements) {.section}

<div class="paragraph">

</div>

(Do this exercise after you have added product types to the language, at
least up to this point in the file).
<div class="paragraph">

</div>

Using the encoding of records into pairs, define pair types representing
the record types
<div class="paragraph">

</div>

<div class="code code-tight">

    <span class="id" type="var">Person</span>   := { <span class="id"
type="var">name</span> : <span class="id" type="var">String</span> }\
     <span class="id" type="var">Student</span>  := { <span class="id"
type="var">name</span> : <span class="id" type="var">String</span> ; \
                   <span class="id" type="var">gpa</span>  : <span
class="id" type="var">Float</span> }\
     <span class="id" type="var">Employee</span> := { <span class="id"
type="var">name</span> : <span class="id" type="var">String</span> ;\
                   <span class="id" type="var">ssn</span>  : <span
class="id" type="var">Integer</span> }
<div class="paragraph">

</div>

</div>

<div class="paragraph">

</div>

Recall that in chapter MoreStlc, the optional subsection "Encoding
Records" describes how records can be encoded as pairs.
<div class="paragraph">

</div>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">Person</span> : <span class="id" type="var">ty</span> :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">Student</span> : <span class="id" type="var">ty</span> :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">Employee</span> : <span class="id" type="var">ty</span> :=\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">sub\_student\_person</span> :\
   <span class="id" type="var">Student</span> \<: <span class="id"
type="var">Person</span>.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">sub\_employee\_person</span> :\
   <span class="id" type="var">Employee</span> \<: <span class="id"
type="var">Person</span>.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">subtyping\_example\_0</span> :\
   (<span class="id" type="var">TArrow</span> <span class="id"
type="var">C</span> <span class="id" type="var">Person</span>) \<:
(<span class="id" type="var">TArrow</span> <span class="id"
type="var">C</span> <span class="id" type="var">TTop</span>).\
   <span class="comment">(\* C-\>Person \<: C-\>Top \*)</span>\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">S\_Arrow</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">S\_Refl</span>. <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The following facts are mostly easy to prove in Coq. To get full benefit
from the exercises, make sure you also understand how to prove them on
paper!
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (subtyping\_example\_1) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">subtyping\_example\_1</span> :\
   (<span class="id" type="var">TArrow</span> <span class="id"
type="var">TTop</span> <span class="id" type="var">Student</span>) \<:
(<span class="id" type="var">TArrow</span> (<span class="id"
type="var">TArrow</span> <span class="id" type="var">C</span> <span
class="id" type="var">C</span>) <span class="id"
type="var">Person</span>).\
   <span
class="comment">(\* Top-\>Student \<: (C-\>C)-\>Person \*)</span>\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (subtyping\_example\_2) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">subtyping\_example\_2</span> :\
   (<span class="id" type="var">TArrow</span> <span class="id"
type="var">TTop</span> <span class="id" type="var">Person</span>) \<:
(<span class="id" type="var">TArrow</span> <span class="id"
type="var">Person</span> <span class="id" type="var">TTop</span>).\
   <span class="comment">(\* Top-\>Person \<: Person-\>Top \*)</span>\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Examples</span>.\
\

</div>

<div class="doc">

Typing {.section}
------

<div class="paragraph">

</div>

The only change to the typing relation is the addition of the rule of
subsumption, <span class="inlinecode"><span class="id"
type="var">T\_Sub</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">context</span> := <span class="id" type="var">id</span> <span
style="font-family: arial;">→</span> (<span class="id"
type="var">option</span> <span class="id" type="var">ty</span>).\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">empty</span> : <span class="id" type="var">context</span> :=
(<span class="id" type="keyword">fun</span> <span class="id"
type="var">\_</span> ⇒ <span class="id" type="var">None</span>).\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">extend</span> (<span
style="font-family: serif; font-size:85%;">Γ</span> : <span class="id"
type="var">context</span>) (<span class="id" type="var">x</span>:<span
class="id" type="var">id</span>) (<span class="id" type="var">T</span> :
<span class="id" type="var">ty</span>) :=\
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
   <span class="comment">(\* Same as before \*)</span>\
   | <span class="id" type="var">T\_Var</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
class="id" type="var">x</span> = <span class="id" type="var">Some</span>
<span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) ∈ <span
class="id" type="var">T</span>\
   | <span class="id" type="var">T\_Abs</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T~11~</span> <span
class="id" type="var">T~12~</span> <span class="id"
type="var">t~12~</span>,\
       (<span class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T~11~</span>) <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~12~</span> ∈ <span class="id" type="var">T~12~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
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
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ (<span class="id" type="var">TArrow</span>
<span class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) ∈ <span class="id"
type="var">T~2~</span>\
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
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tif</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>) ∈ <span class="id" type="var">T</span>\
   | <span class="id" type="var">T\_Unit</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tunit</span> ∈ <span class="id" type="var">TUnit</span>\
   <span class="comment">(\* New rule of subsumption \*)</span>\
   | <span class="id" type="var">T\_Sub</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">S</span> <span
class="id" type="var">T</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">S</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">S</span> \<: <span class="id"
type="var">T</span> <span style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span>\
\
 <span class="id" type="keyword">where</span> "Gamma '<span
style="font-family: arial;">⊢</span>' t '∈' T" := (<span class="id"
type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span>).\
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
"T\_Abs"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_App" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_True"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_False" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_If"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Unit"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Sub" ].\
\
 <span
class="comment">(\* To make your job simpler, the following hints help construct typing\
    derivations. \*)</span>\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Extern</span> 2 (<span class="id"
type="var">has\_type</span> <span class="id" type="var">\_</span> (<span
class="id" type="var">tapp</span> <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span>) <span class="id"
type="var">\_</span>) ⇒\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_App</span>; <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="keyword">Extern</span> 2 (<span class="id" type="var">\_</span> =
<span class="id" type="var">\_</span>) ⇒ <span class="id"
type="tactic">compute</span>; <span class="id"
type="tactic">reflexivity</span>.\
\

</div>

<div class="doc">

Typing examples {.section}
---------------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">Examples2</span>.\
 <span class="id" type="keyword">Import</span> <span class="id"
type="var">Examples</span>.\
\

</div>

<div class="doc">

Do the following exercises after you have added product types to the
language. For each informal typing judgement, write it as a formal
statement in Coq and prove it.
<div class="paragraph">

</div>

#### Exercise: 1 star, optional (typing\_example\_0) {.section}

</div>

<div class="code code-space">

<span class="comment">(\* empty |- ((\\z:A.z), (\\z:B.z)) \
           : (A-\>A \* B-\>B) \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (typing\_example\_1) {.section}

</div>

<div class="code code-space">

<span
class="comment">(\* empty |- (\\x:(Top \* B-\>B). x.snd) ((\\z:A.z), (\\z:B.z)) \
           : B-\>B \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (typing\_example\_2) {.section}

</div>

<div class="code code-space">

<span
class="comment">(\* empty |- (\\z:(C-\>C)-\>(Top \* B-\>B). (z (\\x:C.x)).snd)\
               (\\z:C-\>C. ((\\z:A.z), (\\z:B.z)))\
           : B-\>B \*)</span>\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Examples2</span>.\
\

</div>

<div class="doc">

Properties {.section}
==========

<div class="paragraph">

</div>

The fundamental properties of the system that we want to check are the
same as always: progress and preservation. Unlike the extension of the
STLC with references, we don't need to change the *statements* of these
properties to take subtyping into account. However, their proofs do
become a little bit more involved.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Inversion Lemmas for Subtyping {.section}
------------------------------

<div class="paragraph">

</div>

Before we look at the properties of the typing relation, we need to
record a couple of critical structural properties of the subtype
relation:
<div class="paragraph">

</div>

-   <span class="inlinecode"><span class="id"
    type="var">Bool</span></span> is the only subtype of <span
    class="inlinecode"><span class="id" type="var">Bool</span></span>
-   every subtype of an arrow type is itself an arrow type.

<div class="paragraph">

</div>

These are called *inversion lemmas* because they play the same role in
later proofs as the built-in <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> tactic: given a hypothesis that
there exists a derivation of some subtyping statement <span
class="inlinecode"><span class="id" type="var">S</span></span> <span
class="inlinecode">\<:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span> and some constraints on the shape of <span
class="inlinecode"><span class="id" type="var">S</span></span> and/or
<span class="inlinecode"><span class="id" type="var">T</span></span>,
each one reasons about what this derivation must look like to tell us
something further about the shapes of <span class="inlinecode"><span
class="id" type="var">S</span></span> and <span class="inlinecode"><span
class="id" type="var">T</span></span> and the existence of subtype
relations between their parts.
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (sub\_inversion\_Bool) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">sub\_inversion\_Bool</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">U</span>,\
      <span class="id" type="var">U</span> \<: <span class="id"
type="var">TBool</span> <span style="font-family: arial;">→</span>\
        <span class="id" type="var">U</span> = <span class="id"
type="var">TBool</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">U</span> <span class="id" type="var">Hs</span>.\
   <span class="id" type="var">remember</span> <span class="id"
type="var">TBool</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">V</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars, optional (sub\_inversion\_arrow) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">sub\_inversion\_arrow</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">U</span>
<span class="id" type="var">V1</span> <span class="id"
type="var">V2</span>,\
      <span class="id" type="var">U</span> \<: (<span class="id"
type="var">TArrow</span> <span class="id" type="var">V1</span> <span
class="id" type="var">V2</span>) <span
style="font-family: arial;">→</span>\
      <span style="font-family: arial;">∃</span><span class="id"
type="var">U1</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">U2</span>,\
        <span class="id" type="var">U</span> = (<span class="id"
type="var">TArrow</span> <span class="id" type="var">U1</span> <span
class="id" type="var">U2</span>) <span
style="font-family: arial;">∧</span> (<span class="id"
type="var">V1</span> \<: <span class="id" type="var">U1</span>) <span
style="font-family: arial;">∧</span> (<span class="id"
type="var">U2</span> \<: <span class="id" type="var">V2</span>).\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">U</span> <span class="id" type="var">V1</span> <span
class="id" type="var">V2</span> <span class="id" type="var">Hs</span>.\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">TArrow</span> <span class="id" type="var">V1</span> <span
class="id" type="var">V2</span>) <span class="id"
type="keyword">as</span> <span class="id" type="var">V</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">V2</span>.
<span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">V1</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Canonical Forms {.section}
---------------

<div class="paragraph">

</div>

We'll see first that the proof of the progress theorem doesn't change
too much — we just need one small refinement. When we're considering the
case where the term in question is an application <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> <span
class="inlinecode"><span class="id" type="var">t~2~</span></span> where
both <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> and <span class="inlinecode"><span
class="id" type="var">t~2~</span></span> are values, we need to know
that <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> has the *form* of a lambda-abstraction, so
that we can apply the <span class="inlinecode"><span class="id"
type="var">ST\_AppAbs</span></span> reduction rule. In the ordinary
STLC, this is obvious: we know that <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> has a function type <span
class="inlinecode"><span class="id" type="var">T~11~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T~12~</span></span>, and there is only one rule that can be
used to give a function type to a value — rule <span
class="inlinecode"><span class="id" type="var">T\_Abs</span></span> —
and the form of the conclusion of this rule forces <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> to be
an abstraction.
<div class="paragraph">

</div>

In the STLC with subtyping, this reasoning doesn't quite work because
there's another rule that can be used to show that a value has a
function type: subsumption. Fortunately, this possibility doesn't change
things much: if the last rule used to show <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t~1~</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T~11~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T~12~</span></span> is subsumption, then there is some
*sub*-derivation whose subject is also <span class="inlinecode"><span
class="id" type="var">t~1~</span></span>, and we can reason by induction
until we finally bottom out at a use of <span class="inlinecode"><span
class="id" type="var">T\_Abs</span></span>.
<div class="paragraph">

</div>

This bit of reasoning is packaged up in the following lemma, which tells
us the possible "canonical forms" (i.e. values) of function type.
<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (canonical\_forms\_of\_arrow\_types) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">canonical\_forms\_of\_arrow\_types</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">s</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
   <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">s</span> ∈ (<span class="id" type="var">TArrow</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
   <span class="id" type="var">value</span> <span class="id"
type="var">s</span> <span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">x</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">S~1~</span>, <span
style="font-family: arial;">∃</span><span class="id"
type="var">s~2~</span>,\
      <span class="id" type="var">s</span> = <span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">S~1~</span> <span class="id"
type="var">s~2~</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Similarly, the canonical forms of type <span class="inlinecode"><span
class="id" type="var">Bool</span></span> are the constants <span
class="inlinecode"><span class="id" type="var">true</span></span> and
<span class="inlinecode"><span class="id"
type="var">false</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">canonical\_forms\_of\_Bool</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">s</span>,\
   <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">s</span> ∈ <span class="id" type="var">TBool</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">value</span> <span class="id"
type="var">s</span> <span style="font-family: arial;">→</span>\
   (<span class="id" type="var">s</span> = <span class="id"
type="var">ttrue</span> <span style="font-family: arial;">∨</span> <span
class="id" type="var">s</span> = <span class="id"
type="var">tfalse</span>).\
<div id="proofcontrol1" class="togglescript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')">

<span class="show"></span>

</div>

<div id="proof1" class="proofscript"
onclick="toggleDisplay('proof1');toggleDisplay('proofcontrol1')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">s</span> <span class="id" type="var">Hty</span> <span
class="id" type="var">Hv</span>.\
   <span class="id" type="var">remember</span> <span class="id"
type="var">TBool</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">T</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Hty</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">inversion</span>...\
   <span class="id" type="var">Case</span> "T\_Sub".\
     <span class="id" type="tactic">subst</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">sub\_inversion\_Bool</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">subst</span>...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Progress {.section}
--------

<div class="paragraph">

</div>

The proof of progress proceeds like the one for the pure STLC, except
that in several places we invoke canonical forms lemmas...
<div class="paragraph">

</div>

*Theorem* (Progress): For any term <span class="inlinecode"><span
class="id" type="var">t</span></span> and type <span
class="inlinecode"><span class="id" type="var">T</span></span>, if <span
class="inlinecode"><span class="id" type="var">empty</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T</span></span> then <span
class="inlinecode"><span class="id" type="var">t</span></span> is a
value or <span class="inlinecode"><span class="id"
type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> for some
term <span class="inlinecode"><span class="id"
type="var">t'</span></span>.
<div class="paragraph">

</div>

*Proof*: Let <span class="inlinecode"><span class="id"
type="var">t</span></span> and <span class="inlinecode"><span class="id"
type="var">T</span></span> be given, with <span class="inlinecode"><span
class="id" type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>. Proceed by induction on the typing
derivation.
<div class="paragraph">

</div>

The cases for <span class="inlinecode"><span class="id"
type="var">T\_Abs</span></span>, <span class="inlinecode"><span
class="id" type="var">T\_Unit</span></span>, <span
class="inlinecode"><span class="id" type="var">T\_True</span></span> and
<span class="inlinecode"><span class="id"
type="var">T\_False</span></span> are immediate because abstractions,
<span class="inlinecode"><span class="id" type="var">unit</span></span>,
<span class="inlinecode"><span class="id" type="var">true</span></span>,
and <span class="inlinecode"><span class="id"
type="var">false</span></span> are already values. The <span
class="inlinecode"><span class="id" type="var">T\_Var</span></span> case
is vacuous because variables cannot be typed in the empty context. The
remaining cases are more interesting:
<div class="paragraph">

</div>

-   If the last step in the typing derivation uses rule <span
    class="inlinecode"><span class="id" type="var">T\_App</span></span>,
    then there are terms <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> and types <span
    class="inlinecode"><span class="id" type="var">T~1~</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">T~2~</span></span> such that <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">t~1~</span></span> <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span>,
    <span class="inlinecode"><span class="id" type="var">T</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">T~2~</span></span>, <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">T~1~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">→</span></span>
    <span class="inlinecode"><span class="id"
    type="var">T~2~</span></span>, and <span class="inlinecode"><span
    class="id" type="var">empty</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> <span class="inlinecode">:</span>
    <span class="inlinecode"><span class="id"
    type="var">T~1~</span></span>. Moreover, by the induction
    hypothesis, either <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> is a value or it steps, and either
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> is a value or it steps. There are
    three possibilities to consider:
    <div class="paragraph">

    </div>

    -   Suppose <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode"><span
        style="font-family: arial;">⇒</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span> for some term <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span>. Then <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span> <span
        class="inlinecode"><span
        style="font-family: arial;">⇒</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span> <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span> by <span
        class="inlinecode"><span class="id"
        type="var">ST\_App1</span></span>.
        <div class="paragraph">

        </div>

    -   Suppose <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> is a value and <span
        class="inlinecode"><span class="id"
        type="var">t~2~</span></span> <span class="inlinecode"><span
        style="font-family: arial;">⇒</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~2~'</span></span> for some term <span
        class="inlinecode"><span class="id"
        type="var">t~2~'</span></span>. Then <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span> <span
        class="inlinecode"><span
        style="font-family: arial;">⇒</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode"><span
        class="id" type="var">t~2~'</span></span> by rule <span
        class="inlinecode"><span class="id"
        type="var">ST\_App2</span></span> because <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> is a value.
        <div class="paragraph">

        </div>

    -   Finally, suppose <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> and <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span> are both values. By
        Lemma <span class="inlinecode"><span class="id"
        type="var">canonical\_forms\_for\_arrow\_types</span></span>, we
        know that <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> has the form <span
        class="inlinecode">\\<span class="id" type="var">x</span>:<span
        class="id" type="var">S~1~.s~2~</span></span> for some <span
        class="inlinecode"><span class="id" type="var">x</span></span>,
        <span class="inlinecode"><span class="id"
        type="var">S~1~</span></span>, and <span
        class="inlinecode"><span class="id"
        type="var">s~2~</span></span>. But then <span
        class="inlinecode">(\\<span class="id" type="var">x</span>:<span
        class="id" type="var">S~1~.s~2~</span>)</span> <span
        class="inlinecode"><span class="id"
        type="var">t~2~</span></span> <span class="inlinecode"><span
        style="font-family: arial;">⇒</span></span> <span
        class="inlinecode">[<span class="id" type="var">x</span>:=<span
        class="id" type="var">t~2~</span>]<span class="id"
        type="var">s~2~</span></span> by <span class="inlinecode"><span
        class="id" type="var">ST\_AppAbs</span></span>, since <span
        class="inlinecode"><span class="id"
        type="var">t~2~</span></span> is a value.
        <div class="paragraph">

        </div>
-   If the final step of the derivation uses rule <span
    class="inlinecode"><span class="id" type="var">T\_If</span></span>,
    then there are terms <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span>, <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span>, and <span
    class="inlinecode"><span class="id" type="var">t~3~</span></span>
    such that <span class="inlinecode"><span class="id"
    type="var">t</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="keyword">if</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="keyword">then</span></span> <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span>
    <span class="inlinecode"><span class="id"
    type="keyword">else</span></span> <span class="inlinecode"><span
    class="id" type="var">t~3~</span></span>, with <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">Bool</span></span> and with <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span> and <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~3~</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span>. Moreover, by the induction
    hypothesis, either <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> is a value or it steps.
    <div class="paragraph">

    </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> is a value, then by the canonical
        forms lemma for booleans, either <span class="inlinecode"><span
        class="id" type="var">t~1~</span></span> <span
        class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="var">true</span></span> or <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode">=</span>
        <span class="inlinecode"><span class="id"
        type="var">false</span></span>. In either case, <span
        class="inlinecode"><span class="id" type="var">t</span></span>
        can step, using rule <span class="inlinecode"><span class="id"
        type="var">ST\_IfTrue</span></span> or <span
        class="inlinecode"><span class="id"
        type="var">ST\_IfFalse</span></span>.
        <div class="paragraph">

        </div>

    -   If <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> can step, then so can <span
        class="inlinecode"><span class="id" type="var">t</span></span>,
        by rule <span class="inlinecode"><span class="id"
        type="var">ST\_If</span></span>.
        <div class="paragraph">

        </div>
-   If the final step of the derivation is by <span
    class="inlinecode"><span class="id" type="var">T\_Sub</span></span>,
    then there is a type <span class="inlinecode"><span class="id"
    type="var">S</span></span> such that <span class="inlinecode"><span
    class="id" type="var">S</span></span> <span
    class="inlinecode">\<:</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span> and <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">S</span></span>. The desired result is exactly
    the induction hypothesis for the typing subderivation.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="tactic">progress</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">T</span>,\
      <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">∨</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>, <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span>.\
<div id="proofcontrol2" class="togglescript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')">

<span class="show"></span>

</div>

<div id="proof2" class="proofscript"
onclick="toggleDisplay('proof2');toggleDisplay('proofcontrol2')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
class="id" type="var">Ht</span>.\
   <span class="id" type="var">remember</span> <span class="id"
type="var">empty</span> <span class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="var">revert</span> <span class="id"
type="var">HeqGamma</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Ht</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">HeqGamma</span>; <span class="id"
type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "T\_Var".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="var">right</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span>; <span class="id" type="tactic">subst</span>...\
       <span class="id" type="var">SSCase</span> "t~2~ is a value".\
         <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">canonical\_forms\_of\_arrow\_types</span> <span
class="id" type="var">empty</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>)\
           <span class="id" type="keyword">as</span> [<span class="id"
type="var">x</span> [<span class="id" type="var">S~1~</span> [<span
class="id" type="var">t~12~</span> <span class="id"
type="var">Heqt1</span>]]]...\
         <span class="id" type="tactic">subst</span>. <span
style="font-family: arial;">∃</span>([<span class="id"
type="var">x</span>:=<span class="id" type="var">t~2~</span>]<span
class="id" type="var">t~12~</span>)...\
       <span class="id" type="var">SSCase</span> "t~2~ steps".\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">H0</span> <span class="id"
type="keyword">as</span> [<span class="id" type="var">t~2~'</span> <span
class="id" type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~'</span>)...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)...\
   <span class="id" type="var">Case</span> "T\_If".\
     <span class="id" type="var">right</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>.\
     <span class="id" type="var">SCase</span> "t~1~ is a value"...\
       <span class="id" type="tactic">assert</span> (<span class="id"
type="var">t~1~</span> = <span class="id" type="var">ttrue</span> <span
style="font-family: arial;">∨</span> <span class="id"
type="var">t~1~</span> = <span class="id" type="var">tfalse</span>)\
         <span class="id" type="tactic">by</span> (<span class="id"
type="tactic">eapply</span> <span class="id"
type="var">canonical\_forms\_of\_Bool</span>; <span class="id"
type="tactic">eauto</span>).\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span>; <span class="id" type="tactic">subst</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">rename</span> <span
class="id" type="var">x</span> <span class="id" type="var">into</span>
<span class="id" type="var">t~1~'</span>. <span class="id"
type="tactic">eauto</span>.\
\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Inversion Lemmas for Typing {.section}
---------------------------

<div class="paragraph">

</div>

The proof of the preservation theorem also becomes a little more complex
with the addition of subtyping. The reason is that, as with the
"inversion lemmas for subtyping" above, there are a number of facts
about the typing relation that are "obvious from the definition" in the
pure STLC (and hence can be obtained directly from the <span
class="inlinecode"><span class="id"
type="tactic">inversion</span></span> tactic) but that require real
proofs in the presence of subtyping because there are multiple ways to
derive the same <span class="inlinecode"><span class="id"
type="var">has\_type</span></span> statement.
<div class="paragraph">

</div>

The following "inversion lemma" tells us that, if we have a derivation
of some typing statement <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">\\<span class="id" type="var">x</span>:<span
class="id" type="var">S~1~.t~2~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span> whose subject is an abstraction, then there
must be some subderivation giving a type to the body <span
class="inlinecode"><span class="id" type="var">t~2~</span></span>.
<div class="paragraph">

</div>

*Lemma*: If <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">\\<span class="id" type="var">x</span>:<span
class="id" type="var">S~1~.t~2~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>, then there is a type <span
class="inlinecode"><span class="id" type="var">S~2~</span></span> such
that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,</span> <span
class="inlinecode"><span class="id" type="var">x</span>:<span class="id"
type="var">S~1~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t~2~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">S~2~</span></span> and <span class="inlinecode"><span
class="id" type="var">S~1~</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">S~2~</span></span> <span
class="inlinecode">\<:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>.
<div class="paragraph">

</div>

(Notice that the lemma does *not* say, "then <span
class="inlinecode"><span class="id" type="var">T</span></span> itself is
an arrow type" — this is tempting, but false!)
<div class="paragraph">

</div>

*Proof*: Let <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span>, <span
class="inlinecode"><span class="id" type="var">x</span></span>, <span
class="inlinecode"><span class="id" type="var">S~1~</span></span>, <span
class="inlinecode"><span class="id" type="var">t~2~</span></span> and
<span class="inlinecode"><span class="id" type="var">T</span></span> be
given as described. Proceed by induction on the derivation of <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">\\<span class="id" type="var">x</span>:<span
class="id" type="var">S~1~.t~2~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>. Cases <span class="inlinecode"><span
class="id" type="var">T\_Var</span></span>, <span
class="inlinecode"><span class="id" type="var">T\_App</span></span>, are
vacuous as those rules cannot be used to give a type to a syntactic
abstraction.
<div class="paragraph">

</div>

-   If the last step of the derivation is a use of <span
    class="inlinecode"><span class="id" type="var">T\_Abs</span></span>
    then there is a type <span class="inlinecode"><span class="id"
    type="var">T~12~</span></span> such that <span
    class="inlinecode"><span class="id" type="var">T</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">S~1~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">→</span></span>
    <span class="inlinecode"><span class="id"
    type="var">T~12~</span></span> and <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span>,</span> <span
    class="inlinecode"><span class="id" type="var">x</span>:<span
    class="id" type="var">S~1~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> <span class="inlinecode">:</span>
    <span class="inlinecode"><span class="id"
    type="var">T~12~</span></span>. Picking <span
    class="inlinecode"><span class="id" type="var">T~12~</span></span>
    for <span class="inlinecode"><span class="id"
    type="var">S~2~</span></span> gives us what we need: <span
    class="inlinecode"><span class="id" type="var">S~1~</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">→</span></span> <span
    class="inlinecode"><span class="id" type="var">T~12~</span></span>
    <span class="inlinecode">\<:</span> <span class="inlinecode"><span
    class="id" type="var">S~1~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">→</span></span>
    <span class="inlinecode"><span class="id"
    type="var">T~12~</span></span> follows from <span
    class="inlinecode"><span class="id"
    type="var">S\_Refl</span></span>.
    <div class="paragraph">

    </div>

-   If the last step of the derivation is a use of <span
    class="inlinecode"><span class="id" type="var">T\_Sub</span></span>
    then there is a type <span class="inlinecode"><span class="id"
    type="var">S</span></span> such that <span class="inlinecode"><span
    class="id" type="var">S</span></span> <span
    class="inlinecode">\<:</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span> and <span
    class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode">\\<span class="id"
    type="var">x</span>:<span class="id"
    type="var">S~1~.t~2~</span></span> <span class="inlinecode">:</span>
    <span class="inlinecode"><span class="id"
    type="var">S</span></span>. The IH for the typing subderivation tell
    us that there is some type <span class="inlinecode"><span class="id"
    type="var">S~2~</span></span> with <span class="inlinecode"><span
    class="id" type="var">S~1~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">→</span></span>
    <span class="inlinecode"><span class="id"
    type="var">S~2~</span></span> <span class="inlinecode">\<:</span>
    <span class="inlinecode"><span class="id" type="var">S</span></span>
    and <span class="inlinecode"><span
    style="font-family: serif; font-size:85%;">Γ</span>,</span> <span
    class="inlinecode"><span class="id" type="var">x</span>:<span
    class="id" type="var">S~1~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> <span class="inlinecode">:</span>
    <span class="inlinecode"><span class="id"
    type="var">S~2~</span></span>. Picking type <span
    class="inlinecode"><span class="id" type="var">S~2~</span></span>
    gives us what we need, since <span class="inlinecode"><span
    class="id" type="var">S~1~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">→</span></span>
    <span class="inlinecode"><span class="id"
    type="var">S~2~</span></span> <span class="inlinecode">\<:</span>
    <span class="inlinecode"><span class="id" type="var">T</span></span>
    then follows by <span class="inlinecode"><span class="id"
    type="var">S\_Trans</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_inversion\_abs</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">S~1~</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">T</span>,\
      <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">S~1~</span> <span class="id"
type="var">t~2~</span>) ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
      (<span style="font-family: arial;">∃</span><span class="id"
type="var">S~2~</span>, (<span class="id" type="var">TArrow</span> <span
class="id" type="var">S~1~</span> <span class="id"
type="var">S~2~</span>) \<: <span class="id" type="var">T</span>\
               <span style="font-family: arial;">∧</span> (<span
class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">S~1~</span>) <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">S~2~</span>).\
<div id="proofcontrol3" class="togglescript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')">

<span class="show"></span>

</div>

<div id="proof3" class="proofscript"
onclick="toggleDisplay('proof3');toggleDisplay('proofcontrol3')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">S~1~</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">T</span>
<span class="id" type="var">H</span>.\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">S~1~</span> <span class="id"
type="var">t~2~</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">t</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heqt</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">intros</span>; <span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">T~12~</span>...\
   <span class="id" type="var">Case</span> "T\_Sub".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHhas\_type</span> <span class="id" type="keyword">as</span>
[<span class="id" type="var">S~2~</span> [<span class="id"
type="var">Hsub</span> <span class="id" type="var">Hty</span>]]...\
   <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Similarly...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_inversion\_var</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T</span>,\
   <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) ∈ <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">S</span>,\
     <span style="font-family: serif; font-size:85%;">Γ</span> <span
class="id" type="var">x</span> = <span class="id" type="var">Some</span>
<span class="id" type="var">S</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">S</span> \<: <span class="id" type="var">T</span>.\
<div id="proofcontrol4" class="togglescript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')">

<span class="show"></span>

</div>

<div id="proof4" class="proofscript"
onclick="toggleDisplay('proof4');toggleDisplay('proofcontrol4')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T</span> <span
class="id" type="var">Hty</span>.\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">t</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Hty</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span>;\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heqt</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
   <span class="id" type="var">Case</span> "T\_Var".\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">T</span>...\
   <span class="id" type="var">Case</span> "T\_Sub".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHty</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">U</span> [<span class="id" type="var">Hctx</span>
<span class="id" type="var">HsubU</span>]]... <span class="id"
type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_inversion\_app</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">T~2~</span>,\
   <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) ∈ <span class="id"
type="var">T~2~</span> <span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">T~1~</span>,\
     <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ (<span class="id" type="var">TArrow</span>
<span class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">∧</span>\
     <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T~1~</span>.\
<div id="proofcontrol5" class="togglescript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')">

<span class="show"></span>

</div>

<div id="proof5" class="proofscript"
onclick="toggleDisplay('proof5');toggleDisplay('proofcontrol5')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">T~2~</span> <span class="id"
type="var">Hty</span>.\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) <span class="id"
type="keyword">as</span> <span class="id" type="var">t</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Hty</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span>;\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heqt</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
   <span class="id" type="var">Case</span> "T\_App".\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">T~1~</span>...\
   <span class="id" type="var">Case</span> "T\_Sub".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHty</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">U1</span> [<span class="id" type="var">Hty1</span>
<span class="id" type="var">Hty2</span>]]...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_inversion\_true</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">T</span>,\
   <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">ttrue</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">TBool</span> \<: <span class="id"
type="var">T</span>.\
<div id="proofcontrol6" class="togglescript"
onclick="toggleDisplay('proof6');toggleDisplay('proofcontrol6')">

<span class="show"></span>

</div>

<div id="proof6" class="proofscript"
onclick="toggleDisplay('proof6');toggleDisplay('proofcontrol6')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">T</span> <span class="id" type="var">Htyp</span>. <span
class="id" type="var">remember</span> <span class="id"
type="var">ttrue</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">tu</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Htyp</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heqtu</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">intros</span>...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_inversion\_false</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">T</span>,\
   <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tfalse</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">TBool</span> \<: <span class="id"
type="var">T</span>.\
<div id="proofcontrol7" class="togglescript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')">

<span class="show"></span>

</div>

<div id="proof7" class="proofscript"
onclick="toggleDisplay('proof7');toggleDisplay('proofcontrol7')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">T</span> <span class="id" type="var">Htyp</span>. <span
class="id" type="var">remember</span> <span class="id"
type="var">tfalse</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">tu</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Htyp</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heqtu</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">intros</span>...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_inversion\_if</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> <span class="id" type="var">T</span>,\
   <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tif</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>) ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TBool</span>\
   <span style="font-family: arial;">∧</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">T</span>\
   <span style="font-family: arial;">∧</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~3~</span> ∈ <span class="id" type="var">T</span>.\
<div id="proofcontrol8" class="togglescript"
onclick="toggleDisplay('proof8');toggleDisplay('proofcontrol8')">

<span class="show"></span>

</div>

<div id="proof8" class="proofscript"
onclick="toggleDisplay('proof8');toggleDisplay('proofcontrol8')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">t~3~</span> <span class="id" type="var">T</span>
<span class="id" type="var">Hty</span>.\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">tif</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">t~3~</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">t</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Hty</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span>;\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heqt</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
   <span class="id" type="var">Case</span> "T\_If".\
     <span class="id" type="tactic">auto</span>.\
   <span class="id" type="var">Case</span> "T\_Sub".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHHty</span> <span class="id" type="var">H0</span>) <span
class="id" type="keyword">as</span> [<span class="id"
type="var">H1</span> [<span class="id" type="var">H2</span> <span
class="id" type="var">H3</span>]]...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_inversion\_unit</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">T</span>,\
   <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tunit</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">TUnit</span> \<: <span class="id"
type="var">T</span>.\
<div id="proofcontrol9" class="togglescript"
onclick="toggleDisplay('proof9');toggleDisplay('proofcontrol9')">

<span class="show"></span>

</div>

<div id="proof9" class="proofscript"
onclick="toggleDisplay('proof9');toggleDisplay('proofcontrol9')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">T</span> <span class="id" type="var">Htyp</span>. <span
class="id" type="var">remember</span> <span class="id"
type="var">tunit</span> <span class="id" type="keyword">as</span> <span
class="id" type="var">tu</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Htyp</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heqtu</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">intros</span>...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

The inversion lemmas for typing and for subtyping between arrow types
can be packaged up as a useful "combination lemma" telling us exactly
what we'll actually require below.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">abs\_arrow</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">S~1~</span> <span class="id"
type="var">s~2~</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
   <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">S~1~</span> <span class="id"
type="var">s~2~</span>) ∈ (<span class="id" type="var">TArrow</span>
<span class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
      <span class="id" type="var">T~1~</span> \<: <span class="id"
type="var">S~1~</span>\
   <span style="font-family: arial;">∧</span> (<span class="id"
type="var">extend</span> <span class="id" type="var">empty</span> <span
class="id" type="var">x</span> <span class="id" type="var">S~1~</span>)
<span style="font-family: arial;">⊢</span> <span class="id"
type="var">s~2~</span> ∈ <span class="id" type="var">T~2~</span>.\
<div id="proofcontrol10" class="togglescript"
onclick="toggleDisplay('proof10');toggleDisplay('proofcontrol10')">

<span class="show"></span>

</div>

<div id="proof10" class="proofscript"
onclick="toggleDisplay('proof10');toggleDisplay('proofcontrol10')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">S~1~</span> <span
class="id" type="var">s~2~</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> <span
class="id" type="var">Hty</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">typing\_inversion\_abs</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hty</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hty</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">S~2~</span> [<span class="id"
type="var">Hsub</span> <span class="id" type="var">Hty1</span>]].\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">sub\_inversion\_arrow</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hsub</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hsub</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">U1</span> [<span class="id" type="var">U2</span>
[<span class="id" type="var">Heq</span> [<span class="id"
type="var">Hsub1</span> <span class="id" type="var">Hsub2</span>]]]].\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heq</span>; <span class="id" type="tactic">subst</span>...
<span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Context Invariance {.section}
------------------

<div class="paragraph">

</div>

The context invariance lemma follows the same pattern as in the pure
STLC.

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
   | <span class="id" type="var">afi\_if1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~1~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>)\
   | <span class="id" type="var">afi\_if2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~2~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>)\
   | <span class="id" type="var">afi\_if3</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t~3~</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tif</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">t~3~</span>)\
 .\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">appears\_free\_in</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">context\_invariance</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: serif; font-size:85%;">Γ'</span> <span class="id"
type="var">t</span> <span class="id" type="var">S</span>,\
      <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">S</span> <span
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
      <span style="font-family: serif; font-size:85%;">Γ'</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">S</span>.\
<div id="proofcontrol11" class="togglescript"
onclick="toggleDisplay('proof11');toggleDisplay('proofcontrol11')">

<span class="show"></span>

</div>

<div id="proof11" class="proofscript"
onclick="toggleDisplay('proof11');toggleDisplay('proofcontrol11')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ'</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ'</span> <span class="id"
type="var">Heqv</span>...\
   <span class="id" type="var">Case</span> "T\_Var".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Var</span>... <span class="id"
type="tactic">rewrite</span> <span style="font-family: arial;">←</span>
<span class="id" type="var">Heqv</span>...\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>... <span class="id" type="tactic">apply</span>
<span class="id" type="var">IHhas\_type</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">x0</span> <span
class="id" type="var">Hafi</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>. <span class="id" type="tactic">destruct</span>
(<span class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">x0</span>)...\
   <span class="id" type="var">Case</span> "T\_If".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_If</span>...\
\
 <span class="id" type="keyword">Qed</span>.\

</div>

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">free\_in\_context</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t</span> <span class="id"
type="var">T</span> <span
style="font-family: serif; font-size:85%;">Γ</span>,\
    <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
    <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
    <span style="font-family: arial;">∃</span><span class="id"
type="var">T'</span>, <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> = <span class="id" type="var">Some</span> <span
class="id" type="var">T'</span>.\
<div id="proofcontrol12" class="togglescript"
onclick="toggleDisplay('proof12');toggleDisplay('proofcontrol12')">

<span class="show"></span>

</div>

<div id="proof12" class="proofscript"
onclick="toggleDisplay('proof12');toggleDisplay('proofcontrol12')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">Hafi</span> <span class="id" type="var">Htyp</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Htyp</span>)
<span class="id" type="var">Case</span>;\
       <span class="id" type="tactic">subst</span>; <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hafi</span>;
<span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHHtyp</span> <span class="id" type="var">H4</span>) <span
class="id" type="keyword">as</span> [<span class="id"
type="var">T</span> <span class="id" type="var">Hctx</span>]. <span
style="font-family: arial;">∃</span><span class="id"
type="var">T</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hctx</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">neq\_id</span>
<span class="id" type="keyword">in</span> <span class="id"
type="var">Hctx</span>... <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Substitution {.section}
------------

<div class="paragraph">

</div>

The *substitution lemma* is proved along the same lines as for the pure
STLC. The only significant change is that there are several places
where, instead of the built-in <span class="inlinecode"><span class="id"
type="tactic">inversion</span></span> tactic, we need to use the
inversion lemmas that we proved above to extract structural information
from assumptions about the well-typedness of subterms.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">substitution\_preserves\_typing</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span> <span
class="id" type="var">v</span> <span class="id" type="var">t</span>
<span class="id" type="var">S</span>,\
      (<span class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span>) <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">S</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">v</span> ∈ <span class="id" type="var">U</span> <span
style="font-family: arial;">→</span>\
      <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> ([<span class="id"
type="var">x</span>:=<span class="id" type="var">v</span>]<span
class="id" type="var">t</span>) ∈ <span class="id" type="var">S</span>.\
<div id="proofcontrol13" class="togglescript"
onclick="toggleDisplay('proof13');toggleDisplay('proofcontrol13')">

<span class="show"></span>

</div>

<div id="proof13" class="proofscript"
onclick="toggleDisplay('proof13');toggleDisplay('proofcontrol13')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span> <span
class="id" type="var">v</span> <span class="id" type="var">t</span>
<span class="id" type="var">S</span> <span class="id"
type="var">Htypt</span> <span class="id" type="var">Htypv</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">S</span>.
<span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="var">t\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">t</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span>; <span class="id"
type="tactic">simpl</span>.\
   <span class="id" type="var">Case</span> "tvar".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">typing\_inversion\_var</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id"
type="var">Htypt</span>)\
         <span class="id" type="keyword">as</span> [<span class="id"
type="var">T</span> [<span class="id" type="var">Hctx</span> <span
class="id" type="var">Hsub</span>]].\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hctx</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>)...\
     <span class="id" type="var">SCase</span> "x=y".\
       <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hctx</span>; <span class="id" type="tactic">subst</span>.
<span class="id" type="tactic">clear</span> <span class="id"
type="var">Hctx</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">context\_invariance</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">empty</span>...\
       <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">Hcontra</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">free\_in\_context</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">S</span> <span class="id" type="var">empty</span>
<span class="id" type="var">Hcontra</span>)\
           <span class="id" type="keyword">as</span> [<span class="id"
type="var">T'</span> <span class="id" type="var">HT'</span>]...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT'</span>.\
   <span class="id" type="var">Case</span> "tapp".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">typing\_inversion\_app</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>
<span class="id" type="var">Htypt</span>)\
         <span class="id" type="keyword">as</span> [<span class="id"
type="var">T~1~</span> [<span class="id" type="var">Htypt1</span> <span
class="id" type="var">Htypt2</span>]].\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">T\_App</span>...\
   <span class="id" type="var">Case</span> "tabs".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y</span>. <span class="id"
type="tactic">rename</span> <span class="id" type="var">t</span> <span
class="id" type="var">into</span> <span class="id"
type="var">T~1~</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">typing\_inversion\_abs</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span> <span class="id"
type="var">Htypt</span>)\
       <span class="id" type="keyword">as</span> [<span class="id"
type="var">T~2~</span> [<span class="id" type="var">Hsub</span> <span
class="id" type="var">Htypt2</span>]].\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Sub</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">TArrow</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span>)... <span
class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>...\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>).\
     <span class="id" type="var">SCase</span> "x=y".\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>...\
       <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">Hafi</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">y</span> <span
class="id" type="var">x</span>)...\
     <span class="id" type="var">SCase</span> "x≠y".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHt</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">context\_invariance</span>...\
       <span class="id" type="tactic">intros</span> <span class="id"
type="var">z</span> <span class="id" type="var">Hafi</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span>)...\
       <span class="id" type="tactic">subst</span>. <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>...\
   <span class="id" type="var">Case</span> "ttrue".\
       <span class="id" type="tactic">assert</span> (<span class="id"
type="var">TBool</span> \<: <span class="id" type="var">S</span>)\
         <span class="id" type="tactic">by</span> <span class="id"
type="tactic">apply</span> (<span class="id"
type="var">typing\_inversion\_true</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">Htypt</span>)...\
   <span class="id" type="var">Case</span> "tfalse".\
       <span class="id" type="tactic">assert</span> (<span class="id"
type="var">TBool</span> \<: <span class="id" type="var">S</span>)\
         <span class="id" type="tactic">by</span> <span class="id"
type="tactic">apply</span> (<span class="id"
type="var">typing\_inversion\_false</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">Htypt</span>)...\
   <span class="id" type="var">Case</span> "tif".\
     <span class="id" type="tactic">assert</span> ((<span class="id"
type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span>) <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~1~</span> ∈ <span class="id" type="var">TBool</span>\
             <span style="font-family: arial;">∧</span> (<span
class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span>) <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~2~</span> ∈ <span class="id" type="var">S</span>\
             <span style="font-family: arial;">∧</span> (<span
class="id" type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span>) <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t~3~</span> ∈ <span class="id" type="var">S</span>)\
       <span class="id" type="tactic">by</span> <span class="id"
type="tactic">apply</span> (<span class="id"
type="var">typing\_inversion\_if</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span> <span class="id"
type="var">Htypt</span>).\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">H1</span> [<span class="id" type="var">H2</span>
<span class="id" type="var">H3</span>]].\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHt1</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H1</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHt2</span> <span
class="id" type="keyword">in</span> <span class="id"
type="var">H2</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">IHt3</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H3</span>.\
     <span class="id" type="tactic">auto</span>.\
   <span class="id" type="var">Case</span> "tunit".\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">TUnit</span> \<: <span class="id" type="var">S</span>)\
       <span class="id" type="tactic">by</span> <span class="id"
type="tactic">apply</span> (<span class="id"
type="var">typing\_inversion\_unit</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">Htypt</span>)...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Preservation {.section}
------------

<div class="paragraph">

</div>

The proof of preservation now proceeds pretty much as in earlier
chapters, using the substitution lemma at the appropriate point and
again using inversion lemmas from above to extract structural
information from typing assumptions.
<div class="paragraph">

</div>

*Theorem* (Preservation): If <span class="inlinecode"><span class="id"
type="var">t</span></span>, <span class="inlinecode"><span class="id"
type="var">t'</span></span> are terms and <span class="inlinecode"><span
class="id" type="var">T</span></span> is a type such that <span
class="inlinecode"><span class="id" type="var">empty</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T</span></span> and <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span>, then
<span class="inlinecode"><span class="id" type="var">empty</span></span>
<span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>.
<div class="paragraph">

</div>

*Proof*: Let <span class="inlinecode"><span class="id"
type="var">t</span></span> and <span class="inlinecode"><span class="id"
type="var">T</span></span> be given such that <span
class="inlinecode"><span class="id" type="var">empty</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>. We proceed by induction on the
structure of this typing derivation, leaving <span
class="inlinecode"><span class="id" type="var">t'</span></span> general.
The cases <span class="inlinecode"><span class="id"
type="var">T\_Abs</span></span>, <span class="inlinecode"><span
class="id" type="var">T\_Unit</span></span>, <span
class="inlinecode"><span class="id" type="var">T\_True</span></span>,
and <span class="inlinecode"><span class="id"
type="var">T\_False</span></span> cases are vacuous because abstractions
and constants don't step. Case <span class="inlinecode"><span class="id"
type="var">T\_Var</span></span> is vacuous as well, since the context is
empty.
<div class="paragraph">

</div>

-   If the final step of the derivation is by <span
    class="inlinecode"><span class="id" type="var">T\_App</span></span>,
    then there are terms <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> and <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> and types <span
    class="inlinecode"><span class="id" type="var">T~1~</span></span>
    and <span class="inlinecode"><span class="id"
    type="var">T~2~</span></span> such that <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">t~1~</span></span> <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span>,
    <span class="inlinecode"><span class="id" type="var">T</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">T~2~</span></span>, <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">T~1~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">→</span></span>
    <span class="inlinecode"><span class="id"
    type="var">T~2~</span></span>, and <span class="inlinecode"><span
    class="id" type="var">empty</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> <span class="inlinecode">:</span>
    <span class="inlinecode"><span class="id"
    type="var">T~1~</span></span>.
    <div class="paragraph">

    </div>

    By the definition of the step relation, there are three ways <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> can step. Cases <span
    class="inlinecode"><span class="id"
    type="var">ST\_App1</span></span> and <span class="inlinecode"><span
    class="id" type="var">ST\_App2</span></span> follow immediately by
    the induction hypotheses for the typing subderivations and a use of
    <span class="inlinecode"><span class="id"
    type="var">T\_App</span></span>.
    <div class="paragraph">

    </div>

    Suppose instead <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> steps by <span
    class="inlinecode"><span class="id"
    type="var">ST\_AppAbs</span></span>. Then <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode">\\<span
    class="id" type="var">x</span>:<span class="id"
    type="var">S.t~12~</span></span> for some type <span
    class="inlinecode"><span class="id" type="var">S</span></span> and
    term <span class="inlinecode"><span class="id"
    type="var">t~12~</span></span>, and <span class="inlinecode"><span
    class="id" type="var">t'</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode">[<span
    class="id" type="var">x</span>:=<span class="id"
    type="var">t~2~</span>]<span class="id"
    type="var">t~12~</span></span>.
    <div class="paragraph">

    </div>

    By lemma <span class="inlinecode"><span class="id"
    type="var">abs\_arrow</span></span>, we have <span
    class="inlinecode"><span class="id" type="var">T~1~</span></span>
    <span class="inlinecode">\<:</span> <span class="inlinecode"><span
    class="id" type="var">S</span></span> and <span
    class="inlinecode"><span class="id" type="var">x</span>:<span
    class="id" type="var">S~1~</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">s~2~</span></span> <span class="inlinecode">:</span>
    <span class="inlinecode"><span class="id"
    type="var">T~2~</span></span>. It then follows by the substitution
    lemma (<span class="inlinecode"><span class="id"
    type="var">substitution\_preserves\_typing</span></span>) that <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode">[<span class="id" type="var">x</span>:=<span
    class="id" type="var">t~2~</span>]</span> <span
    class="inlinecode"><span class="id" type="var">t~12~</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">T~2~</span></span> as desired.
    <div class="paragraph">

    </div>

    -   If the final step of the derivation uses rule <span
        class="inlinecode"><span class="id"
        type="var">T\_If</span></span>, then there are terms <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span>, <span class="inlinecode"><span
        class="id" type="var">t~2~</span></span>, and <span
        class="inlinecode"><span class="id"
        type="var">t~3~</span></span> such that <span
        class="inlinecode"><span class="id" type="var">t</span></span>
        <span class="inlinecode">=</span> <span class="inlinecode"><span
        class="id" type="keyword">if</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode"><span
        class="id" type="keyword">then</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~2~</span></span> <span class="inlinecode"><span
        class="id" type="keyword">else</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~3~</span></span>, with <span
        class="inlinecode"><span class="id"
        type="var">empty</span></span> <span class="inlinecode"><span
        style="font-family: arial;">⊢</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode">:</span>
        <span class="inlinecode"><span class="id"
        type="var">Bool</span></span> and with <span
        class="inlinecode"><span class="id"
        type="var">empty</span></span> <span class="inlinecode"><span
        style="font-family: arial;">⊢</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~2~</span></span> <span class="inlinecode">:</span>
        <span class="inlinecode"><span class="id"
        type="var">T</span></span> and <span class="inlinecode"><span
        class="id" type="var">empty</span></span> <span
        class="inlinecode"><span
        style="font-family: arial;">⊢</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~3~</span></span> <span class="inlinecode">:</span>
        <span class="inlinecode"><span class="id"
        type="var">T</span></span>. Moreover, by the induction
        hypothesis, if <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> steps to <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span> then <span
        class="inlinecode"><span class="id"
        type="var">empty</span></span> <span class="inlinecode"><span
        style="font-family: arial;">⊢</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span> <span class="inlinecode">:</span>
        <span class="inlinecode"><span class="id"
        type="var">Bool</span></span>. There are three cases to
        consider, depending on which rule was used to show <span
        class="inlinecode"><span class="id" type="var">t</span></span>
        <span class="inlinecode"><span
        style="font-family: arial;">⇒</span></span> <span
        class="inlinecode"><span class="id" type="var">t'</span></span>.
        <div class="paragraph">

        </div>

        -   If <span class="inlinecode"><span class="id"
            type="var">t</span></span> <span class="inlinecode"><span
            style="font-family: arial;">⇒</span></span> <span
            class="inlinecode"><span class="id"
            type="var">t'</span></span> by rule <span
            class="inlinecode"><span class="id"
            type="var">ST\_If</span></span>, then <span
            class="inlinecode"><span class="id"
            type="var">t'</span></span> <span
            class="inlinecode">=</span> <span class="inlinecode"><span
            class="id" type="keyword">if</span></span> <span
            class="inlinecode"><span class="id"
            type="var">t~1~'</span></span> <span
            class="inlinecode"><span class="id"
            type="keyword">then</span></span> <span
            class="inlinecode"><span class="id"
            type="var">t~2~</span></span> <span class="inlinecode"><span
            class="id" type="keyword">else</span></span> <span
            class="inlinecode"><span class="id"
            type="var">t~3~</span></span> with <span
            class="inlinecode"><span class="id"
            type="var">t~1~</span></span> <span class="inlinecode"><span
            style="font-family: arial;">⇒</span></span> <span
            class="inlinecode"><span class="id"
            type="var">t~1~'</span></span>. By the induction hypothesis,
            <span class="inlinecode"><span class="id"
            type="var">empty</span></span> <span
            class="inlinecode"><span
            style="font-family: arial;">⊢</span></span> <span
            class="inlinecode"><span class="id"
            type="var">t~1~'</span></span> <span
            class="inlinecode">:</span> <span class="inlinecode"><span
            class="id" type="var">Bool</span></span>, and so <span
            class="inlinecode"><span class="id"
            type="var">empty</span></span> <span
            class="inlinecode"><span
            style="font-family: arial;">⊢</span></span> <span
            class="inlinecode"><span class="id"
            type="var">t'</span></span> <span
            class="inlinecode">:</span> <span class="inlinecode"><span
            class="id" type="var">T</span></span> by <span
            class="inlinecode"><span class="id"
            type="var">T\_If</span></span>.
            <div class="paragraph">

            </div>

        -   If <span class="inlinecode"><span class="id"
            type="var">t</span></span> <span class="inlinecode"><span
            style="font-family: arial;">⇒</span></span> <span
            class="inlinecode"><span class="id"
            type="var">t'</span></span> by rule <span
            class="inlinecode"><span class="id"
            type="var">ST\_IfTrue</span></span> or <span
            class="inlinecode"><span class="id"
            type="var">ST\_IfFalse</span></span>, then either <span
            class="inlinecode"><span class="id"
            type="var">t'</span></span> <span
            class="inlinecode">=</span> <span class="inlinecode"><span
            class="id" type="var">t~2~</span></span> or <span
            class="inlinecode"><span class="id"
            type="var">t'</span></span> <span
            class="inlinecode">=</span> <span class="inlinecode"><span
            class="id" type="var">t~3~</span></span>, and <span
            class="inlinecode"><span class="id"
            type="var">empty</span></span> <span
            class="inlinecode"><span
            style="font-family: arial;">⊢</span></span> <span
            class="inlinecode"><span class="id"
            type="var">t'</span></span> <span
            class="inlinecode">:</span> <span class="inlinecode"><span
            class="id" type="var">T</span></span> follows by assumption.
            <div class="paragraph">

            </div>
-   If the final step of the derivation is by <span
    class="inlinecode"><span class="id" type="var">T\_Sub</span></span>,
    then there is a type <span class="inlinecode"><span class="id"
    type="var">S</span></span> such that <span class="inlinecode"><span
    class="id" type="var">S</span></span> <span
    class="inlinecode">\<:</span> <span class="inlinecode"><span
    class="id" type="var">T</span></span> and <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">S</span></span>. The result is immediate by
    the induction hypothesis for the typing subderivation and an
    application of <span class="inlinecode"><span class="id"
    type="var">T\_Sub</span></span>. ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">preservation</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">t'</span> <span class="id"
type="var">T</span>,\
      <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t'</span> ∈ <span class="id" type="var">T</span>.\
<div id="proofcontrol14" class="togglescript"
onclick="toggleDisplay('proof14');toggleDisplay('proofcontrol14')">

<span class="show"></span>

</div>

<div id="proof14" class="proofscript"
onclick="toggleDisplay('proof14');toggleDisplay('proofcontrol14')"
style="display: none;">

<span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">t'</span> <span
class="id" type="var">T</span> <span class="id" type="var">HT</span>.\
   <span class="id" type="var">remember</span> <span class="id"
type="var">empty</span> <span class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id"
type="var">HeqGamma</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">t'</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">HT</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">t'</span> <span class="id" type="var">HeqGamma</span> <span
class="id" type="var">HE</span>; <span class="id"
type="tactic">subst</span>; <span class="id"
type="tactic">inversion</span> <span class="id" type="var">HE</span>;
<span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">SCase</span> "ST\_AppAbs".\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">abs\_arrow</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span> <span class="id"
type="var">\_</span> <span class="id" type="var">HT1</span>) <span
class="id" type="keyword">as</span> [<span class="id"
type="var">HA1</span> <span class="id" type="var">HA2</span>].\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">substitution\_preserves\_typing</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">T</span>...\
 <span class="id" type="keyword">Qed</span>.\

</div>

\

</div>

<div class="doc">

Records, via Products and Top {.section}
-----------------------------

<div class="paragraph">

</div>

This formalization of the STLC with subtyping has omitted record types,
for brevity. If we want to deal with them more seriously, we have two
choices.
<div class="paragraph">

</div>

First, we can treat them as part of the core language, writing down
proper syntax, typing, and subtyping rules for them. Chapter <span
class="inlinecode"><span class="id" type="var">RecordSub</span></span>
shows how this extension works.
<div class="paragraph">

</div>

On the other hand, if we are treating them as a derived form that is
desugared in the parser, then we shouldn't need any new rules: we should
just check that the existing rules for subtyping product and <span
class="inlinecode"><span class="id" type="var">Unit</span></span> types
give rise to reasonable rules for record subtyping via this encoding. To
do this, we just need to make one small change to the encoding described
earlier: instead of using <span class="inlinecode"><span class="id"
type="var">Unit</span></span> as the base case in the encoding of tuples
and the "don't care" placeholder in the encoding of records, we use
<span class="inlinecode"><span class="id" type="var">Top</span></span>.
So:
        {a:Nat, b:Nat} ----> {Nat,Nat}       i.e. (Nat,(Nat,Top))
        {c:Nat, a:Nat} ----> {Nat,Top,Nat}   i.e. (Nat,(Top,(Nat,Top)))

The encoding of record values doesn't change at all. It is easy (and
instructive) to check that the subtyping rules above are validated by
the encoding. For the rest of this chapter, we'll follow this
encoding-based approach.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Exercises {.section}
---------

<div class="paragraph">

</div>

#### Exercise: 2 stars (variations) {.section}

Each part of this problem suggests a different way of changing the
definition of the STLC with Unit and subtyping. (These changes are not
cumulative: each part starts from the original language.) In each part,
list which properties (Progress, Preservation, both, or neither) become
false. If a property becomes false, give a counterexample.
<div class="paragraph">

</div>

-   Suppose we add the following typing rule:
    <span style="font-family: serif; font-size:85%;">Γ</span> <span
    style="font-family: arial;">⊢</span> t : S~1~-\>S~2~
    S~1~ \<: T~1~      T~1~ \<: S~1~     S~2~ \<: T~2~
    (T\_Funny1)  

    ------------------------------------------------------------------------

    <span style="font-family: serif; font-size:85%;">Γ</span> <span
    style="font-family: arial;">⊢</span> t : T~1~-\>T~2~
    <div class="paragraph">

    </div>

-   Suppose we add the following reduction rule:
      
    (ST\_Funny21)  

    ------------------------------------------------------------------------

    unit <span style="font-family: arial;">⇒</span> (\\x:Top. x)
    <div class="paragraph">

    </div>

-   Suppose we add the following subtyping rule:
      
    (S\_Funny3)  

    ------------------------------------------------------------------------

    Unit \<: Top-\>Top
    <div class="paragraph">

    </div>

-   Suppose we add the following subtyping rule:
      
    (S\_Funny4)  

    ------------------------------------------------------------------------

    Top-\>Top \<: Unit
    <div class="paragraph">

    </div>

-   Suppose we add the following evaluation rule:
      
    (ST\_Funny5)  

    ------------------------------------------------------------------------

    (unit t) <span style="font-family: arial;">⇒</span> (t unit)
    <div class="paragraph">

    </div>

-   Suppose we add the same evaluation rule *and* a new typing rule:
      
    (ST\_Funny5)  

    ------------------------------------------------------------------------

    (unit t) <span style="font-family: arial;">⇒</span> (t unit)
      
    (T\_Funny6)  

    ------------------------------------------------------------------------

    empty <span style="font-family: arial;">⊢</span> Unit : Top-\>Top
    <div class="paragraph">

    </div>

-   Suppose we *change* the arrow subtyping rule to:
    S~1~ \<: T~1~       S~2~ \<: T~2~
    (S\_Arrow')  

    ------------------------------------------------------------------------

    S~1~-\>S~2~ \<: T~1~-\>T~2~

<div class="paragraph">

</div>

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Exercise: Adding Products {.section}
=========================

<div class="paragraph">

</div>

#### Exercise: 4 stars (products) {.section}

Adding pairs, projections, and product types to the system we have
defined is a relatively straightforward matter. Carry out this
extension:
<div class="paragraph">

</div>

-   Add constructors for pairs, first and second projections, and
    product types to the definitions of <span class="inlinecode"><span
    class="id" type="var">ty</span></span> and <span
    class="inlinecode"><span class="id" type="var">tm</span></span>.
    (Don't forget to add corresponding cases to <span
    class="inlinecode"><span class="id"
    type="var">T\_cases</span></span> and <span class="inlinecode"><span
    class="id" type="var">t\_cases</span></span>.)
    <div class="paragraph">

    </div>

-   Extend the substitution function and value relation as in MoreSTLC.
    <div class="paragraph">

    </div>

-   Extend the operational semantics with the same reduction rules as in
    MoreSTLC.
    <div class="paragraph">

    </div>

-   Extend the subtyping relation with this rule:
    <div class="paragraph">

    </div>

    S~1~ \<: T~1~ S~2~ \<: T~2~
    -   —————————— (Sub\_Prod) S~1~ \* S~2~ \<: T~1~ \* T~2~
        <div class="paragraph">

        </div>
-   Extend the typing relation with the same rules for pairs and
    projections as in MoreSTLC.
    <div class="paragraph">

    </div>

-   Extend the proofs of progress, preservation, and all their
    supporting lemmas to deal with the new constructs. (You'll also need
    to add some completely new lemmas.)

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
