<div id="page">

<div id="header">

</div>

<div id="main">

Records<span class="subtitle">Adding Records to STLC</span> {.libtitle}
===========================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">Stlc</span>.\
\

</div>

<div class="doc">

Adding Records {.section}
==============

<div class="paragraph">

</div>

We saw in chapter <span class="inlinecode"><span class="id"
type="var">MoreStlc</span></span> how records can be treated as
syntactic sugar for nested uses of products. This is fine for simple
examples, but the encoding is informal (in reality, if we really treated
records this way, it would be carried out in the parser, which we are
eliding here), and anyway it is not very efficient. So it is also
interesting to see how records can be treated as first-class citizens of
the language.
<div class="paragraph">

</div>

Recall the informal definitions we gave before:
<div class="paragraph">

</div>

<div class="paragraph">

</div>

Syntax:
           t ::=                          Terms:
               | ...
               | {i1=t1, ..., in=tn}         record 
               | t.i                         projection

           v ::=                          Values:
               | ...
               | {i1=v1, ..., in=vn}         record value

           T ::=                          Types:
               | ...
               | {i1:T1, ..., in:Tn}         record type

Reduction:
ti <span
style="font-family: arial;">⇒</span> ti'                            (ST\_Rcd)
 

------------------------------------------------------------------------

{i1=v~1~, ..., im=vm, in=tn, ...} <span
style="font-family: arial;">⇒</span> {i1=v~1~, ..., im=vm, in=tn', ...}
t~1~ <span style="font-family: arial;">⇒</span> t~1~'
(ST\_Proj1)  

------------------------------------------------------------------------

t~1~.i <span style="font-family: arial;">⇒</span> t~1~'.i
  
(ST\_ProjRcd)  

------------------------------------------------------------------------

{..., i=vi, ...}.i <span style="font-family: arial;">⇒</span> vi
Typing:
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t~1~ : T~1~     ...     <span
style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> tn : Tn
(T\_Rcd)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> {i1=t~1~, ..., in=tn} : {i1:T~1~, ..., in:Tn}
<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t : {..., i:Ti, ...}
(T\_Proj)  

------------------------------------------------------------------------

<span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> t.i : Ti

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Formalizing Records {.section}
===================

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">STLCExtendedRecords</span>.\
\

</div>

<div class="doc">

### Syntax and Operational Semantics {.section}

<div class="paragraph">

</div>

The most obvious way to formalize the syntax of record types would be
this:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">FirstTry</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">alist</span> (<span class="id" type="var">X</span> : <span
class="id" type="keyword">Type</span>) := <span class="id"
type="var">list</span> (<span class="id" type="var">id</span> × <span
class="id" type="var">X</span>).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ty</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">TBase</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span>\
   | <span class="id" type="var">TArrow</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TRcd</span> : (<span class="id"
type="var">alist</span> <span class="id" type="var">ty</span>) <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span>.\
\

</div>

<div class="doc">

Unfortunately, we encounter here a limitation in Coq: this type does not
automatically give us the induction principle we expect the induction
hypothesis in the <span class="inlinecode"><span class="id"
type="var">TRcd</span></span> case doesn't give us any information about
the <span class="inlinecode"><span class="id"
type="var">ty</span></span> elements of the list, making it useless for
the proofs we want to do.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* Check ty\_ind. \
    ====\>\
     ty\_ind : \
       forall P : ty -\> Prop,\
         (forall i : id, P (TBase i)) -\>\

        (forall t : ty, P t -\> forall t0 : ty, P t0 -\> P (TArrow t t0)) -\>\
         (forall a : alist ty, P (TRcd a)) -\>    <span
class="comment">(\* ??? \*)</span>\
         forall t : ty, P t\
 \*)</span>\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">FirstTry</span>.\
\

</div>

<div class="doc">

It is possible to get a better induction principle out of Coq, but the
details of how this is done are not very pretty, and it is not as
intuitive to use as the ones Coq generates automatically for simple
<span class="inlinecode"><span class="id"
type="keyword">Inductive</span></span> definitions.
<div class="paragraph">

</div>

Fortunately, there is a different way of formalizing records that is, in
some ways, even simpler and more natural: instead of using the existing
<span class="inlinecode"><span class="id" type="var">list</span></span>
type, we can essentially include its constructors ("nil" and "cons") in
the syntax of types.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ty</span> : <span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">TBase</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span>\
   | <span class="id" type="var">TArrow</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TRNil</span> : <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TRCons</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span> "T\_cases" <span
class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "TBase" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"TArrow"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "TRNil" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"TRCons" ].\
\

</div>

<div class="doc">

Similarly, at the level of terms, we have constructors <span
class="inlinecode"><span class="id" type="var">trnil</span></span> the
empty record — and <span class="inlinecode"><span class="id"
type="var">trcons</span></span>, which adds a single field to the front
of a list of fields.

</div>

<div class="code code-tight">

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
   <span class="comment">(\* records \*)</span>\
   | <span class="id" type="var">tproj</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">id</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">trnil</span> : <span class="id"
type="var">tm</span>\
   | <span class="id" type="var">trcons</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">tm</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span> "t\_cases" <span
class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tvar" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "tapp"
| <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tabs"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "tproj" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "trnil"
| <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "trcons" ].\
\

</div>

<div class="doc">

Some variables, for examples...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">a</span> := (<span class="id" type="var">Id</span> 0).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">f</span> := (<span class="id" type="var">Id</span> 1).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">g</span> := (<span class="id" type="var">Id</span> 2).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">l</span> := (<span class="id" type="var">Id</span> 3).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">A</span> := (<span class="id" type="var">TBase</span> (<span
class="id" type="var">Id</span> 4)).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">B</span> := (<span class="id" type="var">TBase</span> (<span
class="id" type="var">Id</span> 5)).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">k</span> := (<span class="id" type="var">Id</span> 6).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">i1</span> := (<span class="id" type="var">Id</span> 7).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">i2</span> := (<span class="id" type="var">Id</span> 8).\
\

</div>

<div class="doc">

<span class="inlinecode">{</span> <span class="inlinecode"><span
class="id" type="var">i1</span>:<span class="id"
type="var">A</span></span> <span class="inlinecode">}</span>

</div>

<div class="code code-tight">

\
 <span class="comment">(\* Check (TRCons i1 A TRNil). \*)</span>\
\

</div>

<div class="doc">

<span class="inlinecode">{</span> <span class="inlinecode"><span
class="id" type="var">i1</span>:<span class="id"
type="var">A</span><span style="font-family: arial;">→</span><span
class="id" type="var">B</span>,</span> <span class="inlinecode"><span
class="id" type="var">i2</span>:<span class="id"
type="var">A</span></span> <span class="inlinecode">}</span>

</div>

<div class="code code-tight">

\
 <span class="comment">(\* Check (TRCons i1 (TArrow A B) \
            (TRCons i2 A TRNil)). \*)</span>\
\

</div>

<div class="doc">

### Well-Formedness {.section}

<div class="paragraph">

</div>

Generalizing our abstract syntax for records (from lists to the nil/cons
presentation) introduces the possibility of writing strange types like
this

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">weird\_type</span> := <span class="id"
type="var">TRCons</span> <span class="id" type="var">X</span> <span
class="id" type="var">A</span> <span class="id" type="var">B</span>.\
\

</div>

<div class="doc">

where the "tail" of a record type is not actually a record type!
<div class="paragraph">

</div>

We'll structure our typing judgement so that no ill-formed types like
<span class="inlinecode"><span class="id"
type="var">weird\_type</span></span> are assigned to terms. To support
this, we define <span class="inlinecode"><span class="id"
type="var">record\_ty</span></span> and <span class="inlinecode"><span
class="id" type="var">record\_tm</span></span>, which identify record
types and terms, and <span class="inlinecode"><span class="id"
type="var">well\_formed\_ty</span></span> which rules out the ill-formed
types.
<div class="paragraph">

</div>

First, a type is a record type if it is built with just <span
class="inlinecode"><span class="id" type="var">TRNil</span></span> and
<span class="inlinecode"><span class="id"
type="var">TRCons</span></span> at the outermost level.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">record\_ty</span> : <span class="id" type="var">ty</span>
<span style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">RTnil</span> :\
         <span class="id" type="var">record\_ty</span> <span class="id"
type="var">TRNil</span>\
   | <span class="id" type="var">RTcons</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">i</span>
<span class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>,\
         <span class="id" type="var">record\_ty</span> (<span class="id"
type="var">TRCons</span> <span class="id" type="var">i</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>).\
\

</div>

<div class="doc">

Similarly, a term is a record term if it is built with <span
class="inlinecode"><span class="id" type="var">trnil</span></span> and
<span class="inlinecode"><span class="id"
type="var">trcons</span></span>

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">record\_tm</span> : <span class="id" type="var">tm</span>
<span style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">rtnil</span> :\
         <span class="id" type="var">record\_tm</span> <span class="id"
type="var">trnil</span>\
   | <span class="id" type="var">rtcons</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">i</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>,\
         <span class="id" type="var">record\_tm</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span>).\
\

</div>

<div class="doc">

Note that <span class="inlinecode"><span class="id"
type="var">record\_ty</span></span> and <span class="inlinecode"><span
class="id" type="var">record\_tm</span></span> are not recursive — they
just check the outermost constructor. The <span class="inlinecode"><span
class="id" type="var">well\_formed\_ty</span></span> property, on the
other hand, verifies that the whole type is well formed in the sense
that the tail of every record (the second argument to <span
class="inlinecode"><span class="id" type="var">TRCons</span></span>) is
a record.
<div class="paragraph">

</div>

Of course, we should also be concerned about ill-formed terms, not just
types; but typechecking can rules those out without the help of an extra
<span class="inlinecode"><span class="id"
type="var">well\_formed\_tm</span></span> definition because it already
examines the structure of terms. LATER : should they fill in part of
this as an exercise? We didn't give rules for it above

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">well\_formed\_ty</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">wfTBase</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">i</span>,\
         <span class="id" type="var">well\_formed\_ty</span> (<span
class="id" type="var">TBase</span> <span class="id"
type="var">i</span>)\
   | <span class="id" type="var">wfTArrow</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span>,\
         <span class="id" type="var">well\_formed\_ty</span> <span
class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
         <span class="id" type="var">well\_formed\_ty</span> <span
class="id" type="var">T~2~</span> <span
style="font-family: arial;">→</span>\
         <span class="id" type="var">well\_formed\_ty</span> (<span
class="id" type="var">TArrow</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span>)\
   | <span class="id" type="var">wfTRNil</span> :\
         <span class="id" type="var">well\_formed\_ty</span> <span
class="id" type="var">TRNil</span>\
   | <span class="id" type="var">wfTRCons</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">i</span>
<span class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>,\
         <span class="id" type="var">well\_formed\_ty</span> <span
class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
         <span class="id" type="var">well\_formed\_ty</span> <span
class="id" type="var">T~2~</span> <span
style="font-family: arial;">→</span>\
         <span class="id" type="var">record\_ty</span> <span class="id"
type="var">T~2~</span> <span style="font-family: arial;">→</span>\
         <span class="id" type="var">well\_formed\_ty</span> (<span
class="id" type="var">TRCons</span> <span class="id" type="var">i</span>
<span class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>).\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">record\_ty</span> <span class="id"
type="var">record\_tm</span> <span class="id"
type="var">well\_formed\_ty</span>.\
\

</div>

<div class="doc">

### Substitution {.section}

</div>

<div class="code code-space">

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
type="var">y</span> ⇒ <span class="id" type="keyword">if</span> <span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">s</span> <span class="id" type="keyword">else</span> <span
class="id" type="var">t</span>\
   | <span class="id" type="var">tabs</span> <span class="id"
type="var">y</span> <span class="id" type="var">T</span> <span
class="id" type="var">t~1~</span> ⇒ <span class="id"
type="var">tabs</span> <span class="id" type="var">y</span> <span
class="id" type="var">T</span> (<span class="id"
type="keyword">if</span> <span class="id" type="var">eq\_id\_dec</span>
<span class="id" type="var">x</span> <span class="id"
type="var">y</span> <span class="id" type="keyword">then</span> <span
class="id" type="var">t~1~</span> <span class="id"
type="keyword">else</span> (<span class="id" type="tactic">subst</span>
<span class="id" type="var">x</span> <span class="id"
type="var">s</span> <span class="id" type="var">t~1~</span>))\
   | <span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒ <span
class="id" type="var">tapp</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
(<span class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~2~</span>)\
   | <span class="id" type="var">tproj</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">i</span> ⇒ <span
class="id" type="var">tproj</span> (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">t~1~</span>)
<span class="id" type="var">i</span>\
   | <span class="id" type="var">trnil</span> ⇒ <span class="id"
type="var">trnil</span>\
   | <span class="id" type="var">trcons</span> <span class="id"
type="var">i</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">tr1</span> ⇒ <span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> (<span
class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~1~</span>) (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">tr1</span>)\
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

Next we define the values of our language. A record is a value if all of
its fields are.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">value</span> : <span class="id" type="var">tm</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">v\_abs</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>,\
       <span class="id" type="var">value</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>)\
   | <span class="id" type="var">v\_rnil</span> : <span class="id"
type="var">value</span> <span class="id" type="var">trnil</span>\
   | <span class="id" type="var">v\_rcons</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">i</span>
<span class="id" type="var">v~1~</span> <span class="id"
type="var">vr</span>,\
       <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">value</span> <span class="id"
type="var">vr</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">value</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">v~1~</span> <span class="id"
type="var">vr</span>).\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">value</span>.\
\

</div>

<div class="doc">

Utility functions for extracting one field from record type or term:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">Tlookup</span> (<span class="id" type="var">i</span>:<span
class="id" type="var">id</span>) (<span class="id"
type="var">Tr</span>:<span class="id" type="var">ty</span>) : <span
class="id" type="var">option</span> <span class="id"
type="var">ty</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">Tr</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">TRCons</span> <span class="id"
type="var">i'</span> <span class="id" type="var">T</span> <span
class="id" type="var">Tr'</span> ⇒ <span class="id"
type="keyword">if</span> <span class="id" type="var">eq\_id\_dec</span>
<span class="id" type="var">i</span> <span class="id"
type="var">i'</span> <span class="id" type="keyword">then</span> <span
class="id" type="var">Some</span> <span class="id" type="var">T</span>
<span class="id" type="keyword">else</span> <span class="id"
type="var">Tlookup</span> <span class="id" type="var">i</span> <span
class="id" type="var">Tr'</span>\
   | <span class="id" type="var">\_</span> ⇒ <span class="id"
type="var">None</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">tlookup</span> (<span class="id" type="var">i</span>:<span
class="id" type="var">id</span>) (<span class="id"
type="var">tr</span>:<span class="id" type="var">tm</span>) : <span
class="id" type="var">option</span> <span class="id"
type="var">tm</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">tr</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">trcons</span> <span class="id"
type="var">i'</span> <span class="id" type="var">t</span> <span
class="id" type="var">tr'</span> ⇒ <span class="id"
type="keyword">if</span> <span class="id" type="var">eq\_id\_dec</span>
<span class="id" type="var">i</span> <span class="id"
type="var">i'</span> <span class="id" type="keyword">then</span> <span
class="id" type="var">Some</span> <span class="id" type="var">t</span>
<span class="id" type="keyword">else</span> <span class="id"
type="var">tlookup</span> <span class="id" type="var">i</span> <span
class="id" type="var">tr'</span>\
   | <span class="id" type="var">\_</span> ⇒ <span class="id"
type="var">None</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="var">step</span></span> function uses the term-level lookup
function (for the projection rule), while the type-level lookup is
needed for <span class="inlinecode"><span class="id"
type="var">has\_type</span></span>.

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
<span class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span> <span class="id" type="var">v~2~</span>,\
          <span class="id" type="var">value</span> <span class="id"
type="var">v~2~</span> <span style="font-family: arial;">→</span>\
          (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>) <span class="id" type="var">v~2~</span>) <span
style="font-family: arial;">⇒</span> ([<span class="id"
type="var">x</span>:=<span class="id" type="var">v~2~</span>]<span
class="id" type="var">t~12~</span>)\
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
   | <span class="id" type="var">ST\_Proj1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">t~1~</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">i</span>,\
         <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tproj</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">i</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tproj</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">i</span>)\
   | <span class="id" type="var">ST\_ProjRcd</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">tr</span> <span class="id" type="var">i</span> <span
class="id" type="var">vi</span>,\
         <span class="id" type="var">value</span> <span class="id"
type="var">tr</span> <span style="font-family: arial;">→</span>\
         <span class="id" type="var">tlookup</span> <span class="id"
type="var">i</span> <span class="id" type="var">tr</span> = <span
class="id" type="var">Some</span> <span class="id" type="var">vi</span>
<span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tproj</span> <span class="id"
type="var">tr</span> <span class="id" type="var">i</span>) <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">vi</span>\
   | <span class="id" type="var">ST\_Rcd\_Head</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">i</span>
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~1~'</span> <span class="id" type="var">tr2</span>,\
         <span class="id" type="var">t~1~</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t~1~'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">trcons</span> <span class="id"
type="var">i</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">tr2</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">t~1~'</span> <span class="id"
type="var">tr2</span>)\
   | <span class="id" type="var">ST\_Rcd\_Tail</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">i</span>
<span class="id" type="var">v~1~</span> <span class="id"
type="var">tr2</span> <span class="id" type="var">tr2'</span>,\
         <span class="id" type="var">value</span> <span class="id"
type="var">v~1~</span> <span style="font-family: arial;">→</span>\
         <span class="id" type="var">tr2</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tr2'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">trcons</span> <span class="id"
type="var">i</span> <span class="id" type="var">v~1~</span> <span
class="id" type="var">tr2</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">v~1~</span> <span class="id"
type="var">tr2'</span>)\
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
"ST\_App1" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "ST\_App2"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Proj1" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_ProjRcd"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Rcd\_Head" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Rcd\_Tail" ].\
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
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id" type="var">step</span>.\
\

</div>

<div class="doc">

### Typing {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">context</span> := <span class="id"
type="var">partial\_map</span> <span class="id" type="var">ty</span>.\
\

</div>

<div class="doc">

Next we define the typing rules. These are nearly direct transcriptions
of the inference rules shown above. The only major difference is the use
of <span class="inlinecode"><span class="id"
type="var">well\_formed\_ty</span></span>. In the informal presentation
we used a grammar that only allowed well formed record types, so we
didn't have to add a separate check.
<div class="paragraph">

</div>

We'd like to set things up so that that whenever <span
class="inlinecode"><span class="id" type="var">has\_type</span></span>
<span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode"><span class="id" type="var">T</span></span> holds, we
also have <span class="inlinecode"><span class="id"
type="var">well\_formed\_ty</span></span> <span class="inlinecode"><span
class="id" type="var">T</span></span>. That is, <span
class="inlinecode"><span class="id" type="var">has\_type</span></span>
never assigns ill-formed types to terms. In fact, we prove this theorem
below.
<div class="paragraph">

</div>

However, we don't want to clutter the definition of <span
class="inlinecode"><span class="id" type="var">has\_type</span></span>
with unnecessary uses of <span class="inlinecode"><span class="id"
type="var">well\_formed\_ty</span></span>. Instead, we place <span
class="inlinecode"><span class="id"
type="var">well\_formed\_ty</span></span> checks only where needed -
where an inductive call to <span class="inlinecode"><span class="id"
type="var">has\_type</span></span> won't already be checking the
well-formedness of a type.
<div class="paragraph">

</div>

For example, we check <span class="inlinecode"><span class="id"
type="var">well\_formed\_ty</span></span> <span class="inlinecode"><span
class="id" type="var">T</span></span> in the <span
class="inlinecode"><span class="id" type="var">T\_Var</span></span>
case, because there is no inductive <span class="inlinecode"><span
class="id" type="var">has\_type</span></span> call that would enforce
this. Similarly, in the <span class="inlinecode"><span class="id"
type="var">T\_Abs</span></span> case, we require a proof of <span
class="inlinecode"><span class="id"
type="var">well\_formed\_ty</span></span> <span class="inlinecode"><span
class="id" type="var">T~11~</span></span> because the inductive call to
<span class="inlinecode"><span class="id"
type="var">has\_type</span></span> only guarantees that <span
class="inlinecode"><span class="id" type="var">T~12~</span></span> is
well-formed.
<div class="paragraph">

</div>

In the rules you must write, the only necessary <span
class="inlinecode"><span class="id"
type="var">well\_formed\_ty</span></span> check comes in the <span
class="inlinecode"><span class="id" type="var">tnil</span></span> case.

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
       <span class="id" type="var">well\_formed\_ty</span> <span
class="id" type="var">T</span> <span
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
       <span class="id" type="var">well\_formed\_ty</span> <span
class="id" type="var">T~11~</span> <span
style="font-family: arial;">→</span>\
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
   <span class="comment">(\* records: \*)</span>\
   | <span class="id" type="var">T\_Proj</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">i</span> <span class="id" type="var">t</span> <span
class="id" type="var">Ti</span> <span class="id" type="var">Tr</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">Tr</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">Tlookup</span> <span class="id"
type="var">i</span> <span class="id" type="var">Tr</span> = <span
class="id" type="var">Some</span> <span class="id" type="var">Ti</span>
<span style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">tproj</span> <span class="id" type="var">t</span> <span
class="id" type="var">i</span>) ∈ <span class="id" type="var">Ti</span>\
   | <span class="id" type="var">T\_RNil</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">trnil</span> ∈ <span class="id" type="var">TRNil</span>\
   | <span class="id" type="var">T\_RCons</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">i</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span class="id" type="var">tr</span>
<span class="id" type="var">Tr</span>,\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">tr</span> ∈ <span class="id" type="var">Tr</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">record\_ty</span> <span class="id"
type="var">Tr</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">record\_tm</span> <span class="id"
type="var">tr</span> <span style="font-family: arial;">→</span>\
       <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">t</span> <span class="id" type="var">tr</span>) ∈
(<span class="id" type="var">TRCons</span> <span class="id"
type="var">i</span> <span class="id" type="var">T</span> <span
class="id" type="var">Tr</span>)\
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
"T\_Abs" | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_App"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_Proj" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_RNil" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "T\_RCons" ].\
\

</div>

<div class="doc">

Examples {.section}
--------

<div class="paragraph">

</div>

#### Exercise: 2 stars (examples) {.section}

Finish the proofs.
<div class="paragraph">

</div>

Feel free to use Coq's automation features in this proof. However, if
you are not confident about how the type system works, you may want to
carry out the proof first using the basic features (<span
class="inlinecode"><span class="id" type="tactic">apply</span></span>
instead of <span class="inlinecode"><span class="id"
type="tactic">eapply</span></span>, in particular) and then perhaps
compress it using automation.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_example\_2</span> :\
   <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span>\
     (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">a</span> (<span
class="id" type="var">TRCons</span> <span class="id"
type="var">i1</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">A</span> <span class="id" type="var">A</span>)\
                       (<span class="id" type="var">TRCons</span> <span
class="id" type="var">i2</span> (<span class="id"
type="var">TArrow</span> <span class="id" type="var">B</span> <span
class="id" type="var">B</span>)\
                        <span class="id" type="var">TRNil</span>))\
               (<span class="id" type="var">tproj</span> (<span
class="id" type="var">tvar</span> <span class="id" type="var">a</span>)
<span class="id" type="var">i2</span>))\
             (<span class="id" type="var">trcons</span> <span class="id"
type="var">i1</span> (<span class="id" type="var">tabs</span> <span
class="id" type="var">a</span> <span class="id" type="var">A</span>
(<span class="id" type="var">tvar</span> <span class="id"
type="var">a</span>))\
             (<span class="id" type="var">trcons</span> <span class="id"
type="var">i2</span> (<span class="id" type="var">tabs</span> <span
class="id" type="var">a</span> <span class="id" type="var">B</span>
(<span class="id" type="var">tvar</span> <span class="id"
type="var">a</span>))\
              <span class="id" type="var">trnil</span>))) ∈\
     (<span class="id" type="var">TArrow</span> <span class="id"
type="var">B</span> <span class="id" type="var">B</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Before starting to prove this fact (or the one above!), make sure you
understand what it is saying.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_nonexample</span> :\
   ¬ <span style="font-family: arial;">∃</span><span class="id"
type="var">T</span>,\
       (<span class="id" type="var">extend</span> <span class="id"
type="var">empty</span> <span class="id" type="var">a</span> (<span
class="id" type="var">TRCons</span> <span class="id"
type="var">i2</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">A</span> <span class="id" type="var">A</span>)\
                                 <span class="id"
type="var">TRNil</span>)) <span style="font-family: arial;">⊢</span>\
                (<span class="id" type="var">trcons</span> <span
class="id" type="var">i1</span> (<span class="id" type="var">tabs</span>
<span class="id" type="var">a</span> <span class="id"
type="var">B</span> (<span class="id" type="var">tvar</span> <span
class="id" type="var">a</span>)) (<span class="id"
type="var">tvar</span> <span class="id" type="var">a</span>)) ∈\
                <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_nonexample\_2</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">y</span>,\
   ¬ <span style="font-family: arial;">∃</span><span class="id"
type="var">T</span>,\
     (<span class="id" type="var">extend</span> <span class="id"
type="var">empty</span> <span class="id" type="var">y</span> <span
class="id" type="var">A</span>) <span
style="font-family: arial;">⊢</span>\
            (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">a</span> (<span
class="id" type="var">TRCons</span> <span class="id"
type="var">i1</span> <span class="id" type="var">A</span> <span
class="id" type="var">TRNil</span>)\
                      (<span class="id" type="var">tproj</span> (<span
class="id" type="var">tvar</span> <span class="id" type="var">a</span>)
<span class="id" type="var">i1</span>))\
                    (<span class="id" type="var">trcons</span> <span
class="id" type="var">i1</span> (<span class="id" type="var">tvar</span>
<span class="id" type="var">y</span>) (<span class="id"
type="var">trcons</span> <span class="id" type="var">i2</span> (<span
class="id" type="var">tvar</span> <span class="id" type="var">y</span>)
<span class="id" type="var">trnil</span>))) ∈\
            <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Properties of Typing {.section}
--------------------

<div class="paragraph">

</div>

The proofs of progress and preservation for this system are essentially
the same as for the pure simply typed lambda-calculus, but we need to
add some technical lemmas involving records.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Well-Formedness {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">wf\_rcd\_lookup</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">i</span>
<span class="id" type="var">T</span> <span class="id"
type="var">Ti</span>,\
   <span class="id" type="var">well\_formed\_ty</span> <span class="id"
type="var">T</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">Tlookup</span> <span class="id"
type="var">i</span> <span class="id" type="var">T</span> = <span
class="id" type="var">Some</span> <span class="id" type="var">Ti</span>
<span style="font-family: arial;">→</span>\
   <span class="id" type="var">well\_formed\_ty</span> <span class="id"
type="var">Ti</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">i</span> <span class="id" type="var">T</span>.\
   <span class="id" type="var">T\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">T</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span>; <span class="id" type="tactic">try</span>
<span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
   <span class="id" type="var">Case</span> "TRCons".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">unfold</span> <span class="id"
type="var">Tlookup</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H0</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">i</span> <span
class="id" type="var">i0</span>)...\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span>. <span class="id" type="tactic">subst</span>...
<span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">step\_preserves\_record\_tm</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">tr</span> <span class="id" type="var">tr'</span>,\
   <span class="id" type="var">record\_tm</span> <span class="id"
type="var">tr</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">tr</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tr'</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">record\_tm</span> <span class="id"
type="var">tr'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">tr</span> <span class="id" type="var">tr'</span> <span
class="id" type="var">Hrt</span> <span class="id"
type="var">Hstp</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hrt</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hstp</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">has\_type\_\_wf</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span>,\
   <span style="font-family: serif; font-size:85%;">Γ</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">t</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">well\_formed\_ty</span> <span class="id"
type="var">T</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
class="id" type="var">Htyp</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Htyp</span>)
<span class="id" type="var">Case</span>...\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">IHHtyp1</span>...\
   <span class="id" type="var">Case</span> "T\_Proj".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">wf\_rcd\_lookup</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Field Lookup {.section}

<div class="paragraph">

</div>

Lemma: If <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">v</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span> and <span class="inlinecode"><span class="id"
type="var">Tlookup</span></span> <span class="inlinecode"><span
class="id" type="var">i</span></span> <span class="inlinecode"><span
class="id" type="var">T</span></span> returns <span
class="inlinecode"><span class="id" type="var">Some</span></span> <span
class="inlinecode"><span class="id" type="var">Ti</span></span>, then
<span class="inlinecode"><span class="id"
type="var">tlookup</span></span> <span class="inlinecode"><span
class="id" type="var">i</span></span> <span class="inlinecode"><span
class="id" type="var">v</span></span> returns <span
class="inlinecode"><span class="id" type="var">Some</span></span> <span
class="inlinecode"><span class="id" type="var">ti</span></span> for some
term <span class="inlinecode"><span class="id"
type="var">ti</span></span> such that <span class="inlinecode"><span
class="id" type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">ti</span></span> <span
class="inlinecode">∈</span> <span class="inlinecode"><span class="id"
type="var">Ti</span></span>.
<div class="paragraph">

</div>

Proof: By induction on the typing derivation <span
class="inlinecode"><span class="id" type="var">Htyp</span></span>. Since
<span class="inlinecode"><span class="id"
type="var">Tlookup</span></span> <span class="inlinecode"><span
class="id" type="var">i</span></span> <span class="inlinecode"><span
class="id" type="var">T</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">Some</span></span>
<span class="inlinecode"><span class="id" type="var">Ti</span></span>,
<span class="inlinecode"><span class="id" type="var">T</span></span>
must be a record type, this and the fact that <span
class="inlinecode"><span class="id" type="var">v</span></span> is a
value eliminate most cases by inspection, leaving only the <span
class="inlinecode"><span class="id" type="var">T\_RCons</span></span>
case.
<div class="paragraph">

</div>

If the last step in the typing derivation is by <span
class="inlinecode"><span class="id" type="var">T\_RCons</span></span>,
then <span class="inlinecode"><span class="id"
type="var">t</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">trcons</span></span>
<span class="inlinecode"><span class="id" type="var">i0</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode"><span class="id" type="var">tr</span></span>
and <span class="inlinecode"><span class="id" type="var">T</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">TRCons</span></span> <span
class="inlinecode"><span class="id" type="var">i0</span></span> <span
class="inlinecode"><span class="id" type="var">T</span></span> <span
class="inlinecode"><span class="id" type="var">Tr</span></span> for some
<span class="inlinecode"><span class="id" type="var">i0</span></span>,
<span class="inlinecode"><span class="id" type="var">t</span></span>,
<span class="inlinecode"><span class="id" type="var">tr</span></span>,
<span class="inlinecode"><span class="id" type="var">T</span></span> and
<span class="inlinecode"><span class="id" type="var">Tr</span></span>.
<div class="paragraph">

</div>

This leaves two possiblities to consider - either <span
class="inlinecode"><span class="id" type="var">i0</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">i</span></span> or not.
<div class="paragraph">

</div>

-   If <span class="inlinecode"><span class="id"
    type="var">i</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">i0</span></span>,
    then since <span class="inlinecode"><span class="id"
    type="var">Tlookup</span></span> <span class="inlinecode"><span
    class="id" type="var">i</span></span> <span
    class="inlinecode">(<span class="id" type="var">TRCons</span></span>
    <span class="inlinecode"><span class="id"
    type="var">i0</span></span> <span class="inlinecode"><span
    class="id" type="var">T</span></span> <span class="inlinecode"><span
    class="id" type="var">Tr</span>)</span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">Some</span></span> <span
    class="inlinecode"><span class="id" type="var">Ti</span></span> we
    have <span class="inlinecode"><span class="id"
    type="var">T</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">Ti</span></span>. It
    follows that <span class="inlinecode"><span class="id"
    type="var">t</span></span> itself satisfies the theorem.
    <div class="paragraph">

    </div>

-   On the other hand, suppose <span class="inlinecode"><span class="id"
    type="var">i</span></span> <span class="inlinecode">≠</span> <span
    class="inlinecode"><span class="id" type="var">i0</span></span>.
    Then
    <div class="paragraph">

    </div>

    <div class="code code-tight">

    <span class="id" type="var">Tlookup</span> <span class="id"
    type="var">i</span> <span class="id" type="var">T</span> = <span
    class="id" type="var">Tlookup</span> <span class="id"
    type="var">i</span> <span class="id" type="var">Tr</span>
    <div class="paragraph">

    </div>

    </div>

    and
    <div class="paragraph">

    </div>

    <div class="code code-tight">

    <span class="id" type="var">tlookup</span> <span class="id"
    type="var">i</span> <span class="id" type="var">t</span> = <span
    class="id" type="var">tlookup</span> <span class="id"
    type="var">i</span> <span class="id" type="var">tr</span>,
    <div class="paragraph">

    </div>

    </div>

    so the result follows from the induction hypothesis. ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">lookup\_field\_in\_value</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">v</span>
<span class="id" type="var">T</span> <span class="id"
type="var">i</span> <span class="id" type="var">Ti</span>,\
   <span class="id" type="var">value</span> <span class="id"
type="var">v</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">v</span> ∈ <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">Tlookup</span> <span class="id"
type="var">i</span> <span class="id" type="var">T</span> = <span
class="id" type="var">Some</span> <span class="id" type="var">Ti</span>
<span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">ti</span>, <span class="id" type="var">tlookup</span> <span
class="id" type="var">i</span> <span class="id" type="var">v</span> =
<span class="id" type="var">Some</span> <span class="id"
type="var">ti</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">empty</span> <span
style="font-family: arial;">⊢</span> <span class="id"
type="var">ti</span> ∈ <span class="id" type="var">Ti</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">v</span> <span class="id" type="var">T</span> <span
class="id" type="var">i</span> <span class="id" type="var">Ti</span>
<span class="id" type="var">Hval</span> <span class="id"
type="var">Htyp</span> <span class="id" type="var">Hget</span>.\
   <span class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Htyp</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">subst</span>; <span class="id" type="tactic">try</span>
<span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>...\
   <span class="id" type="var">Case</span> "T\_RCons".\
     <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hget</span>. <span
class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">i</span> <span
class="id" type="var">i0</span>).\
     <span class="id" type="var">SCase</span> "i is first".\
       <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hget</span>.
<span class="id" type="tactic">subst</span>.\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">t</span>...\
     <span class="id" type="var">SCase</span> "get tail".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHtyp2</span> <span class="id" type="keyword">as</span>
[<span class="id" type="var">vi</span> [<span class="id"
type="var">Hgeti</span> <span class="id" type="var">Htypi</span>]]...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hval</span>... <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Progress {.section}

</div>

<div class="code code-space">

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
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span
class="comment">(\* Theorem: Suppose empty |- t : T.  Then either\
        1. t is a value, or\
        2. t ==\> t' for some t'.\
      Proof: By induction on the given typing derivation. \*)</span>\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
class="id" type="var">Ht</span>.\
   <span class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id"
type="var">HeqGamma</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Ht</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">HeqGamma</span>;
<span class="id" type="tactic">subst</span>.\
   <span class="id" type="var">Case</span> "T\_Var".\
     <span
class="comment">(\* The final rule in the given typing derivation cannot be <span
class="inlinecode"><span class="id" type="var">T\_Var</span></span>,\
        since it can never be the case that <span
class="inlinecode"><span class="id" type="var">empty</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">x</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T</span></span> (since the\
        context is empty). \*)</span>\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="comment">(\* If the <span class="inlinecode"><span
class="id"
type="var">T\_Abs</span></span> rule was the last used, then <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">tabs</span></span> <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode"><span class="id"
type="var">T~11~</span></span> <span class="inlinecode"><span class="id"
type="var">t~12~</span></span>,\
        which is a value. \*)</span>\
     <span class="id" type="var">left</span>...\
   <span class="id" type="var">Case</span> "T\_App".\
     <span
class="comment">(\* If the last rule applied was T\_App, then <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> <span class="inlinecode"><span class="id"
type="var">t~2~</span></span>, and we know \
        from the form of the rule that\
          <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~1~</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">T~2~</span></span>\
          <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t~2~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~1~</span></span>\

       By the induction hypothesis, each of t~1~ and t~2~ either is a value \
        or can take a step. \*)</span>\
     <span class="id" type="var">right</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">SCase</span> "t~1~ is a value".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span>; <span class="id" type="tactic">subst</span>...\
       <span class="id" type="var">SSCase</span> "t~2~ is a value".\
       <span class="comment">(\* If both <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> and <span
class="inlinecode"><span class="id"
type="var">t~2~</span></span> are values, then we know that \
          <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">tabs</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">T~11~</span></span> <span
class="inlinecode"><span class="id"
type="var">t~12~</span></span>, since abstractions are the only values\
          that can have an arrow type.  But \
          <span class="inlinecode">(<span class="id"
type="var">tabs</span></span> <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode"><span class="id"
type="var">T~11~</span></span> <span class="inlinecode"><span class="id"
type="var">t~12~</span>)</span> <span class="inlinecode"><span
class="id" type="var">t~2~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">t~2~</span>]<span class="id"
type="var">t~12~</span></span> by <span class="inlinecode"><span
class="id" type="var">ST\_AppAbs</span></span>. \*)</span>\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">H</span>; <span class="id"
type="tactic">subst</span>; <span class="id" type="tactic">try</span>
(<span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>).\
         <span style="font-family: arial;">∃</span>([<span class="id"
type="var">x</span>:=<span class="id" type="var">t~2~</span>]<span
class="id" type="var">t~12~</span>)...\
       <span class="id" type="var">SSCase</span> "t~2~ steps".\
         <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> is a value and <span
class="inlinecode"><span class="id" type="var">t~2~</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span>
<span class="inlinecode"><span class="id"
type="var">t~2~'</span></span>, then <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> <span class="inlinecode"><span
class="id" type="var">t~2~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> <span
class="inlinecode"><span class="id" type="var">t~2~'</span></span> \
            by <span class="inlinecode"><span class="id"
type="var">ST\_App2</span></span>. \*)</span>\
         <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~2~'</span> <span class="id"
type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~'</span>)...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="comment">(\* Finally, If <span
class="inlinecode"><span class="id" type="var">t~1~</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span>
<span class="inlinecode"><span class="id"
type="var">t~1~'</span></span>, then <span class="inlinecode"><span
class="id" type="var">t~1~</span></span> <span class="inlinecode"><span
class="id" type="var">t~2~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t~1~'</span></span> <span
class="inlinecode"><span class="id"
type="var">t~2~</span></span> by <span class="inlinecode"><span
class="id" type="var">ST\_App1</span></span>. \*)</span>\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)...\
   <span class="id" type="var">Case</span> "T\_Proj".\
     <span
class="comment">(\* If the last rule in the given derivation is <span
class="inlinecode"><span class="id"
type="var">T\_Proj</span></span>, then \
        <span class="inlinecode"><span class="id"
type="var">t</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">tproj</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode"><span class="id" type="var">i</span></span> and\
            <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">:</span> <span class="inlinecode">(<span class="id"
type="var">TRcd</span></span> <span class="inlinecode"><span class="id"
type="var">Tr</span>)</span>\
        By the IH, <span class="inlinecode"><span class="id"
type="var">t</span></span> either is a value or takes a step. \*)</span>\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id"
type="var">IHHt</span>...\
     <span class="id" type="var">SCase</span> "rcd is value".\
       <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">t</span></span> is a value, then we may use lemma\
          <span class="inlinecode"><span class="id"
type="var">lookup\_field\_in\_value</span></span> to show <span
class="inlinecode"><span class="id" type="var">tlookup</span></span>
<span class="inlinecode"><span class="id" type="var">i</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">=</span> <span class="inlinecode"><span
class="id" type="var">Some</span></span> <span class="inlinecode"><span
class="id" type="var">ti</span></span> for\
          some <span class="inlinecode"><span class="id"
type="var">ti</span></span> which gives us <span
class="inlinecode"><span class="id" type="var">tproj</span></span> <span
class="inlinecode"><span class="id" type="var">i</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span>
<span class="inlinecode"><span class="id"
type="var">ti</span></span> by <span class="inlinecode"><span class="id"
type="var">ST\_ProjRcd</span></span>\
          \*)</span>\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">lookup\_field\_in\_value</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>
<span class="id" type="var">H0</span> <span class="id"
type="var">Ht</span> <span class="id" type="var">H</span>) <span
class="id" type="keyword">as</span> [<span class="id"
type="var">ti</span> [<span class="id" type="var">Hlkup</span> <span
class="id" type="var">\_</span>]].\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">ti</span>...\
     <span class="id" type="var">SCase</span> "rcd\_steps".\
       <span class="comment">(\* On the other hand, if <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span>
<span class="inlinecode"><span class="id"
type="var">t'</span></span>, then <span class="inlinecode"><span
class="id" type="var">tproj</span></span> <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
class="id" type="var">i</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">tproj</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> <span
class="inlinecode"><span class="id" type="var">i</span></span>\
          by <span class="inlinecode"><span class="id"
type="var">ST\_Proj1</span></span>. \*)</span>\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t'</span> <span class="id"
type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tproj</span> <span class="id" type="var">t'</span> <span
class="id" type="var">i</span>)...\
   <span class="id" type="var">Case</span> "T\_RNil".\
     <span
class="comment">(\* If the last rule in the given derivation is <span
class="inlinecode"><span class="id"
type="var">T\_RNil</span></span>, then \
        <span class="inlinecode"><span class="id"
type="var">t</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id"
type="var">trnil</span></span>, which is a value. \*)</span>\
     <span class="id" type="var">left</span>...\
   <span class="id" type="var">Case</span> "T\_RCons".\
     <span class="comment">(\* If the last rule is <span
class="inlinecode"><span class="id"
type="var">T\_RCons</span></span>, then <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">trcons</span></span> <span class="inlinecode"><span
class="id" type="var">i</span></span> <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
class="id" type="var">tr</span></span> and\
          <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>\
          <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">tr</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">Tr</span></span>\
        By the IH, each of <span class="inlinecode"><span class="id"
type="var">t</span></span> and <span class="inlinecode"><span class="id"
type="var">tr</span></span> either is a value or can take\
        a step. \*)</span>\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>...\
     <span class="id" type="var">SCase</span> "head is a value".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span>; <span class="id" type="tactic">try</span> <span
class="id" type="tactic">reflexivity</span>.\
       <span class="id" type="var">SSCase</span> "tail is a value".\
       <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">t</span></span> and <span class="inlinecode"><span
class="id" type="var">tr</span></span> are both values, then <span
class="inlinecode"><span class="id" type="var">trcons</span></span>
<span class="inlinecode"><span class="id" type="var">i</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode"><span class="id" type="var">tr</span></span>\
          is a value as well. \*)</span>\
         <span class="id" type="var">left</span>...\
       <span class="id" type="var">SSCase</span> "tail steps".\
         <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">t</span></span> is a value and <span
class="inlinecode"><span class="id" type="var">tr</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span>
<span class="inlinecode"><span class="id"
type="var">tr'</span></span>, then \
            <span class="inlinecode"><span class="id"
type="var">trcons</span></span> <span class="inlinecode"><span
class="id" type="var">i</span></span> <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
class="id" type="var">tr</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">trcons</span></span>
<span class="inlinecode"><span class="id" type="var">i</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode"><span class="id"
type="var">tr'</span></span> by \
            <span class="inlinecode"><span class="id"
type="var">ST\_Rcd\_Tail</span></span>. \*)</span>\
         <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">H2</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">tr'</span> <span class="id" type="var">Hstp</span>].\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">t</span> <span class="id"
type="var">tr'</span>)...\
     <span class="id" type="var">SCase</span> "head steps".\
       <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span>, then \
          <span class="inlinecode"><span class="id"
type="var">trcons</span></span> <span class="inlinecode"><span
class="id" type="var">i</span></span> <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
class="id" type="var">tr</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">trcons</span></span>
<span class="inlinecode"><span class="id" type="var">i</span></span>
<span class="inlinecode"><span class="id" type="var">t'</span></span>
<span class="inlinecode"><span class="id" type="var">tr</span></span> \
          by <span class="inlinecode"><span class="id"
type="var">ST\_Rcd\_Head</span></span>. \*)</span>\
       <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">H1</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">t'</span> <span class="id" type="var">Hstp</span>].\
       <span style="font-family: arial;">∃</span>(<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">t'</span> <span class="id"
type="var">tr</span>)... <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Context Invariance {.section}

</div>

<div class="code code-space">

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
   | <span class="id" type="var">afi\_proj</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">t</span> <span class="id"
type="var">i</span>,\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id" type="var">tproj</span>
<span class="id" type="var">t</span> <span class="id"
type="var">i</span>)\
   | <span class="id" type="var">afi\_rhead</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">i</span> <span class="id"
type="var">ti</span> <span class="id" type="var">tr</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">ti</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">ti</span> <span class="id" type="var">tr</span>)\
   | <span class="id" type="var">afi\_rtail</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">i</span> <span class="id"
type="var">ti</span> <span class="id" type="var">tr</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">tr</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">ti</span> <span class="id" type="var">tr</span>).\
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
type="tactic">intros</span> <span class="id" type="var">y</span> <span
class="id" type="var">Hafi</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span>. <span class="id" type="tactic">destruct</span>
(<span class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span>)...\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_App</span> <span class="id" type="keyword">with</span>
<span class="id" type="var">T~1~</span>...\
   <span class="id" type="var">Case</span> "T\_RCons".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_RCons</span>... <span class="id"
type="keyword">Qed</span>.\
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
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">Hafi</span> <span class="id" type="var">Htyp</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Htyp</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hafi</span>;
<span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHtyp</span> <span class="id" type="keyword">as</span>
[<span class="id" type="var">T'</span> <span class="id"
type="var">Hctx</span>]... <span
style="font-family: arial;">∃</span><span class="id"
type="var">T'</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hctx</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">Hctx</span>...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Preservation {.section}

</div>

<div class="code code-space">

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
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span
class="comment">(\* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then \
      Gamma |- (<span class="inlinecode"><span class="id"
type="var">x</span>:=<span class="id"
type="var">v</span></span>t) S. \*)</span>\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span> <span
class="id" type="var">v</span> <span class="id" type="var">t</span>
<span class="id" type="var">S</span> <span class="id"
type="var">Htypt</span> <span class="id" type="var">Htypv</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">S</span>.\
   <span
class="comment">(\* Proof: By induction on the term t.  Most cases follow directly\
      from the IH, with the exception of tvar, tabs, trcons.\
      The former aren't automatic because we must reason about how the\
      variables interact. In the case of trcons, we must do a little\
      extra work to show that substituting into a term doesn't change\
      whether it is a record term. \*)</span>\
   <span class="id" type="var">t\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">t</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">S</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">Htypt</span>; <span class="id" type="tactic">simpl</span>;
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">Htypt</span>; <span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "tvar".\
     <span class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">rename</span> <span class="id" type="var">i</span> <span
class="id" type="var">into</span> <span class="id" type="var">y</span>.\
     <span class="comment">(\* If t = y, we know that\
          <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">v</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">U</span></span> and\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">S</span></span>\
        and, by inversion, <span class="inlinecode"><span class="id"
type="var">extend</span></span> <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">U</span></span> <span
class="inlinecode"><span class="id" type="var">y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">Some</span></span> <span class="inlinecode"><span class="id"
type="var">S</span></span>.  We want to\
        show that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">y</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">S</span></span>.\
\
        There are two cases to consider: either <span
class="inlinecode"><span class="id" type="var">x</span>=<span class="id"
type="var">y</span></span> or <span class="inlinecode"><span class="id"
type="var">x</span>≠<span class="id"
type="var">y</span></span>. \*)</span>\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>).\
     <span class="id" type="var">SCase</span> "x=y".\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">y</span></span>, then we know that <span
class="inlinecode"><span class="id" type="var">U</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">S</span></span>, and that <span class="inlinecode">[<span
class="id" type="var">x</span>:=<span class="id"
type="var">v</span>]<span class="id" type="var">y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">v</span></span>.\
        So what we really must show is that if <span
class="inlinecode"><span class="id" type="var">empty</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">v</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">U</span></span> then\
        <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">v</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id"
type="var">U</span></span>.  We have already proven a more general version\
        of this theorem, called context invariance. \*)</span>\
       <span class="id" type="tactic">subst</span>.\
       <span class="id" type="tactic">unfold</span> <span class="id"
type="var">extend</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H0</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">eq\_id</span>
<span class="id" type="keyword">in</span> <span class="id"
type="var">H0</span>.\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span>; <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H0</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>...\
       <span class="id" type="tactic">intros</span> <span class="id"
type="var">x</span> <span class="id" type="var">Hcontra</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">free\_in\_context</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">S</span> <span class="id" type="var">empty</span>
<span class="id" type="var">Hcontra</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">T'</span> <span
class="id" type="var">HT'</span>]...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT'</span>.\
     <span class="id" type="var">SCase</span> "x≠y".\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">≠</span>
<span class="inlinecode"><span class="id"
type="var">y</span></span>, then <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span class="id" type="var">y</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">Some</span></span> <span class="inlinecode"><span class="id"
type="var">S</span></span> and the substitution has no\
        effect.  We can show that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">S</span></span> by <span class="inlinecode"><span
class="id" type="var">T\_Var</span></span>. \*)</span>\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Var</span>... <span class="id" type="tactic">unfold</span>
<span class="id" type="var">extend</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H0</span>. <span
class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H0</span>...\
   <span class="id" type="var">Case</span> "tabs".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y</span>. <span class="id"
type="tactic">rename</span> <span class="id" type="var">t</span> <span
class="id" type="var">into</span> <span class="id"
type="var">T~11~</span>.\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">tabs</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span>
<span class="inlinecode"><span class="id" type="var">T~11~</span></span>
<span class="inlinecode"><span class="id"
type="var">t0</span></span>, then we know that\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">tabs</span></span>
<span class="inlinecode"><span class="id" type="var">y</span></span>
<span class="inlinecode"><span class="id" type="var">T~11~</span></span>
<span class="inlinecode"><span class="id" type="var">t0</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T~11~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T~12~</span></span>\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span>,<span
class="id" type="var">y</span>:<span class="id"
type="var">T~11~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~12~</span></span>\
          <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">v</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">U</span></span>\
        As our IH, we know that forall S Gamma, \
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t0</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">S</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t0</span></span> <span class="inlinecode"><span class="id"
type="var">S</span></span>.\
     \
        We can calculate that \
          <span class="inlinecode"><span class="id"
type="var">x</span>:=<span class="id"
type="var">v</span></span>t = tabs y T~11~ (if beq\_id x y then t0 else <span
class="inlinecode"><span class="id" type="var">x</span>:=<span
class="id" type="var">v</span></span>t0)\
        And we must show that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">T~11~</span><span
style="font-family: arial;">→</span><span class="id"
type="var">T~12~</span></span>.  We know\
        we will do so using <span class="inlinecode"><span class="id"
type="var">T\_Abs</span></span>, so it remains to be shown that:\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span></span>
<span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="keyword">if</span></span>
<span class="inlinecode"><span class="id"
type="var">beq\_id</span></span> <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode"><span
class="id" type="var">y</span></span> <span class="inlinecode"><span
class="id" type="keyword">then</span></span> <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode"><span class="id" type="keyword">else</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t0</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">T~12~</span></span>\
        We consider two cases: <span class="inlinecode"><span class="id"
type="var">x</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">y</span></span> and <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode">≠</span> <span class="inlinecode"><span class="id"
type="var">y</span></span>.\
     \*)</span>\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Abs</span>...\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span>).\
     <span class="id" type="var">SCase</span> "x=y".\
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">y</span></span>, then the substitution has no effect.  Context\
        invariance shows that <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">U</span>,<span
class="id" type="var">y</span>:<span class="id"
type="var">T~11~</span></span> and <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span></span> are\
        equivalent.  Since the former context shows that <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~12~</span></span>, so\
        does the latter. \*)</span>\
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
     <span class="comment">(\* If <span class="inlinecode"><span
class="id" type="var">x</span></span> <span class="inlinecode">≠</span>
<span class="inlinecode"><span class="id"
type="var">y</span></span>, then the IH and context invariance allow us to show that\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">x</span>:<span class="id" type="var">U</span>,<span
class="id" type="var">y</span>:<span class="id"
type="var">T~11~</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~12~</span></span>       =\>\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span>,<span
class="id" type="var">x</span>:<span class="id"
type="var">U</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t0</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~12~</span></span>       =\>\
          <span class="inlinecode"><span
style="font-family: serif; font-size:85%;">Γ</span>,<span class="id"
type="var">y</span>:<span class="id" type="var">T~11~</span></span>
<span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v</span>]<span class="id"
type="var">t0</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id"
type="var">T~12~</span></span> \*)</span>\
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
   <span class="id" type="var">Case</span> "trcons".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_RCons</span>... <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H7</span>;
<span class="id" type="tactic">subst</span>; <span class="id"
type="tactic">simpl</span>...\
 <span class="id" type="keyword">Qed</span>.\
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
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">t'</span> <span
class="id" type="var">T</span> <span class="id" type="var">HT</span>.\
   <span class="comment">(\* Theorem: If <span class="inlinecode"><span
class="id" type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span> and <span class="inlinecode"><span class="id"
type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id"
type="var">t'</span></span>, then <span class="inlinecode"><span
class="id" type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span>. \*)</span>\
   <span class="id" type="var">remember</span> (@<span class="id"
type="var">empty</span> <span class="id" type="var">ty</span>) <span
class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>. <span class="id"
type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id"
type="var">HeqGamma</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">t'</span>.\
   <span
class="comment">(\* Proof: By induction on the given typing derivation.  Many cases are\
      contradictory (<span class="inlinecode"><span class="id"
type="var">T\_Var</span></span>, <span class="inlinecode"><span
class="id"
type="var">T\_Abs</span></span>) or follow directly from the IH\
      (<span class="inlinecode"><span class="id"
type="var">T\_RCons</span></span>).  We show just the interesting ones. \*)</span>\
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
     <span class="comment">(\* If the last rule used was <span
class="inlinecode"><span class="id"
type="var">T\_App</span></span>, then <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">t~1~</span></span>
<span class="inlinecode"><span class="id"
type="var">t~2~</span></span>, and three rules\
        could have been used to show <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span>: <span
class="inlinecode"><span class="id"
type="var">ST\_App1</span></span>, <span class="inlinecode"><span
class="id" type="var">ST\_App2</span></span>, and \
        <span class="inlinecode"><span class="id"
type="var">ST\_AppAbs</span></span>. In the first two cases, the result follows directly from \
        the IH. \*)</span>\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HE</span>; <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">SCase</span> "ST\_AppAbs".\
       <span class="comment">(\* For the third case, suppose \
            <span class="inlinecode"><span class="id"
type="var">t~1~</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id" type="var">tabs</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">T~11~</span></span> <span
class="inlinecode"><span class="id" type="var">t~12~</span></span>\
          and\
            <span class="inlinecode"><span class="id"
type="var">t~2~</span></span> <span class="inlinecode">=</span> <span
class="inlinecode"><span class="id"
type="var">v~2~</span></span>.  We must show that <span
class="inlinecode"><span class="id" type="var">empty</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode">[<span class="id" type="var">x</span>:=<span
class="id" type="var">v~2~</span>]<span class="id"
type="var">t~12~</span></span> <span class="inlinecode">:</span> <span
class="inlinecode"><span class="id" type="var">T~2~</span></span>. \
          We know by assumption that\
              <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">tabs</span></span> <span
class="inlinecode"><span class="id" type="var">x</span></span> <span
class="inlinecode"><span class="id" type="var">T~11~</span></span> <span
class="inlinecode"><span class="id" type="var">t~12~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~1~</span><span style="font-family: arial;">→</span><span
class="id" type="var">T~2~</span></span>\
          and by inversion\
              <span class="inlinecode"><span class="id"
type="var">x</span>:<span class="id" type="var">T~1~</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t~12~</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T~2~</span></span>\

         We have already proven that substitution\_preserves\_typing and \
              <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">v~2~</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T~1~</span></span>\
          by assumption, so we are done. \*)</span>\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">substitution\_preserves\_typing</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">T~1~</span>...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT1</span>...\
   <span class="id" type="var">Case</span> "T\_Proj".\
   <span class="comment">(\* If the last rule was <span
class="inlinecode"><span class="id"
type="var">T\_Proj</span></span>, then <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id" type="var">tproj</span></span>
<span class="inlinecode"><span class="id" type="var">t~1~</span></span>
<span class="inlinecode"><span class="id"
type="var">i</span></span>.  Two rules\
      could have caused <span class="inlinecode"><span class="id"
type="var">t</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id" type="var">t'</span></span>: <span
class="inlinecode"><span class="id"
type="var">T\_Proj1</span></span> and <span class="inlinecode"><span
class="id" type="var">T\_ProjRcd</span></span>.  The typing\
      of <span class="inlinecode"><span class="id"
type="var">t'</span></span> follows from the IH in the former case, so we only\
      consider <span class="inlinecode"><span class="id"
type="var">T\_ProjRcd</span></span>.\
\
      Here we have that <span class="inlinecode"><span class="id"
type="var">t</span></span> is a record value.  Since rule T\_Proj was\
      used, we know <span class="inlinecode"><span class="id"
type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">∈</span> <span class="inlinecode"><span class="id"
type="var">Tr</span></span> and <span class="inlinecode"><span
class="id" type="var">Tlookup</span></span> <span
class="inlinecode"><span class="id" type="var">i</span></span> <span
class="inlinecode"><span class="id" type="var">Tr</span></span> <span
class="inlinecode">=</span> <span class="inlinecode"><span class="id"
type="var">Some</span></span> <span class="inlinecode"><span class="id"
type="var">Ti</span></span> for some <span class="inlinecode"><span
class="id" type="var">i</span></span> and <span class="inlinecode"><span
class="id" type="var">Tr</span></span>.  We may therefore apply lemma\
      <span class="inlinecode"><span class="id"
type="var">lookup\_field\_in\_value</span></span> to find the record element this\
      projection steps to. \*)</span>\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">lookup\_field\_in\_value</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>
<span class="id" type="var">H2</span> <span class="id"
type="var">HT</span> <span class="id" type="var">H</span>)\
       <span class="id" type="keyword">as</span> [<span class="id"
type="var">vi</span> [<span class="id" type="var">Hget</span> <span
class="id" type="var">Htyp</span>]].\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H4</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hget</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hget</span>.
<span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "T\_RCons".\
   <span class="comment">(\* If the last rule was <span
class="inlinecode"><span class="id"
type="var">T\_RCons</span></span>, then <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode">=</span>
<span class="inlinecode"><span class="id"
type="var">trcons</span></span> <span class="inlinecode"><span
class="id" type="var">i</span></span> <span class="inlinecode"><span
class="id" type="var">t</span></span> <span class="inlinecode"><span
class="id" type="var">tr</span></span> for\
      some <span class="inlinecode"><span class="id"
type="var">i</span></span>, <span class="inlinecode"><span class="id"
type="var">t</span></span> and <span class="inlinecode"><span class="id"
type="var">tr</span></span> such that <span class="inlinecode"><span
class="id" type="var">record\_tm</span></span> <span
class="inlinecode"><span class="id"
type="var">tr</span></span>.  If the step is\
      by <span class="inlinecode"><span class="id"
type="var">ST\_Rcd\_Head</span></span>, the result is immediate by the IH.  If the step\
      is by <span class="inlinecode"><span class="id"
type="var">ST\_Rcd\_Tail</span></span>, <span class="inlinecode"><span
class="id" type="var">tr</span></span> <span class="inlinecode"><span
style="font-family: arial;">⇒</span></span> <span
class="inlinecode"><span class="id"
type="var">tr2'</span></span> for some <span class="inlinecode"><span
class="id" type="var">tr2'</span></span> and we must also\
      use lemma <span class="inlinecode"><span class="id"
type="var">step\_preserves\_record\_tm</span></span> to show <span
class="inlinecode"><span class="id" type="var">record\_tm</span></span>
<span class="inlinecode"><span class="id"
type="var">tr2'</span></span>. \*)</span>\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_RCons</span>... <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">step\_preserves\_record\_tm</span>...\
 <span class="id" type="keyword">Qed</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">STLCExtendedRecords</span>.\
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
