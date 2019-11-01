<div id="page">

<div id="header">

</div>

<div id="main">

RecordSub<span class="subtitle">Subtyping with Records</span> {.libtitle}
=============================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id"
type="var">MoreStlc</span>.\
\

</div>

<div class="doc">

Core Definitions {.section}
================

</div>

<div class="code code-space">

\

</div>

<div class="doc">

### Syntax {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ty</span> : <span class="id" type="keyword">Type</span> :=\
   <span class="comment">(\* proper types \*)</span>\
   | <span class="id" type="var">TTop</span> : <span class="id"
type="var">ty</span>\
   | <span class="id" type="var">TBase</span> : <span class="id"
type="var">id</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span>\
   | <span class="id" type="var">TArrow</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span>\
   <span class="comment">(\* record types \*)</span>\
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
type="var">c</span> "TTop" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span> "TBase"
| <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "TArrow"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "TRNil" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"TRCons" ].\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">tm</span> : <span class="id" type="keyword">Type</span> :=\
   <span class="comment">(\* proper terms \*)</span>\
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
   | <span class="id" type="var">tproj</span> : <span class="id"
type="var">tm</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">id</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">tm</span>\
   <span class="comment">(\* record terms \*)</span>\
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

### Well-Formedness {.section}

</div>

<div class="code code-space">

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
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">well\_formed\_ty</span> : <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">wfTTop</span> :\
         <span class="id" type="var">well\_formed\_ty</span> <span
class="id" type="var">TTop</span>\
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
class="id" type="var">tr2</span> ⇒ <span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> (<span
class="id" type="tactic">subst</span> <span class="id"
type="var">x</span> <span class="id" type="var">s</span> <span
class="id" type="var">t~1~</span>) (<span class="id"
type="tactic">subst</span> <span class="id" type="var">x</span> <span
class="id" type="var">s</span> <span class="id" type="var">tr2</span>)\
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

</div>

<div class="code code-space">

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
   | <span class="id" type="var">v\_rnil</span> : <span class="id"
type="var">value</span> <span class="id" type="var">trnil</span>\
   | <span class="id" type="var">v\_rcons</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">i</span>
<span class="id" type="var">v</span> <span class="id"
type="var">vr</span>,\
       <span class="id" type="var">value</span> <span class="id"
type="var">v</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">value</span> <span class="id"
type="var">vr</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">value</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">v</span> <span class="id" type="var">vr</span>).\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id"
type="var">value</span>.\
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
   | <span class="id" type="var">ST\_Proj1</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">tr</span> <span class="id" type="var">tr'</span> <span
class="id" type="var">i</span>,\
         <span class="id" type="var">tr</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">tr'</span> <span style="font-family: arial;">→</span>\
         (<span class="id" type="var">tproj</span> <span class="id"
type="var">tr</span> <span class="id" type="var">i</span>) <span
style="font-family: arial;">⇒</span> (<span class="id"
type="var">tproj</span> <span class="id" type="var">tr'</span> <span
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
"ST\_ProjRcd" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "ST\_Rcd"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "ST\_Rcd\_Head" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"ST\_Rcd\_Tail" ].\
\
 <span class="id" type="keyword">Hint</span> <span class="id"
type="var">Constructors</span> <span class="id" type="var">step</span>.\
\

</div>

<div class="doc">

Subtyping {.section}
=========

<div class="paragraph">

</div>

Now we come to the interesting part. We begin by defining the subtyping
relation and developing some of its important technical properties.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Definition {.section}
----------

<div class="paragraph">

</div>

The definition of subtyping is essentially just what we sketched in the
motivating discussion, but we need to add well-formedness side
conditions to some of the rules.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">subtype</span> : <span class="id" type="var">ty</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">ty</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   <span class="comment">(\* Subtyping between proper types \*)</span>\
   | <span class="id" type="var">S\_Refl</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T</span>,\
     <span class="id" type="var">well\_formed\_ty</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">subtype</span> <span class="id"
type="var">T</span> <span class="id" type="var">T</span>\
   | <span class="id" type="var">S\_Trans</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">S</span>
<span class="id" type="var">U</span> <span class="id"
type="var">T</span>,\
     <span class="id" type="var">subtype</span> <span class="id"
type="var">S</span> <span class="id" type="var">U</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">subtype</span> <span class="id"
type="var">U</span> <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">subtype</span> <span class="id"
type="var">S</span> <span class="id" type="var">T</span>\
   | <span class="id" type="var">S\_Top</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">S</span>,\
     <span class="id" type="var">well\_formed\_ty</span> <span
class="id" type="var">S</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">subtype</span> <span class="id"
type="var">S</span> <span class="id" type="var">TTop</span>\
   | <span class="id" type="var">S\_Arrow</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">S~1~</span> <span class="id" type="var">S~2~</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>,\
     <span class="id" type="var">subtype</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">S~1~</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">subtype</span> <span class="id"
type="var">S~2~</span> <span class="id" type="var">T~2~</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">subtype</span> (<span class="id"
type="var">TArrow</span> <span class="id" type="var">S~1~</span> <span
class="id" type="var">S~2~</span>) (<span class="id"
type="var">TArrow</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>)\
   <span class="comment">(\* Subtyping between record types \*)</span>\
   | <span class="id" type="var">S\_RcdWidth</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">i</span>
<span class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>,\
     <span class="id" type="var">well\_formed\_ty</span> (<span
class="id" type="var">TRCons</span> <span class="id" type="var">i</span>
<span class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
     <span class="id" type="var">subtype</span> (<span class="id"
type="var">TRCons</span> <span class="id" type="var">i</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span class="id" type="var">TRNil</span>\
   | <span class="id" type="var">S\_RcdDepth</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">i</span>
<span class="id" type="var">S~1~</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">Sr2</span> <span
class="id" type="var">Tr2</span>,\
     <span class="id" type="var">subtype</span> <span class="id"
type="var">S~1~</span> <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">subtype</span> <span class="id"
type="var">Sr2</span> <span class="id" type="var">Tr2</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">record\_ty</span> <span class="id"
type="var">Sr2</span> <span style="font-family: arial;">→</span>\
     <span class="id" type="var">record\_ty</span> <span class="id"
type="var">Tr2</span> <span style="font-family: arial;">→</span>\
     <span class="id" type="var">subtype</span> (<span class="id"
type="var">TRCons</span> <span class="id" type="var">i</span> <span
class="id" type="var">S~1~</span> <span class="id"
type="var">Sr2</span>) (<span class="id" type="var">TRCons</span> <span
class="id" type="var">i</span> <span class="id" type="var">T~1~</span>
<span class="id" type="var">Tr2</span>)\
   | <span class="id" type="var">S\_RcdPerm</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">i1</span> <span class="id" type="var">i2</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span> <span class="id" type="var">Tr3</span>,\
     <span class="id" type="var">well\_formed\_ty</span> (<span
class="id" type="var">TRCons</span> <span class="id"
type="var">i1</span> <span class="id" type="var">T~1~</span> (<span
class="id" type="var">TRCons</span> <span class="id"
type="var">i2</span> <span class="id" type="var">T~2~</span> <span
class="id" type="var">Tr3</span>)) <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">i1</span> ≠ <span class="id"
type="var">i2</span> <span style="font-family: arial;">→</span>\
     <span class="id" type="var">subtype</span> (<span class="id"
type="var">TRCons</span> <span class="id" type="var">i1</span> <span
class="id" type="var">T~1~</span> (<span class="id"
type="var">TRCons</span> <span class="id" type="var">i2</span> <span
class="id" type="var">T~2~</span> <span class="id"
type="var">Tr3</span>))\
             (<span class="id" type="var">TRCons</span> <span class="id"
type="var">i2</span> <span class="id" type="var">T~2~</span> (<span
class="id" type="var">TRCons</span> <span class="id"
type="var">i1</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">Tr3</span>)).\
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
"S\_Trans" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "S\_Top"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "S\_Arrow" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"S\_RcdWidth"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "S\_RcdDepth" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"S\_RcdPerm" ].\
\

</div>

<div class="doc">

Subtyping Examples and Exercises {.section}
--------------------------------

</div>

<div class="code code-space">

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
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">j</span> := (<span class="id" type="var">Id</span> 3).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">k</span> := (<span class="id" type="var">Id</span> 4).\
 <span class="id" type="keyword">Notation</span> <span class="id"
type="var">i</span> := (<span class="id" type="var">Id</span> 5).\
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
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">TRcd\_j</span> :=\
   (<span class="id" type="var">TRCons</span> <span class="id"
type="var">j</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">B</span> <span class="id" type="var">B</span>)
<span class="id" type="var">TRNil</span>). <span
class="comment">(\* {j:B-\>B} \*)</span>\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">TRcd\_kj</span> :=\
   <span class="id" type="var">TRCons</span> <span class="id"
type="var">k</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">A</span> <span class="id" type="var">A</span>)
<span class="id" type="var">TRcd\_j</span>. <span
class="comment">(\* {k:C-\>C,j:B-\>B} \*)</span>\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">subtyping\_example\_0</span> :\
   <span class="id" type="var">subtype</span> (<span class="id"
type="var">TArrow</span> <span class="id" type="var">C</span> <span
class="id" type="var">TRcd\_kj</span>)\
           (<span class="id" type="var">TArrow</span> <span class="id"
type="var">C</span> <span class="id" type="var">TRNil</span>).\
 <span class="comment">(\* C-\>{k:A-\>A,j:B-\>B} \<: C-\>{} \*)</span>\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">S\_Arrow</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">S\_Refl</span>. <span class="id" type="tactic">auto</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">TRcd\_kj</span>, <span class="id" type="var">TRcd\_j</span>.
<span class="id" type="tactic">apply</span> <span class="id"
type="var">S\_RcdWidth</span>; <span class="id"
type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The following facts are mostly easy to prove in Coq. To get full benefit
from the exercises, make sure you also understand how to prove them on
paper!
<div class="paragraph">

</div>

#### Exercise: 2 stars {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">subtyping\_example\_1</span> :\
   <span class="id" type="var">subtype</span> <span class="id"
type="var">TRcd\_kj</span> <span class="id" type="var">TRcd\_j</span>.\
 <span class="comment">(\* {k:A-\>A,j:B-\>B} \<: {j:B-\>B} \*)</span>\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">subtyping\_example\_2</span> :\
   <span class="id" type="var">subtype</span> (<span class="id"
type="var">TArrow</span> <span class="id" type="var">TTop</span> <span
class="id" type="var">TRcd\_kj</span>)\
           (<span class="id" type="var">TArrow</span> (<span class="id"
type="var">TArrow</span> <span class="id" type="var">C</span> <span
class="id" type="var">C</span>) <span class="id"
type="var">TRcd\_j</span>).\
 <span
class="comment">(\* Top-\>{k:A-\>A,j:B-\>B} \<: (C-\>C)-\>{j:B-\>B} \*)</span>\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">subtyping\_example\_3</span> :\
   <span class="id" type="var">subtype</span> (<span class="id"
type="var">TArrow</span> <span class="id" type="var">TRNil</span> (<span
class="id" type="var">TRCons</span> <span class="id" type="var">j</span>
<span class="id" type="var">A</span> <span class="id"
type="var">TRNil</span>))\
           (<span class="id" type="var">TArrow</span> (<span class="id"
type="var">TRCons</span> <span class="id" type="var">k</span> <span
class="id" type="var">B</span> <span class="id" type="var">TRNil</span>)
<span class="id" type="var">TRNil</span>).\
 <span class="comment">(\* {}-\>{j:A} \<: {k:B}-\>{} \*)</span>\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">subtyping\_example\_4</span> :\
   <span class="id" type="var">subtype</span> (<span class="id"
type="var">TRCons</span> <span class="id" type="var">x</span> <span
class="id" type="var">A</span> (<span class="id"
type="var">TRCons</span> <span class="id" type="var">y</span> <span
class="id" type="var">B</span> (<span class="id"
type="var">TRCons</span> <span class="id" type="var">z</span> <span
class="id" type="var">C</span> <span class="id"
type="var">TRNil</span>)))\
           (<span class="id" type="var">TRCons</span> <span class="id"
type="var">z</span> <span class="id" type="var">C</span> (<span
class="id" type="var">TRCons</span> <span class="id" type="var">y</span>
<span class="id" type="var">B</span> (<span class="id"
type="var">TRCons</span> <span class="id" type="var">x</span> <span
class="id" type="var">A</span> <span class="id"
type="var">TRNil</span>))).\
 <span class="comment">(\* {x:A,y:B,z:C} \<: {z:C,y:B,x:A} \*)</span>\
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
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">trcd\_kj</span> :=\
   (<span class="id" type="var">trcons</span> <span class="id"
type="var">k</span> (<span class="id" type="var">tabs</span> <span
class="id" type="var">z</span> <span class="id" type="var">A</span>
(<span class="id" type="var">tvar</span> <span class="id"
type="var">z</span>))\
            (<span class="id" type="var">trcons</span> <span class="id"
type="var">j</span> (<span class="id" type="var">tabs</span> <span
class="id" type="var">z</span> <span class="id" type="var">B</span>
(<span class="id" type="var">tvar</span> <span class="id"
type="var">z</span>))\
                       <span class="id" type="var">trnil</span>)).\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">Examples</span>.\
\

</div>

<div class="doc">

Properties of Subtyping {.section}
-----------------------

<div class="paragraph">

</div>

### Well-Formedness {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">subtype\_\_wf</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">S</span>
<span class="id" type="var">T</span>,\
   <span class="id" type="var">subtype</span> <span class="id"
type="var">S</span> <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">well\_formed\_ty</span> <span class="id"
type="var">T</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">well\_formed\_ty</span> <span class="id"
type="var">S</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">S</span> <span class="id" type="var">T</span> <span
class="id" type="var">Hsub</span>.\
   <span class="id" type="var">subtype\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Hsub</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">intros</span>; <span class="id"
type="tactic">try</span> (<span class="id" type="tactic">destruct</span>
<span class="id" type="var">IHHsub1</span>; <span class="id"
type="tactic">destruct</span> <span class="id"
type="var">IHHsub2</span>)...\
   <span class="id" type="var">Case</span> "S\_RcdPerm".\
     <span class="id" type="tactic">split</span>... <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>.
<span class="id" type="tactic">subst</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H5</span>...
<span class="id" type="keyword">Qed</span>.\
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
class="id" type="var">i0</span>)... <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H0</span>;
<span class="id" type="tactic">subst</span>... <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Field Lookup {.section}

<div class="paragraph">

</div>

Our record matching lemmas get a little more complicated in the presence
of subtyping for two reasons: First, record types no longer necessarily
describe the exact structure of corresponding terms. Second, reasoning
by induction on <span class="inlinecode"><span class="id"
type="var">has\_type</span></span> derivations becomes harder in
general, because <span class="inlinecode"><span class="id"
type="var">has\_type</span></span> is no longer syntax directed.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">rcd\_types\_match</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">S</span>
<span class="id" type="var">T</span> <span class="id"
type="var">i</span> <span class="id" type="var">Ti</span>,\
   <span class="id" type="var">subtype</span> <span class="id"
type="var">S</span> <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">Tlookup</span> <span class="id"
type="var">i</span> <span class="id" type="var">T</span> = <span
class="id" type="var">Some</span> <span class="id" type="var">Ti</span>
<span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">Si</span>, <span class="id" type="var">Tlookup</span> <span
class="id" type="var">i</span> <span class="id" type="var">S</span> =
<span class="id" type="var">Some</span> <span class="id"
type="var">Si</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">subtype</span> <span class="id"
type="var">Si</span> <span class="id" type="var">Ti</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> (<span class="id" type="tactic">eauto</span>
<span class="id" type="keyword">using</span> <span class="id"
type="var">wf\_rcd\_lookup</span>).\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">S</span> <span class="id" type="var">T</span> <span
class="id" type="var">i</span> <span class="id" type="var">Ti</span>
<span class="id" type="var">Hsub</span> <span class="id"
type="var">Hget</span>. <span class="id" type="tactic">generalize</span>
<span class="id" type="tactic">dependent</span> <span class="id"
type="var">Ti</span>.\
   <span class="id" type="var">subtype\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Hsub</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">Ti</span> <span
class="id" type="var">Hget</span>;\
     <span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
   <span class="id" type="var">Case</span> "S\_Refl".\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">Ti</span>...\
   <span class="id" type="var">Case</span> "S\_Trans".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHHsub2</span> <span class="id" type="var">Ti</span>) <span
class="id" type="keyword">as</span> [<span class="id"
type="var">Ui</span> <span class="id" type="var">Hui</span>]... <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">Hui</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHHsub1</span> <span class="id" type="var">Ui</span>) <span
class="id" type="keyword">as</span> [<span class="id"
type="var">Si</span> <span class="id" type="var">Hsi</span>]... <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">Hsi</span>.\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">Si</span>...\
   <span class="id" type="var">Case</span> "S\_RcdDepth".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i0</span> <span class="id" type="var">into</span> <span
class="id" type="var">k</span>.\
     <span class="id" type="tactic">unfold</span> <span class="id"
type="var">Tlookup</span>. <span class="id" type="tactic">unfold</span>
<span class="id" type="var">Tlookup</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hget</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">i</span> <span
class="id" type="var">k</span>)...\
     <span class="id" type="var">SCase</span> "i = k -- we're looking up
the first field".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hget</span>. <span class="id" type="tactic">subst</span>.
<span style="font-family: arial;">∃</span><span class="id"
type="var">S~1~</span>...\
   <span class="id" type="var">Case</span> "S\_RcdPerm".\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">Ti</span>. <span class="id" type="tactic">split</span>.\
     <span class="id" type="var">SCase</span> "lookup".\
       <span class="id" type="tactic">unfold</span> <span class="id"
type="var">Tlookup</span>. <span class="id" type="tactic">unfold</span>
<span class="id" type="var">Tlookup</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hget</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">i</span> <span
class="id" type="var">i1</span>)...\
       <span class="id" type="var">SSCase</span> "i = i1 -- we're
looking up the first field".\
         <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">i</span> <span class="id" type="var">i2</span>)...\
         <span class="id" type="var">SSSCase</span> "i =
i2 - -contradictory".\
           <span class="id" type="tactic">destruct</span> <span
class="id" type="var">H0</span>.\
           <span class="id" type="tactic">subst</span>...\
     <span class="id" type="var">SCase</span> "subtype".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">H5</span>. <span class="id" type="tactic">subst</span>...
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars (rcd\_types\_match\_informal) {.section}

Write a careful informal proof of the <span class="inlinecode"><span
class="id" type="var">rcd\_types\_match</span></span> lemma.

</div>

<div class="code code-tight">

\
 <span class="comment">(\* FILL IN HERE \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

### Inversion Lemmas {.section}

<div class="paragraph">

</div>

#### Exercise: 3 stars, optional (sub\_inversion\_arrow) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">sub\_inversion\_arrow</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">U</span>
<span class="id" type="var">V1</span> <span class="id"
type="var">V2</span>,\
      <span class="id" type="var">subtype</span> <span class="id"
type="var">U</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">V1</span> <span class="id" type="var">V2</span>)
<span style="font-family: arial;">→</span>\
      <span style="font-family: arial;">∃</span><span class="id"
type="var">U1</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">U2</span>,\
        (<span class="id" type="var">U</span>=(<span class="id"
type="var">TArrow</span> <span class="id" type="var">U1</span> <span
class="id" type="var">U2</span>)) <span
style="font-family: arial;">∧</span> (<span class="id"
type="var">subtype</span> <span class="id" type="var">V1</span> <span
class="id" type="var">U1</span>) <span
style="font-family: arial;">∧</span> (<span class="id"
type="var">subtype</span> <span class="id" type="var">U2</span> <span
class="id" type="var">V2</span>).\
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

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Typing {.section}
======

</div>

<div class="code code-space">

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
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) <span
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
       <span class="id" type="var">has\_type</span> (<span class="id"
type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T~11~</span>) <span
class="id" type="var">t~12~</span> <span class="id"
type="var">T~12~</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">t~12~</span>) (<span class="id" type="var">TArrow</span>
<span class="id" type="var">T~11~</span> <span class="id"
type="var">T~12~</span>)\
   | <span class="id" type="var">T\_App</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span>,\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">T~1~</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) <span class="id"
type="var">T~2~</span>\
   | <span class="id" type="var">T\_Proj</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">i</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span class="id" type="var">Ti</span>,\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">Tlookup</span> <span class="id"
type="var">i</span> <span class="id" type="var">T</span> = <span
class="id" type="var">Some</span> <span class="id" type="var">Ti</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tproj</span> <span class="id" type="var">t</span> <span
class="id" type="var">i</span>) <span class="id" type="var">Ti</span>\
   <span class="comment">(\* Subsumption \*)</span>\
   | <span class="id" type="var">T\_Sub</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">S</span> <span
class="id" type="var">T</span>,\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">S</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">subtype</span> <span class="id"
type="var">S</span> <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span>\
   <span class="comment">(\* Rules for record terms \*)</span>\
   | <span class="id" type="var">T\_RNil</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span>,\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">trnil</span> <span class="id" type="var">TRNil</span>\
   | <span class="id" type="var">T\_RCons</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">i</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span class="id" type="var">tr</span>
<span class="id" type="var">Tr</span>,\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">tr</span> <span class="id" type="var">Tr</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">record\_ty</span> <span class="id"
type="var">Tr</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">record\_tm</span> <span class="id"
type="var">tr</span> <span style="font-family: arial;">→</span>\
       <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">t</span> <span class="id" type="var">tr</span>)
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
"T\_Sub"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "T\_RNil" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"T\_RCons" ].\
\

</div>

<div class="doc">

Typing Examples {.section}
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

#### Exercise: 1 star {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_example\_0</span> :\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span>\
            (<span class="id" type="var">trcons</span> <span class="id"
type="var">k</span> (<span class="id" type="var">tabs</span> <span
class="id" type="var">z</span> <span class="id" type="var">A</span>
(<span class="id" type="var">tvar</span> <span class="id"
type="var">z</span>))\
                      (<span class="id" type="var">trcons</span> <span
class="id" type="var">j</span> (<span class="id" type="var">tabs</span>
<span class="id" type="var">z</span> <span class="id"
type="var">B</span> (<span class="id" type="var">tvar</span> <span
class="id" type="var">z</span>))\
                                <span class="id"
type="var">trnil</span>))\
            <span class="id" type="var">TRcd\_kj</span>.\
 <span
class="comment">(\* empty |- {k=(\\z:A.z), j=(\\z:B.z)} : {k:A-\>A,j:B-\>B} \*)</span>\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_example\_1</span> :\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span>\
            (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">TRcd\_j</span> (<span class="id"
type="var">tproj</span> (<span class="id" type="var">tvar</span> <span
class="id" type="var">x</span>) <span class="id" type="var">j</span>))\
                    (<span class="id" type="var">trcd\_kj</span>))\
            (<span class="id" type="var">TArrow</span> <span class="id"
type="var">B</span> <span class="id" type="var">B</span>).\
 <span
class="comment">(\* empty |- (\\x:{k:A-\>A,j:B-\>B}. x.j) {k=(\\z:A.z), j=(\\z:B.z)} : B-\>B \*)</span>\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Example</span> <span class="id"
type="var">typing\_example\_2</span> :\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span>\
            (<span class="id" type="var">tapp</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">z</span> (<span
class="id" type="var">TArrow</span> (<span class="id"
type="var">TArrow</span> <span class="id" type="var">C</span> <span
class="id" type="var">C</span>) <span class="id"
type="var">TRcd\_j</span>)\
                            (<span class="id" type="var">tproj</span>
(<span class="id" type="var">tapp</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">z</span>)\
                                             (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">C</span> (<span class="id" type="var">tvar</span>
<span class="id" type="var">x</span>)))\
                                     <span class="id"
type="var">j</span>))\
                    (<span class="id" type="var">tabs</span> <span
class="id" type="var">z</span> (<span class="id"
type="var">TArrow</span> <span class="id" type="var">C</span> <span
class="id" type="var">C</span>) <span class="id"
type="var">trcd\_kj</span>))\
            (<span class="id" type="var">TArrow</span> <span class="id"
type="var">B</span> <span class="id" type="var">B</span>).\
 <span
class="comment">(\* empty |- (\\z:(C-\>C)-\>{j:B-\>B}. (z (\\x:C.x)).j)\
               (\\z:C-\>C. {k=(\\z:A.z), j=(\\z:B.z)})\
            : B-\>B \*)</span>\
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
type="var">Examples2</span>.\
\

</div>

<div class="doc">

Properties of Typing {.section}
--------------------

<div class="paragraph">

</div>

### Well-Formedness {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">has\_type\_\_wf</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span>,\
   <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
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
   <span class="id" type="var">Case</span> "T\_Sub".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">subtype\_\_wf</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span>...\
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
<span class="id" type="tactic">eauto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Field Lookup {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">lookup\_field\_in\_value</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">v</span>
<span class="id" type="var">T</span> <span class="id"
type="var">i</span> <span class="id" type="var">Ti</span>,\
   <span class="id" type="var">value</span> <span class="id"
type="var">v</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">v</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">Tlookup</span> <span class="id"
type="var">i</span> <span class="id" type="var">T</span> = <span
class="id" type="var">Some</span> <span class="id" type="var">Ti</span>
<span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">vi</span>, <span class="id" type="var">tlookup</span> <span
class="id" type="var">i</span> <span class="id" type="var">v</span> =
<span class="id" type="var">Some</span> <span class="id"
type="var">vi</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">vi</span> <span
class="id" type="var">Ti</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="var">remember</span> <span class="id"
type="var">empty</span> <span class="id" type="keyword">as</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
class="id" type="var">i</span> <span class="id" type="var">Ti</span>
<span class="id" type="var">Hval</span> <span class="id"
type="var">Htyp</span>. <span class="id" type="var">revert</span> <span
class="id" type="var">Ti</span> <span class="id"
type="var">HeqGamma</span> <span class="id" type="var">Hval</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Htyp</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span>; <span class="id"
type="tactic">subst</span>; <span class="id" type="tactic">try</span>
<span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
   <span class="id" type="var">Case</span> "T\_Sub".\
     <span class="id" type="tactic">apply</span> (<span class="id"
type="var">rcd\_types\_match</span> <span class="id"
type="var">S</span>) <span class="id" type="keyword">in</span> <span
class="id" type="var">H0</span>... <span class="id"
type="tactic">destruct</span> <span class="id" type="var">H0</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">Si</span> [<span class="id" type="var">HgetSi</span> <span
class="id" type="var">Hsub</span>]].\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHHtyp</span> <span class="id" type="var">Si</span>) <span
class="id" type="keyword">as</span> [<span class="id"
type="var">vi</span> [<span class="id" type="var">Hget</span> <span
class="id" type="var">Htyvi</span>]]...\
   <span class="id" type="var">Case</span> "T\_RCons".\
     <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H0</span>. <span
class="id" type="tactic">simpl</span>. <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H1</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">i</span> <span
class="id" type="var">i0</span>).\
     <span class="id" type="var">SCase</span> "i is first".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H1</span>. <span class="id" type="tactic">subst</span>. <span
style="font-family: arial;">∃</span><span class="id"
type="var">t</span>...\
     <span class="id" type="var">SCase</span> "i in tail".\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHHtyp2</span> <span class="id" type="var">Ti</span>) <span
class="id" type="keyword">as</span> [<span class="id"
type="var">vi</span> [<span class="id" type="var">get</span> <span
class="id" type="var">Htyvi</span>]]...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hval</span>... <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

### Progress {.section}

<div class="paragraph">

</div>

#### Exercise: 3 stars (canonical\_forms\_of\_arrow\_types) {.section}

</div>

<div class="code code-space">

<span class="id" type="keyword">Lemma</span> <span class="id"
type="var">canonical\_forms\_of\_arrow\_types</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">s</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
      <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">s</span> (<span class="id" type="var">TArrow</span> <span
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

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="tactic">progress</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">T</span>,\
      <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">value</span> <span class="id"
type="var">t</span> <span style="font-family: arial;">∨</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">t'</span>, <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span>.\
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
         <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~2~'</span> <span class="id"
type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~'</span>)...\
     <span class="id" type="var">SCase</span> "t~1~ steps".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t~1~'</span> <span class="id"
type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~'</span> <span
class="id" type="var">t~2~</span>)...\
   <span class="id" type="var">Case</span> "T\_Proj".\
     <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id"
type="var">IHHt</span>...\
     <span class="id" type="var">SCase</span> "rcd is value".\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">lookup\_field\_in\_value</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
class="id" type="var">i</span> <span class="id" type="var">Ti</span>)
<span class="id" type="keyword">as</span> [<span class="id"
type="var">t'</span> [<span class="id" type="var">Hget</span> <span
class="id" type="var">Ht'</span>]]...\
     <span class="id" type="var">SCase</span> "rcd\_steps".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">t'</span> <span class="id"
type="var">Hstp</span>]. <span
style="font-family: arial;">∃</span>(<span class="id"
type="var">tproj</span> <span class="id" type="var">t'</span> <span
class="id" type="var">i</span>)...\
   <span class="id" type="var">Case</span> "T\_RCons".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt1</span>...\
     <span class="id" type="var">SCase</span> "head is a value".\
       <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHHt2</span>...\
       <span class="id" type="var">SSCase</span> "tail steps".\
         <span class="id" type="var">right</span>. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">H2</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">tr'</span> <span class="id" type="var">Hstp</span>].\
         <span style="font-family: arial;">∃</span>(<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">t</span> <span class="id"
type="var">tr'</span>)...\
     <span class="id" type="var">SCase</span> "head steps".\
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

Informal proof of progress:
<div class="paragraph">

</div>

Theorem : For any term <span class="inlinecode"><span class="id"
type="var">t</span></span> and type <span class="inlinecode"><span
class="id" type="var">T</span></span>, if <span class="inlinecode"><span
class="id" type="var">empty</span></span> <span class="inlinecode"><span
style="font-family: arial;">⊢</span></span> <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode">:</span> <span class="inlinecode"><span class="id"
type="var">T</span></span> then <span class="inlinecode"><span
class="id" type="var">t</span></span> is a value or <span
class="inlinecode"><span class="id" type="var">t</span></span> <span
class="inlinecode"><span style="font-family: arial;">⇒</span></span>
<span class="inlinecode"><span class="id" type="var">t'</span></span>
for some term <span class="inlinecode"><span class="id"
type="var">t'</span></span>.
<div class="paragraph">

</div>

Proof : Let <span class="inlinecode"><span class="id"
type="var">t</span></span> and <span class="inlinecode"><span class="id"
type="var">T</span></span> be given such that <span
class="inlinecode"><span class="id" type="var">empty</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>. We go by induction on the typing
derivation. Cases <span class="inlinecode"><span class="id"
type="var">T\_Abs</span></span> and <span class="inlinecode"><span
class="id" type="var">T\_RNil</span></span> are immediate because
abstractions and <span class="inlinecode">{}</span> are always values.
Case <span class="inlinecode"><span class="id"
type="var">T\_Var</span></span> is vacuous because variables cannot be
typed in the empty context.
<div class="paragraph">

</div>

-   If the last step in the typing derivation is by <span
    class="inlinecode"><span class="id" type="var">T\_App</span></span>,
    then there are terms <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> and types <span
    class="inlinecode"><span class="id" type="var">T~1~</span></span>
    <span class="inlinecode"><span class="id"
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
    type="var">T~2~</span></span> and <span class="inlinecode"><span
    class="id" type="var">empty</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> <span class="inlinecode">:</span>
    <span class="inlinecode"><span class="id"
    type="var">T~1~</span></span>.
    <div class="paragraph">

    </div>

    The induction hypotheses for these typing derivations yield that
    <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> is a value or steps, and that <span
    class="inlinecode"><span class="id" type="var">t~2~</span></span> is
    a value or steps. We consider each case:
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

    -   Otherwise <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> is a value.
        <div class="paragraph">

        </div>

        -   Suppose <span class="inlinecode"><span class="id"
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

        -   Otherwise, <span class="inlinecode"><span class="id"
            type="var">t~2~</span></span> is a value. By lemma <span
            class="inlinecode"><span class="id"
            type="var">canonical\_forms\_for\_arrow\_types</span></span>,
            <span class="inlinecode"><span class="id"
            type="var">t~1~</span></span> <span
            class="inlinecode">=</span> <span class="inlinecode">\\<span
            class="id" type="var">x</span>:<span class="id"
            type="var">S~1~.s~2~</span></span> for some <span
            class="inlinecode"><span class="id"
            type="var">x</span></span>, <span class="inlinecode"><span
            class="id" type="var">S~1~</span></span>, and <span
            class="inlinecode"><span class="id"
            type="var">s~2~</span></span>. And <span
            class="inlinecode">(\\<span class="id"
            type="var">x</span>:<span class="id"
            type="var">S~1~.s~2~</span>)</span> <span
            class="inlinecode"><span class="id"
            type="var">t~2~</span></span> <span class="inlinecode"><span
            style="font-family: arial;">⇒</span></span> <span
            class="inlinecode">[<span class="id"
            type="var">x</span>:=<span class="id"
            type="var">t~2~</span>]<span class="id"
            type="var">s~2~</span></span> by <span
            class="inlinecode"><span class="id"
            type="var">ST\_AppAbs</span></span>, since <span
            class="inlinecode"><span class="id"
            type="var">t~2~</span></span> is a value.
            <div class="paragraph">

            </div>
-   If the last step of the derivation is by <span
    class="inlinecode"><span class="id"
    type="var">T\_Proj</span></span>, then there is a term <span
    class="inlinecode"><span class="id" type="var">tr</span></span>,
    type <span class="inlinecode"><span class="id"
    type="var">Tr</span></span> and label <span class="inlinecode"><span
    class="id" type="var">i</span></span> such that <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">tr.i</span></span>, <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">tr</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">Tr</span></span>, and <span
    class="inlinecode"><span class="id" type="var">Tlookup</span></span>
    <span class="inlinecode"><span class="id" type="var">i</span></span>
    <span class="inlinecode"><span class="id"
    type="var">Tr</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">Some</span></span>
    <span class="inlinecode"><span class="id"
    type="var">T</span></span>.
    <div class="paragraph">

    </div>

    The IH for the typing subderivation gives us that either <span
    class="inlinecode"><span class="id" type="var">tr</span></span> is a
    value or it steps. If <span class="inlinecode"><span class="id"
    type="var">tr</span></span> <span class="inlinecode"><span
    style="font-family: arial;">⇒</span></span> <span
    class="inlinecode"><span class="id" type="var">tr'</span></span> for
    some term <span class="inlinecode"><span class="id"
    type="var">tr'</span></span>, then <span class="inlinecode"><span
    class="id" type="var">tr.i</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⇒</span></span>
    <span class="inlinecode"><span class="id"
    type="var">tr'.i</span></span> by rule <span
    class="inlinecode"><span class="id"
    type="var">ST\_Proj1</span></span>.
    <div class="paragraph">

    </div>

    Otherwise, <span class="inlinecode"><span class="id"
    type="var">tr</span></span> is a value. In this case, lemma <span
    class="inlinecode"><span class="id"
    type="var">lookup\_field\_in\_value</span></span> yields that there
    is a term <span class="inlinecode"><span class="id"
    type="var">ti</span></span> such that <span class="inlinecode"><span
    class="id" type="var">tlookup</span></span> <span
    class="inlinecode"><span class="id" type="var">i</span></span> <span
    class="inlinecode"><span class="id" type="var">tr</span></span>
    <span class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">Some</span></span> <span
    class="inlinecode"><span class="id" type="var">ti</span></span>. It
    follows that <span class="inlinecode"><span class="id"
    type="var">tr.i</span></span> <span class="inlinecode"><span
    style="font-family: arial;">⇒</span></span> <span
    class="inlinecode"><span class="id" type="var">ti</span></span> by
    rule <span class="inlinecode"><span class="id"
    type="var">ST\_ProjRcd</span></span>.
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
    <div class="paragraph">

    </div>

-   If the final step of the derivation is by <span
    class="inlinecode"><span class="id"
    type="var">T\_RCons</span></span>, then there exist some terms <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">tr</span></span>, types <span class="inlinecode"><span
    class="id" type="var">T~1~</span></span> <span
    class="inlinecode"><span class="id" type="var">Tr</span></span> and
    a label <span class="inlinecode"><span class="id"
    type="var">t</span></span> such that <span class="inlinecode"><span
    class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode">{<span
    class="id" type="var">i</span>=<span class="id"
    type="var">t~1~</span>,</span> <span class="inlinecode"><span
    class="id" type="var">tr</span>}</span>, <span
    class="inlinecode"><span class="id" type="var">T</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode">{<span
    class="id" type="var">i</span>:<span class="id"
    type="var">T~1~</span>,</span> <span class="inlinecode"><span
    class="id" type="var">Tr</span>}</span>, <span
    class="inlinecode"><span class="id"
    type="var">record\_tm</span></span> <span class="inlinecode"><span
    class="id" type="var">tr</span></span>, <span
    class="inlinecode"><span class="id"
    type="var">record\_tm</span></span> <span class="inlinecode"><span
    class="id" type="var">Tr</span></span>, <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">T~1~</span></span> and <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">tr</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">Tr</span></span>.
    <div class="paragraph">

    </div>

    The induction hypotheses for these typing derivations yield that
    <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> is a value or steps, and that <span
    class="inlinecode"><span class="id" type="var">tr</span></span> is a
    value or steps. We consider each case:
    <div class="paragraph">

    </div>

    -   Suppose <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> <span class="inlinecode"><span
        style="font-family: arial;">⇒</span></span> <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span> for some term <span
        class="inlinecode"><span class="id"
        type="var">t~1~'</span></span>. Then <span
        class="inlinecode">{<span class="id" type="var">i</span>=<span
        class="id" type="var">t~1~</span>,</span> <span
        class="inlinecode"><span class="id" type="var">tr</span>}</span>
        <span class="inlinecode"><span
        style="font-family: arial;">⇒</span></span> <span
        class="inlinecode">{<span class="id" type="var">i</span>=<span
        class="id" type="var">t~1~'</span>,</span> <span
        class="inlinecode"><span class="id" type="var">tr</span>}</span>
        by rule <span class="inlinecode"><span class="id"
        type="var">ST\_Rcd\_Head</span></span>.
        <div class="paragraph">

        </div>

    -   Otherwise <span class="inlinecode"><span class="id"
        type="var">t~1~</span></span> is a value.
        <div class="paragraph">

        </div>

        -   Suppose <span class="inlinecode"><span class="id"
            type="var">tr</span></span> <span class="inlinecode"><span
            style="font-family: arial;">⇒</span></span> <span
            class="inlinecode"><span class="id"
            type="var">tr'</span></span> for some term <span
            class="inlinecode"><span class="id"
            type="var">tr'</span></span>. Then <span
            class="inlinecode">{<span class="id"
            type="var">i</span>=<span class="id"
            type="var">t~1~</span>,</span> <span
            class="inlinecode"><span class="id"
            type="var">tr</span>}</span> <span class="inlinecode"><span
            style="font-family: arial;">⇒</span></span> <span
            class="inlinecode">{<span class="id"
            type="var">i</span>=<span class="id"
            type="var">t~1~</span>,</span> <span
            class="inlinecode"><span class="id"
            type="var">tr'</span>}</span> by rule <span
            class="inlinecode"><span class="id"
            type="var">ST\_Rcd\_Tail</span></span>, since <span
            class="inlinecode"><span class="id"
            type="var">t~1~</span></span> is a value.
            <div class="paragraph">

            </div>

        -   Otherwise, <span class="inlinecode"><span class="id"
            type="var">tr</span></span> is also a value. So, <span
            class="inlinecode">{<span class="id"
            type="var">i</span>=<span class="id"
            type="var">t~1~</span>,</span> <span
            class="inlinecode"><span class="id"
            type="var">tr</span>}</span> is a value by <span
            class="inlinecode"><span class="id"
            type="var">v\_rcons</span></span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

### Inversion Lemmas {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_inversion\_var</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">T</span>,\
   <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tvar</span> <span class="id" type="var">x</span>) <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">S</span>,\
     <span style="font-family: serif; font-size:85%;">Γ</span> <span
class="id" type="var">x</span> = <span class="id" type="var">Some</span>
<span class="id" type="var">S</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">subtype</span> <span class="id" type="var">S</span> <span
class="id" type="var">T</span>.\
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
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_inversion\_app</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> <span
class="id" type="var">T~2~</span>,\
   <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tapp</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">t~2~</span>) <span class="id"
type="var">T~2~</span> <span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">T~1~</span>,\
     <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">T~1~</span> <span class="id"
type="var">T~2~</span>) <span style="font-family: arial;">∧</span>\
     <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">T~1~</span>.\
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
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">Hwf</span> := <span class="id"
type="var">has\_type\_\_wf</span> <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span> <span class="id"
type="var">\_</span> <span class="id" type="var">Hty2</span>).\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">U1</span>... <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_inversion\_abs</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">S~1~</span> <span
class="id" type="var">t~2~</span> <span class="id" type="var">T</span>,\
      <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tabs</span> <span class="id" type="var">x</span> <span
class="id" type="var">S~1~</span> <span class="id"
type="var">t~2~</span>) <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
      (<span style="font-family: arial;">∃</span><span class="id"
type="var">S~2~</span>, <span class="id" type="var">subtype</span>
(<span class="id" type="var">TArrow</span> <span class="id"
type="var">S~1~</span> <span class="id" type="var">S~2~</span>) <span
class="id" type="var">T</span>\
               <span style="font-family: arial;">∧</span> <span
class="id" type="var">has\_type</span> (<span class="id"
type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">S~1~</span>) <span
class="id" type="var">t~2~</span> <span class="id"
type="var">S~2~</span>).\
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
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">Hwf</span> := <span class="id"
type="var">has\_type\_\_wf</span> <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span> <span class="id"
type="var">\_</span> <span class="id" type="var">H0</span>).\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">T~12~</span>...\
   <span class="id" type="var">Case</span> "T\_Sub".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHhas\_type</span> <span class="id" type="keyword">as</span>
[<span class="id" type="var">S~2~</span> [<span class="id"
type="var">Hsub</span> <span class="id" type="var">Hty</span>]]...\
     <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_inversion\_proj</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">i</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">Ti</span>,\
   <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">tproj</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">i</span>) <span class="id" type="var">Ti</span>
<span style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">T</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">Si</span>,\
     <span class="id" type="var">Tlookup</span> <span class="id"
type="var">i</span> <span class="id" type="var">T</span> = <span
class="id" type="var">Some</span> <span class="id" type="var">Si</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">subtype</span> <span class="id" type="var">Si</span> <span
class="id" type="var">Ti</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">i</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">Ti</span> <span class="id" type="var">H</span>.\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">tproj</span> <span class="id" type="var">t~1~</span> <span
class="id" type="var">i</span>) <span class="id"
type="keyword">as</span> <span class="id" type="var">t</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">H</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heqt</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">intros</span>; <span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
   <span class="id" type="var">Case</span> "T\_Proj".\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">well\_formed\_ty</span> <span class="id"
type="var">Ti</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">Hwf</span>.\
       <span class="id" type="var">SCase</span> "pf of assertion".\
         <span class="id" type="tactic">apply</span> (<span class="id"
type="var">wf\_rcd\_lookup</span> <span class="id" type="var">i</span>
<span class="id" type="var">T</span> <span class="id"
type="var">Ti</span>)...\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">has\_type\_\_wf</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H</span>...\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">T</span>. <span style="font-family: arial;">∃</span><span
class="id" type="var">Ti</span>...\
   <span class="id" type="var">Case</span> "T\_Sub".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">IHhas\_type</span> <span class="id" type="keyword">as</span>
[<span class="id" type="var">U</span> [<span class="id"
type="var">Ui</span> [<span class="id" type="var">Hget</span> [<span
class="id" type="var">Hsub</span> <span class="id"
type="var">Hty</span>]]]]...\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">U</span>. <span style="font-family: arial;">∃</span><span
class="id" type="var">Ui</span>... <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">typing\_inversion\_rcons</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">i</span> <span class="id" type="var">ti</span> <span
class="id" type="var">tr</span> <span class="id" type="var">T</span>,\
   <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">ti</span> <span class="id" type="var">tr</span>)
<span class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
   <span style="font-family: arial;">∃</span><span class="id"
type="var">Si</span>, <span style="font-family: arial;">∃</span><span
class="id" type="var">Sr</span>,\
     <span class="id" type="var">subtype</span> (<span class="id"
type="var">TRCons</span> <span class="id" type="var">i</span> <span
class="id" type="var">Si</span> <span class="id" type="var">Sr</span>)
<span class="id" type="var">T</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">ti</span> <span class="id" type="var">Si</span> <span
style="font-family: arial;">∧</span>\
     <span class="id" type="var">record\_tm</span> <span class="id"
type="var">tr</span> <span style="font-family: arial;">∧</span> <span
class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">tr</span> <span class="id" type="var">Sr</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">i</span> <span class="id" type="var">ti</span> <span
class="id" type="var">tr</span> <span class="id" type="var">T</span>
<span class="id" type="var">Hty</span>.\
   <span class="id" type="var">remember</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">ti</span> <span class="id" type="var">tr</span>)
<span class="id" type="keyword">as</span> <span class="id"
type="var">t</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Hty</span>)
<span class="id" type="var">Case</span>;\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heqt</span>; <span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "T\_Sub".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHHty</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">H0</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">H0</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">Ri</span> [<span class="id" type="var">Rr</span>
[<span class="id" type="var">HsubRS</span> [<span class="id"
type="var">HtypRi</span> <span class="id" type="var">HtypRr</span>]]]].\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">Ri</span>. <span style="font-family: arial;">∃</span><span
class="id" type="var">Rr</span>...\
   <span class="id" type="var">Case</span> "T\_RCons".\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">well\_formed\_ty</span> (<span class="id"
type="var">TRCons</span> <span class="id" type="var">i</span> <span
class="id" type="var">T</span> <span class="id" type="var">Tr</span>))
<span class="id" type="keyword">as</span> <span class="id"
type="var">Hwf</span>.\
       <span class="id" type="var">SCase</span> "pf of assertion".\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">has\_type\_\_wf</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hty1</span>.\
         <span class="id" type="tactic">apply</span> <span class="id"
type="var">has\_type\_\_wf</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hty2</span>...\
     <span style="font-family: arial;">∃</span><span class="id"
type="var">T</span>. <span style="font-family: arial;">∃</span><span
class="id" type="var">Tr</span>... <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">abs\_arrow</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">S~1~</span> <span class="id"
type="var">s~2~</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>,\
   <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> (<span class="id" type="var">tabs</span> <span
class="id" type="var">x</span> <span class="id" type="var">S~1~</span>
<span class="id" type="var">s~2~</span>) (<span class="id"
type="var">TArrow</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>) <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">subtype</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">S~1~</span>\
   <span style="font-family: arial;">∧</span> <span class="id"
type="var">has\_type</span> (<span class="id" type="var">extend</span>
<span class="id" type="var">empty</span> <span class="id"
type="var">x</span> <span class="id" type="var">S~1~</span>) <span
class="id" type="var">s~2~</span> <span class="id"
type="var">T~2~</span>.\
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
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">Hty</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">S~2~</span> [<span class="id"
type="var">Hsub</span> <span class="id" type="var">Hty</span>]].\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">sub\_inversion\_arrow</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hsub</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">Hsub</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">U1</span> [<span class="id" type="var">U2</span>
[<span class="id" type="var">Heq</span> [<span class="id"
type="var">Hsub1</span> <span class="id" type="var">Hsub2</span>]]]].\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Heq</span>; <span class="id" type="tactic">subst</span>...
<span class="id" type="keyword">Qed</span>.\
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
type="var">t</span> <span class="id" type="var">tr</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">t</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">t</span> <span class="id" type="var">tr</span>)\
   | <span class="id" type="var">afi\_rtail</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">x</span>
<span class="id" type="var">i</span> <span class="id"
type="var">t</span> <span class="id" type="var">tr</span>,\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> <span class="id" type="var">tr</span>
<span style="font-family: arial;">→</span>\
       <span class="id" type="var">appears\_free\_in</span> <span
class="id" type="var">x</span> (<span class="id"
type="var">trcons</span> <span class="id" type="var">i</span> <span
class="id" type="var">t</span> <span class="id" type="var">tr</span>).\
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
      <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">S</span> <span
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
      <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ'</span> <span class="id"
type="var">t</span> <span class="id" type="var">S</span>.\
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
    <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
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
type="tactic">subst</span>; <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hafi</span>;
<span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "T\_Abs".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">IHHtyp</span> <span class="id" type="var">H5</span>) <span
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
      <span class="id" type="var">has\_type</span> (<span class="id"
type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="var">U</span>) <span
class="id" type="var">t</span> <span class="id" type="var">S</span>
<span style="font-family: arial;">→</span>\
      <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">v</span> <span
class="id" type="var">U</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> ([<span class="id"
type="var">x</span>:=<span class="id" type="var">v</span>]<span
class="id" type="var">t</span>) <span class="id" type="var">S</span>.\
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
type="var">Htypt</span>) <span class="id" type="keyword">as</span>
[<span class="id" type="var">T</span> [<span class="id"
type="var">Hctx</span> <span class="id" type="var">Hsub</span>]].\
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
<span class="id" type="var">Hcontra</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">T'</span> <span
class="id" type="var">HT'</span>]...\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">HT'</span>.\
     <span class="id" type="var">SCase</span> "x≠y".\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">subtype\_\_wf</span> <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span> <span class="id"
type="var">Hsub</span>)...\
   <span class="id" type="var">Case</span> "tapp".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">typing\_inversion\_app</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>
<span class="id" type="var">Htypt</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">T~1~</span> [<span
class="id" type="var">Htypt1</span> <span class="id"
type="var">Htypt2</span>]].\
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
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">subtype\_\_wf</span> <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span> <span class="id"
type="var">Hsub</span>) <span class="id" type="keyword">as</span> [<span
class="id" type="var">Hwf1</span> <span class="id"
type="var">Hwf2</span>].\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hwf2</span>. <span class="id" type="tactic">subst</span>.\
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
   <span class="id" type="var">Case</span> "tproj".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">typing\_inversion\_proj</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>
<span class="id" type="var">Htypt</span>)\
       <span class="id" type="keyword">as</span> [<span class="id"
type="var">T</span> [<span class="id" type="var">Ti</span> [<span
class="id" type="var">Hget</span> [<span class="id"
type="var">Hsub</span> <span class="id" type="var">Htypt1</span>]]]]...\
   <span class="id" type="var">Case</span> "trnil".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">context\_invariance</span>...\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">y</span> <span class="id" type="var">Hcontra</span>. <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">Hcontra</span>.\
   <span class="id" type="var">Case</span> "trcons".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">typing\_inversion\_rcons</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>
<span class="id" type="var">\_</span> <span class="id"
type="var">Htypt</span>) <span class="id" type="keyword">as</span>\
       [<span class="id" type="var">Ti</span> [<span class="id"
type="var">Tr</span> [<span class="id" type="var">Hsub</span> [<span
class="id" type="var">HtypTi</span> [<span class="id"
type="var">Hrcdt2</span> <span class="id"
type="var">HtypTr</span>]]]]].\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_Sub</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">TRCons</span> <span class="id"
type="var">i</span> <span class="id" type="var">Ti</span> <span
class="id" type="var">Tr</span>)...\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">T\_RCons</span>...\
     <span class="id" type="var">SCase</span> "record\_ty Tr".\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">subtype\_\_wf</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hsub</span>. <span
class="id" type="tactic">destruct</span> <span class="id"
type="var">Hsub</span>. <span class="id" type="tactic">inversion</span>
<span class="id" type="var">H0</span>...\
     <span class="id" type="var">SCase</span> "record\_tm
([x:=v]t~2~)".\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hrcdt2</span>; <span class="id" type="tactic">subst</span>;
<span class="id" type="tactic">simpl</span>... <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">preservation</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">t</span>
<span class="id" type="var">t'</span> <span class="id"
type="var">T</span>,\
      <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">t</span> <span
style="font-family: arial;">⇒</span> <span class="id"
type="var">t'</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">has\_type</span> <span class="id"
type="var">empty</span> <span class="id" type="var">t'</span> <span
class="id" type="var">T</span>.\
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
   <span class="id" type="var">Case</span> "T\_Proj".\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">lookup\_field\_in\_value</span> <span class="id"
type="var">\_</span> <span class="id" type="var">\_</span> <span
class="id" type="var">\_</span> <span class="id" type="var">\_</span>
<span class="id" type="var">H2</span> <span class="id"
type="var">HT</span> <span class="id" type="var">H</span>)\
       <span class="id" type="keyword">as</span> [<span class="id"
type="var">vi</span> [<span class="id" type="var">Hget</span> <span
class="id" type="var">Hty</span>]].\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">H4</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">Hget</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hget</span>.
<span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "T\_RCons".\
     <span class="id" type="tactic">eauto</span> <span class="id"
type="keyword">using</span> <span class="id"
type="var">step\_preserves\_record\_tm</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Informal proof of <span class="inlinecode"><span class="id"
type="var">preservation</span></span>:
<div class="paragraph">

</div>

Theorem: If <span class="inlinecode"><span class="id"
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

Proof: Let <span class="inlinecode"><span class="id"
type="var">t</span></span> and <span class="inlinecode"><span class="id"
type="var">T</span></span> be given such that <span
class="inlinecode"><span class="id" type="var">empty</span></span> <span
class="inlinecode"><span style="font-family: arial;">⊢</span></span>
<span class="inlinecode"><span class="id" type="var">t</span></span>
<span class="inlinecode">:</span> <span class="inlinecode"><span
class="id" type="var">T</span></span>. We go by induction on the
structure of this typing derivation, leaving <span
class="inlinecode"><span class="id" type="var">t'</span></span> general.
Cases <span class="inlinecode"><span class="id"
type="var">T\_Abs</span></span> and <span class="inlinecode"><span
class="id" type="var">T\_RNil</span></span> are vacuous because
abstractions and {} don't step. Case <span class="inlinecode"><span
class="id" type="var">T\_Var</span></span> is vacuous as well, since the
context is empty.
<div class="paragraph">

</div>

-   If the final step of the derivation is by <span
    class="inlinecode"><span class="id" type="var">T\_App</span></span>,
    then there are terms <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> and types <span
    class="inlinecode"><span class="id" type="var">T~1~</span></span>
    <span class="inlinecode"><span class="id"
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
    type="var">T~2~</span></span> and <span class="inlinecode"><span
    class="id" type="var">empty</span></span> <span
    class="inlinecode"><span style="font-family: arial;">⊢</span></span>
    <span class="inlinecode"><span class="id"
    type="var">t~2~</span></span> <span class="inlinecode">:</span>
    <span class="inlinecode"><span class="id"
    type="var">T~1~</span></span>.
    <div class="paragraph">

    </div>

    By inspection of the definition of the step relation, there are
    three ways <span class="inlinecode"><span class="id"
    type="var">t~1~</span></span> <span class="inlinecode"><span
    class="id" type="var">t~2~</span></span> can step. Cases <span
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

    By Lemma <span class="inlinecode"><span class="id"
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
    type="var">T~2~</span></span>. It then follows by lemma <span
    class="inlinecode"><span class="id"
    type="var">substitution\_preserves\_typing</span></span> that <span
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

-   If the final step of the derivation is by <span
    class="inlinecode"><span class="id"
    type="var">T\_Proj</span></span>, then there is a term <span
    class="inlinecode"><span class="id" type="var">tr</span></span>,
    type <span class="inlinecode"><span class="id"
    type="var">Tr</span></span> and label <span class="inlinecode"><span
    class="id" type="var">i</span></span> such that <span
    class="inlinecode"><span class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">tr.i</span></span>, <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">tr</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">Tr</span></span>, and <span
    class="inlinecode"><span class="id" type="var">Tlookup</span></span>
    <span class="inlinecode"><span class="id" type="var">i</span></span>
    <span class="inlinecode"><span class="id"
    type="var">Tr</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">Some</span></span>
    <span class="inlinecode"><span class="id"
    type="var">T</span></span>.
    <div class="paragraph">

    </div>

    The IH for the typing derivation gives us that, for any term <span
    class="inlinecode"><span class="id" type="var">tr'</span></span>, if
    <span class="inlinecode"><span class="id"
    type="var">tr</span></span> <span class="inlinecode"><span
    style="font-family: arial;">⇒</span></span> <span
    class="inlinecode"><span class="id" type="var">tr'</span></span>
    then <span class="inlinecode"><span class="id"
    type="var">empty</span></span> <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">tr'</span></span>
    <span class="inlinecode"><span class="id"
    type="var">Tr</span></span>. Inspection of the definition of the
    step relation reveals that there are two ways a projection can step.
    Case <span class="inlinecode"><span class="id"
    type="var">ST\_Proj1</span></span> follows immediately by the IH.
    <div class="paragraph">

    </div>

    Instead suppose <span class="inlinecode"><span class="id"
    type="var">tr.i</span></span> steps by <span
    class="inlinecode"><span class="id"
    type="var">ST\_ProjRcd</span></span>. Then <span
    class="inlinecode"><span class="id" type="var">tr</span></span> is a
    value and there is some term <span class="inlinecode"><span
    class="id" type="var">vi</span></span> such that <span
    class="inlinecode"><span class="id" type="var">tlookup</span></span>
    <span class="inlinecode"><span class="id" type="var">i</span></span>
    <span class="inlinecode"><span class="id"
    type="var">tr</span></span> <span class="inlinecode">=</span> <span
    class="inlinecode"><span class="id" type="var">Some</span></span>
    <span class="inlinecode"><span class="id"
    type="var">vi</span></span> and <span class="inlinecode"><span
    class="id" type="var">t'</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode"><span
    class="id" type="var">vi</span></span>. But by lemma <span
    class="inlinecode"><span class="id"
    type="var">lookup\_field\_in\_value</span></span>, <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">vi</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">Ti</span></span> as desired.
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
    type="var">T\_Sub</span></span>.
    <div class="paragraph">

    </div>

-   If the final step of the derivation is by <span
    class="inlinecode"><span class="id"
    type="var">T\_RCons</span></span>, then there exist some terms <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode"><span class="id"
    type="var">tr</span></span>, types <span class="inlinecode"><span
    class="id" type="var">T~1~</span></span> <span
    class="inlinecode"><span class="id" type="var">Tr</span></span> and
    a label <span class="inlinecode"><span class="id"
    type="var">t</span></span> such that <span class="inlinecode"><span
    class="id" type="var">t</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode">{<span
    class="id" type="var">i</span>=<span class="id"
    type="var">t~1~</span>,</span> <span class="inlinecode"><span
    class="id" type="var">tr</span>}</span>, <span
    class="inlinecode"><span class="id" type="var">T</span></span> <span
    class="inlinecode">=</span> <span class="inlinecode">{<span
    class="id" type="var">i</span>:<span class="id"
    type="var">T~1~</span>,</span> <span class="inlinecode"><span
    class="id" type="var">Tr</span>}</span>, <span
    class="inlinecode"><span class="id"
    type="var">record\_tm</span></span> <span class="inlinecode"><span
    class="id" type="var">tr</span></span>, <span
    class="inlinecode"><span class="id"
    type="var">record\_tm</span></span> <span class="inlinecode"><span
    class="id" type="var">Tr</span></span>, <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">t~1~</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">T~1~</span></span> and <span
    class="inlinecode"><span class="id" type="var">empty</span></span>
    <span class="inlinecode"><span
    style="font-family: arial;">⊢</span></span> <span
    class="inlinecode"><span class="id" type="var">tr</span></span>
    <span class="inlinecode">:</span> <span class="inlinecode"><span
    class="id" type="var">Tr</span></span>.
    <div class="paragraph">

    </div>

    By the definition of the step relation, <span
    class="inlinecode"><span class="id" type="var">t</span></span> must
    have stepped by <span class="inlinecode"><span class="id"
    type="var">ST\_Rcd\_Head</span></span> or <span
    class="inlinecode"><span class="id"
    type="var">ST\_Rcd\_Tail</span></span>. In the first case, the
    result follows by the IH for <span class="inlinecode"><span
    class="id" type="var">t~1~</span></span>'s typing derivation and
    <span class="inlinecode"><span class="id"
    type="var">T\_RCons</span></span>. In the second case, the result
    follows by the IH for <span class="inlinecode"><span class="id"
    type="var">tr</span></span>'s typing derivation, <span
    class="inlinecode"><span class="id"
    type="var">T\_RCons</span></span>, and a use of the <span
    class="inlinecode"><span class="id"
    type="var">step\_preserves\_record\_tm</span></span> lemma.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Exercises on Typing {.section}
-------------------

<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (variations) {.section}

Each part of this problem suggests a different way of changing the
definition of the STLC with records and subtyping. (These changes are
not cumulative: each part starts from the original language.) In each
part, list which properties (Progress, Preservation, both, or neither)
become false. If a property becomes false, give a counterexample.
<div class="paragraph">

</div>

-   Suppose we add the following typing rule:
           <span
    style="font-family: serif; font-size:85%;">Γ</span> <span
    style="font-family: arial;">⊢</span> t : S~1~-\>S~2~
          S~1~ \<: T~1~      T~1~ \<: S~1~     S~2~ \<: T~2~
    ----------------------------------- (T\_Funny1)  

    ------------------------------------------------------------------------

           <span
    style="font-family: serif; font-size:85%;">Γ</span> <span
    style="font-family: arial;">⊢</span> t : T~1~-\>T~2~
    <div class="paragraph">

    </div>

-   Suppose we add the following reduction rule:
      
    ------------------ (ST\_Funny21)  

    ------------------------------------------------------------------------

            {} <span style="font-family: arial;">⇒</span> (\\x:Top. x)
    <div class="paragraph">

    </div>

-   Suppose we add the following subtyping rule:
      
    -------------- (S\_Funny3)  

    ------------------------------------------------------------------------

              {} \<: Top-\>Top
    <div class="paragraph">

    </div>

-   Suppose we add the following subtyping rule:
      
    -------------- (S\_Funny4)  

    ------------------------------------------------------------------------

              Top-\>Top \<: {}
    <div class="paragraph">

    </div>

-   Suppose we add the following evaluation rule:
      
    ----------------- (ST\_Funny5)  

    ------------------------------------------------------------------------

            ({} t) <span style="font-family: arial;">⇒</span> (t {})
    <div class="paragraph">

    </div>

-   Suppose we add the same evaluation rule \*and\* a new typing rule:
      
    ----------------- (ST\_Funny5)  

    ------------------------------------------------------------------------

            ({} t) <span style="font-family: arial;">⇒</span> (t {})
      
    ---------------------- (T\_Funny6)  

    ------------------------------------------------------------------------

          empty <span
    style="font-family: arial;">⊢</span> {} : Top-\>Top
    <div class="paragraph">

    </div>

-   Suppose we \*change\* the arrow subtyping rule to:
         S~1~ \<: T~1~       S~2~ \<: T~2~
    ----------------------- (S\_Arrow')  

    ------------------------------------------------------------------------

              S~1~-\>S~2~ \<: T~1~-\>T~2~

<div class="paragraph">

</div>

<span class="comment">(\*\* <span class="inlinecode"></span> \*)</span>\
<div class="paragraph">

</div>

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
