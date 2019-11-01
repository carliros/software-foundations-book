<div id="page">

<div id="header">

</div>

<div id="main">

SfLib<span class="subtitle">Software Foundations Library</span> {.libtitle}
===============================================================

<div class="code code-tight">

</div>

<div class="doc">

<div class="paragraph">

</div>

Here we collect together several useful definitions and theorems from
Basics.v, List.v, Poly.v, Ind.v, and Logic.v that are not already in the
Coq standard library. From now on we can <span class="inlinecode"><span
class="id" type="keyword">Import</span></span> or <span
class="inlinecode"><span class="id" type="keyword">Export</span></span>
this file, instead of cluttering our environment with all the examples
and false starts in those files.
<div class="paragraph">

</div>

From the Coq Standard Library {.section}
=============================

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="var">Omega</span>. <span
class="comment">(\* needed for using the <span class="inlinecode"><span
class="id" type="tactic">omega</span></span> tactic \*)</span>\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">Bool</span>.\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">List</span>.\
 <span class="id" type="keyword">Export</span> <span class="id"
type="var">ListNotations</span>.\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">Arith</span>.\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id"
type="var">Arith.EqNat</span>. <span class="comment">(\* Contains <span
class="inlinecode"><span class="id"
type="var">beq\_nat</span></span>, among other things \*)</span>\
\

</div>

<div class="doc">

From Basics.v {.section}
=============

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">admit</span> {<span class="id" type="var">T</span>: <span
class="id" type="keyword">Type</span>} : <span class="id"
type="var">T</span>. <span class="id" type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Require</span> <span class="id"
type="var">String</span>. <span class="id" type="keyword">Open</span>
<span class="id" type="keyword">Scope</span> <span class="id"
type="var">string\_scope</span>.\
\
 <span class="id" type="keyword">Ltac</span> <span class="id"
type="var">move\_to\_top</span> <span class="id" type="var">x</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">reverse</span> <span class="id" type="var">goal</span> <span
class="id" type="keyword">with</span>\
   | <span class="id" type="var">H</span> : <span class="id"
type="var">\_</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">\_</span> ⇒ <span class="id"
type="tactic">try</span> <span class="id" type="tactic">move</span>
<span class="id" type="var">x</span> <span class="id"
type="keyword">after</span> <span class="id" type="var">H</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span> "assert\_eq"
<span class="id" type="var">ident</span>(<span class="id"
type="var">x</span>) <span class="id" type="var">constr</span>(<span
class="id" type="var">v</span>) :=\
   <span class="id" type="keyword">let</span> <span class="id"
type="var">H</span> := <span class="id" type="tactic">fresh</span> <span
class="id" type="keyword">in</span>\
   <span class="id" type="tactic">assert</span> (<span class="id"
type="var">x</span> = <span class="id" type="var">v</span>) <span
class="id" type="keyword">as</span> <span class="id" type="var">H</span>
<span class="id" type="tactic">by</span> <span class="id"
type="tactic">reflexivity</span>;\
   <span class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span> "Case\_aux"
<span class="id" type="var">ident</span>(<span class="id"
type="var">x</span>) <span class="id" type="var">constr</span>(<span
class="id" type="var">name</span>) :=\
   <span class="id" type="var">first</span> [\
     <span class="id" type="tactic">set</span> (<span class="id"
type="var">x</span> := <span class="id" type="var">name</span>); <span
class="id" type="var">move\_to\_top</span> <span class="id"
type="var">x</span>\
   | <span class="id" type="var">assert\_eq</span> <span class="id"
type="var">x</span> <span class="id" type="var">name</span>; <span
class="id" type="var">move\_to\_top</span> <span class="id"
type="var">x</span>\
   | <span class="id" type="tactic">fail</span> 1 "because we are
working on a different case" ].\
\
 <span class="id" type="keyword">Tactic Notation</span> "Case" <span
class="id" type="var">constr</span>(<span class="id"
type="var">name</span>) := <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">Case</span> <span class="id"
type="var">name</span>.\
 <span class="id" type="keyword">Tactic Notation</span> "SCase" <span
class="id" type="var">constr</span>(<span class="id"
type="var">name</span>) := <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">SCase</span> <span class="id"
type="var">name</span>.\
 <span class="id" type="keyword">Tactic Notation</span> "SSCase" <span
class="id" type="var">constr</span>(<span class="id"
type="var">name</span>) := <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">SSCase</span> <span class="id"
type="var">name</span>.\
 <span class="id" type="keyword">Tactic Notation</span> "SSSCase" <span
class="id" type="var">constr</span>(<span class="id"
type="var">name</span>) := <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">SSSCase</span> <span class="id"
type="var">name</span>.\
 <span class="id" type="keyword">Tactic Notation</span> "SSSSCase" <span
class="id" type="var">constr</span>(<span class="id"
type="var">name</span>) := <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">SSSSCase</span> <span class="id"
type="var">name</span>.\
 <span class="id" type="keyword">Tactic Notation</span> "SSSSSCase"
<span class="id" type="var">constr</span>(<span class="id"
type="var">name</span>) := <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">SSSSSCase</span> <span class="id"
type="var">name</span>.\
 <span class="id" type="keyword">Tactic Notation</span> "SSSSSSCase"
<span class="id" type="var">constr</span>(<span class="id"
type="var">name</span>) := <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">SSSSSSCase</span> <span class="id"
type="var">name</span>.\
 <span class="id" type="keyword">Tactic Notation</span> "SSSSSSSCase"
<span class="id" type="var">constr</span>(<span class="id"
type="var">name</span>) := <span class="id" type="var">Case\_aux</span>
<span class="id" type="var">SSSSSSSCase</span> <span class="id"
type="var">name</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">ble\_nat</span> (<span class="id" type="var">n</span> <span
class="id" type="var">m</span> : <span class="id" type="var">nat</span>)
: <span class="id" type="var">bool</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">n</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">O</span> ⇒ <span class="id"
type="var">true</span>\
   | <span class="id" type="var">S</span> <span class="id"
type="var">n'</span> ⇒\
       <span class="id" type="keyword">match</span> <span class="id"
type="var">m</span> <span class="id" type="keyword">with</span>\
       | <span class="id" type="var">O</span> ⇒ <span class="id"
type="var">false</span>\
       | <span class="id" type="var">S</span> <span class="id"
type="var">m'</span> ⇒ <span class="id" type="var">ble\_nat</span> <span
class="id" type="var">n'</span> <span class="id" type="var">m'</span>\
       <span class="id" type="keyword">end</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">andb\_true\_elim1</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span>,\
   <span class="id" type="var">andb</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">b</span> = <span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">b</span>.\
   <span class="id" type="var">Case</span> "b = true".\
     <span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "b = false".\
     <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">reflexivity</span>.
<span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">andb\_true\_elim2</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span>,\
   <span class="id" type="var">andb</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">c</span> = <span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* An exercise in Basics.v \*)</span>\
 <span class="id" type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">beq\_nat\_sym</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">n</span> <span class="id" type="var">m</span> : <span
class="id" type="var">nat</span>),\
   <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">beq\_nat</span> <span class="id"
type="var">m</span> <span class="id" type="var">n</span>.\
 <span class="comment">(\* An exercise in Lists.v \*)</span>\
 <span class="id" type="var">Admitted</span>.\
\

</div>

<div class="doc">

From Props.v {.section}
============

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">ev</span> : <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   | <span class="id" type="var">ev\_0</span> : <span class="id"
type="var">ev</span> <span class="id" type="var">O</span>\
   | <span class="id" type="var">ev\_SS</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>:<span class="id" type="var">nat</span>, <span
class="id" type="var">ev</span> <span class="id" type="var">n</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">ev</span> (<span class="id" type="var">S</span> (<span
class="id" type="var">S</span> <span class="id" type="var">n</span>)).\
\

</div>

<div class="doc">

From Logic.v {.section}
============

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">andb\_true</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">c</span>,\
   <span class="id" type="var">andb</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">b</span> = <span class="id" type="var">true</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">c</span> = <span class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">c</span> <span
class="id" type="var">H</span>.\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">b</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">c</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">conj</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="tactic">reflexivity</span>.\
       <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>.\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>. <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">false\_beq\_nat</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">n'</span> : <span class="id"
type="var">nat</span>,\
      <span class="id" type="var">n</span> ≠ <span class="id"
type="var">n'</span> <span style="font-family: arial;">→</span>\
      <span class="id" type="var">beq\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">n'</span> = <span
class="id" type="var">false</span>.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* An exercise in Logic.v \*)</span>\
 <span class="id" type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ex\_falso\_quodlibet</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span>:<span class="id" type="keyword">Prop</span>),\
   <span class="id" type="var">False</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">contra</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">contra</span>. <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ev\_not\_ev\_S</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">n</span>,\
   <span class="id" type="var">ev</span> <span class="id"
type="var">n</span> <span style="font-family: arial;">→</span> ¬ <span
class="id" type="var">ev</span> (<span class="id" type="var">S</span>
<span class="id" type="var">n</span>).\
 <span class="id" type="keyword">Proof</span>.\
 <span class="comment">(\* An exercise in Logic.v \*)</span>\
 <span class="id" type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ble\_nat\_true</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">ble\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">n</span> ≤ <span class="id" type="var">m</span>.\
 <span class="comment">(\* An exercise in Logic.v \*)</span>\
 <span class="id" type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ble\_nat\_false</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span>,\
   <span class="id" type="var">ble\_nat</span> <span class="id"
type="var">n</span> <span class="id" type="var">m</span> = <span
class="id" type="var">false</span> <span
style="font-family: arial;">→</span> \~(<span class="id"
type="var">n</span> ≤ <span class="id" type="var">m</span>).\
 <span class="comment">(\* An exercise in Logic.v \*)</span>\
 <span class="id" type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">appears\_in</span> (<span class="id" type="var">n</span> :
<span class="id" type="var">nat</span>) : <span class="id"
type="var">list</span> <span class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
 | <span class="id" type="var">ai\_here</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">l</span>, <span class="id" type="var">appears\_in</span>
<span class="id" type="var">n</span> (<span class="id"
type="var">n</span>::<span class="id" type="var">l</span>)\
 | <span class="id" type="var">ai\_later</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">m</span>
<span class="id" type="var">l</span>, <span class="id"
type="var">appears\_in</span> <span class="id" type="var">n</span> <span
class="id" type="var">l</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">appears\_in</span> <span class="id" type="var">n</span>
(<span class="id" type="var">m</span>::<span class="id"
type="var">l</span>).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">next\_nat</span> (<span class="id" type="var">n</span>:<span
class="id" type="var">nat</span>) : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">nn</span> : <span class="id"
type="var">next\_nat</span> <span class="id" type="var">n</span> (<span
class="id" type="var">S</span> <span class="id" type="var">n</span>).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">total\_relation</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> :=\
   <span class="id" type="var">tot</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">n</span>
<span class="id" type="var">m</span> : <span class="id"
type="var">nat</span>, <span class="id"
type="var">total\_relation</span> <span class="id" type="var">n</span>
<span class="id" type="var">m</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">empty\_relation</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">nat</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span> := .\
\

</div>

<div class="doc">

From Later Files {.section}
================

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">relation</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) := <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">X</span> <span
style="font-family: arial;">→</span> <span class="id"
type="keyword">Prop</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">deterministic</span> {<span class="id" type="var">X</span>:
<span class="id" type="keyword">Type</span>} (<span class="id"
type="var">R</span>: <span class="id" type="var">relation</span> <span
class="id" type="var">X</span>) :=\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">x</span> <span class="id" type="var">y1</span> <span
class="id" type="var">y2</span> : <span class="id" type="var">X</span>,
<span class="id" type="var">R</span> <span class="id"
type="var">x</span> <span class="id" type="var">y1</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">R</span> <span class="id" type="var">x</span> <span
class="id" type="var">y2</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">y1</span> = <span class="id" type="var">y2</span>.\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">multi</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) (<span class="id"
type="var">R</span>: <span class="id" type="var">relation</span> <span
class="id" type="var">X</span>)\
                             : <span class="id" type="var">X</span>
<span style="font-family: arial;">→</span> <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="keyword">Prop</span> :=\
   | <span class="id" type="var">multi\_refl</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> : <span class="id" type="var">X</span>),\
                  <span class="id" type="var">multi</span> <span
class="id" type="var">X</span> <span class="id" type="var">R</span>
<span class="id" type="var">x</span> <span class="id"
type="var">x</span>\
   | <span class="id" type="var">multi\_step</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span> : <span class="id" type="var">X</span>),\
                     <span class="id" type="var">R</span> <span
class="id" type="var">x</span> <span class="id" type="var">y</span>
<span style="font-family: arial;">→</span>\
                     <span class="id" type="var">multi</span> <span
class="id" type="var">X</span> <span class="id" type="var">R</span>
<span class="id" type="var">y</span> <span class="id"
type="var">z</span> <span style="font-family: arial;">→</span>\
                     <span class="id" type="var">multi</span> <span
class="id" type="var">X</span> <span class="id" type="var">R</span>
<span class="id" type="var">x</span> <span class="id"
type="var">z</span>.\
 <span class="id" type="keyword">Implicit Arguments</span> <span
class="id" type="var">multi</span> [[<span class="id"
type="var">X</span>]].\
\
 <span class="id" type="keyword">Tactic Notation</span> "multi\_cases"
<span class="id" type="var">tactic</span>(<span class="id"
type="var">first</span>) <span class="id" type="var">ident</span>(<span
class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "multi\_refl" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"multi\_step" ].\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">multi\_R</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">R</span>:<span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">x</span> <span class="id" type="var">y</span> :
<span class="id" type="var">X</span>),\
        <span class="id" type="var">R</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">multi</span> <span class="id" type="var">R</span> <span
class="id" type="var">x</span> <span class="id" type="var">y</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">X</span> <span class="id" type="var">R</span> <span
class="id" type="var">x</span> <span class="id" type="var">y</span>
<span class="id" type="var">r</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">multi\_step</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">y</span>. <span
class="id" type="tactic">apply</span> <span class="id"
type="var">r</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">multi\_refl</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">multi\_trans</span> :\
   <span style="font-family: arial;">∀</span>(<span class="id"
type="var">X</span>:<span class="id" type="keyword">Type</span>) (<span
class="id" type="var">R</span>: <span class="id"
type="var">relation</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">x</span> <span class="id" type="var">y</span>
<span class="id" type="var">z</span> : <span class="id"
type="var">X</span>),\
       <span class="id" type="var">multi</span> <span class="id"
type="var">R</span> <span class="id" type="var">x</span> <span
class="id" type="var">y</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">multi</span> <span class="id"
type="var">R</span> <span class="id" type="var">y</span> <span
class="id" type="var">z</span> <span
style="font-family: arial;">→</span>\
       <span class="id" type="var">multi</span> <span class="id"
type="var">R</span> <span class="id" type="var">x</span> <span
class="id" type="var">z</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Identifiers and polymorphic partial maps.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">id</span> : <span class="id" type="keyword">Type</span> :=\
   <span class="id" type="var">Id</span> : <span class="id"
type="var">nat</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">id</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">eq\_id\_dec</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">id1</span> <span class="id" type="var">id2</span> : <span
class="id" type="var">id</span>, {<span class="id" type="var">id1</span>
= <span class="id" type="var">id2</span>} + {<span class="id"
type="var">id1</span> ≠ <span class="id" type="var">id2</span>}.\
 <span class="id" type="keyword">Proof</span>.\
    <span class="id" type="tactic">intros</span> <span class="id"
type="var">id1</span> <span class="id" type="var">id2</span>.\
    <span class="id" type="tactic">destruct</span> <span class="id"
type="var">id1</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">n1</span>]. <span class="id"
type="tactic">destruct</span> <span class="id" type="var">id2</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">n2</span>].\
    <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_nat\_dec</span> <span class="id" type="var">n1</span>
<span class="id" type="var">n2</span>) <span class="id"
type="keyword">as</span> [<span class="id" type="var">Heq</span> | <span
class="id" type="var">Hneq</span>].\
    <span class="id" type="var">Case</span> "n1 = n2".\
      <span class="id" type="var">left</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">Heq</span>.
<span class="id" type="tactic">reflexivity</span>.\
    <span class="id" type="var">Case</span> "n1 ≠ n2".\
      <span class="id" type="var">right</span>. <span class="id"
type="tactic">intros</span> <span class="id" type="var">contra</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">contra</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">Hneq</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H0</span>.\
 <span class="id" type="keyword">Defined</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">eq\_id</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">T</span>:<span class="id" type="keyword">Type</span>) <span
class="id" type="var">x</span> (<span class="id" type="var">p</span>
<span class="id" type="var">q</span>:<span class="id"
type="var">T</span>),\
               (<span class="id" type="keyword">if</span> <span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">x</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">p</span> <span class="id" type="keyword">else</span> <span
class="id" type="var">q</span>) = <span class="id" type="var">p</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>.\
   <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x</span> <span
class="id" type="var">x</span>); <span class="id"
type="tactic">try</span> <span class="id"
type="tactic">reflexivity</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ex\_falso\_quodlibet</span>; <span class="id"
type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">neq\_id</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">T</span>:<span class="id" type="keyword">Type</span>) <span
class="id" type="var">x</span> <span class="id" type="var">y</span>
(<span class="id" type="var">p</span> <span class="id"
type="var">q</span>:<span class="id" type="var">T</span>), <span
class="id" type="var">x</span> ≠ <span class="id" type="var">y</span>
<span style="font-family: arial;">→</span>\
                (<span class="id" type="keyword">if</span> <span
class="id" type="var">eq\_id\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">p</span> <span class="id" type="keyword">else</span> <span
class="id" type="var">q</span>) = <span class="id" type="var">q</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
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
 <span class="id" type="keyword">Notation</span> "'\\empty'" := <span
class="id" type="var">empty</span>.\
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
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">extend</span>.
<span class="id" type="tactic">rewrite</span> <span class="id"
type="var">eq\_id</span>; <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
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
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">extend</span>.
<span class="id" type="tactic">rewrite</span> <span class="id"
type="var">neq\_id</span>; <span class="id" type="tactic">auto</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">extend\_shadow</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">A</span>
(<span class="id" type="var">ctxt</span>: <span class="id"
type="var">partial\_map</span> <span class="id" type="var">A</span>)
<span class="id" type="var">t~1~</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">x1</span> <span
class="id" type="var">x2</span>,\
   <span class="id" type="var">extend</span> (<span class="id"
type="var">extend</span> <span class="id" type="var">ctxt</span> <span
class="id" type="var">x2</span> <span class="id" type="var">t~1~</span>)
<span class="id" type="var">x2</span> <span class="id"
type="var">t~2~</span> <span class="id" type="var">x1</span> = <span
class="id" type="var">extend</span> <span class="id"
type="var">ctxt</span> <span class="id" type="var">x2</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="var">x1</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">extend</span>.
<span class="id" type="tactic">destruct</span> (<span class="id"
type="var">eq\_id\_dec</span> <span class="id" type="var">x2</span>
<span class="id" type="var">x1</span>)...\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

------------------------------------------------------------------------

<div class="paragraph">

</div>

Some useful tactics {.section}
===================

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Tactic Notation</span>
"solve\_by\_inversion\_step" <span class="id"
type="var">tactic</span>(<span class="id" type="var">t</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">goal</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">H</span> : <span class="id"
type="var">\_</span> <span style="font-family: arial;">⊢</span> <span
class="id" type="var">\_</span> ⇒ <span class="id"
type="var">solve</span> [ <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H</span>;
<span class="id" type="tactic">subst</span>; <span class="id"
type="var">t</span> ]\
   <span class="id" type="keyword">end</span>\
   <span style="font-family: arial;">⇓</span> <span class="id"
type="tactic">fail</span> "because the goal is not solvable by
inversion.".\
\
 <span class="id" type="keyword">Tactic Notation</span> "solve" "by"
"inversion" "1" :=\
   <span class="id" type="var">solve\_by\_inversion\_step</span> <span
class="id" type="var">idtac</span>.\
 <span class="id" type="keyword">Tactic Notation</span> "solve" "by"
"inversion" "2" :=\
   <span class="id" type="var">solve\_by\_inversion\_step</span> (<span
class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id" type="tactic">inversion</span>
1).\
 <span class="id" type="keyword">Tactic Notation</span> "solve" "by"
"inversion" "3" :=\
   <span class="id" type="var">solve\_by\_inversion\_step</span> (<span
class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id" type="tactic">inversion</span>
2).\
 <span class="id" type="keyword">Tactic Notation</span> "solve" "by"
"inversion" :=\
   <span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id" type="tactic">inversion</span>
1.\
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
