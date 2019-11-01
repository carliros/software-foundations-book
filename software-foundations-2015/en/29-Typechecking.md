<div id="page">

<div id="header">

</div>

<div id="main">

Typechecking {.libtitle}
============

<div class="code code-tight">

</div>

<div class="doc">

MoreStlc: A Typechecker for STLC {.section}
================================

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Export</span> <span class="id" type="var">Stlc</span>.\
\

</div>

<div class="doc">

The <span class="inlinecode"><span class="id"
type="var">has\_type</span></span> relation of the STLC defines what it
means for a term to belong to a type (in some context). But it doesn't,
by itself, tell us how to *check* whether or not a term is well typed.
<div class="paragraph">

</div>

Fortunately, the rules defining <span class="inlinecode"><span
class="id" type="var">has\_type</span></span> are *syntax directed* —
they exactly follow the shape of the term. This makes it straightforward
to translate the typing rules into clauses of a typechecking *function*
that takes a term and a context and either returns the term's type or
else signals that the term is not typable.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Module</span> <span class="id"
type="var">STLCChecker</span>.\
 <span class="id" type="keyword">Import</span> <span class="id"
type="var">STLC</span>.\
\

</div>

<div class="doc">

Comparing Types {.section}
---------------

<div class="paragraph">

</div>

First, we need a function to compare two types for equality...

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">beq\_ty</span> (<span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>:<span class="id" type="var">ty</span>)
: <span class="id" type="var">bool</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">T~1~</span>,<span class="id" type="var">T~2~</span> <span
class="id" type="keyword">with</span>\
   | <span class="id" type="var">TBool</span>, <span class="id"
type="var">TBool</span> ⇒\
       <span class="id" type="var">true</span>\
   | <span class="id" type="var">TArrow</span> <span class="id"
type="var">T~11~</span> <span class="id" type="var">T~12~</span>, <span
class="id" type="var">TArrow</span> <span class="id"
type="var">T21</span> <span class="id" type="var">T22</span> ⇒\
       <span class="id" type="var">andb</span> (<span class="id"
type="var">beq\_ty</span> <span class="id" type="var">T~11~</span> <span
class="id" type="var">T21</span>) (<span class="id"
type="var">beq\_ty</span> <span class="id" type="var">T~12~</span> <span
class="id" type="var">T22</span>)\
   | <span class="id" type="var">\_</span>,\_ ⇒\
       <span class="id" type="var">false</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

... and we need to establish the usual two-way connection between the
boolean result returned by <span class="inlinecode"><span class="id"
type="var">beq\_ty</span></span> and the logical proposition that its
inputs are equal.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">beq\_ty\_refl</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T~1~</span>,\
   <span class="id" type="var">beq\_ty</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~1~</span> = <span
class="id" type="var">true</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">T~1~</span>. <span class="id" type="tactic">induction</span>
<span class="id" type="var">T~1~</span>; <span class="id"
type="tactic">simpl</span>.\
     <span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHT1\_1</span>. <span class="id" type="tactic">rewrite</span>
<span class="id" type="var">IHT1\_2</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">beq\_ty\_\_eq</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span>,\
   <span class="id" type="var">beq\_ty</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> = <span
class="id" type="var">true</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">T~1~</span> = <span class="id" type="var">T~2~</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">T~1~</span>. <span class="id" type="tactic">induction</span>
<span class="id" type="var">T~1~</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">T~2~</span>
<span class="id" type="var">Hbeq</span>; <span class="id"
type="tactic">destruct</span> <span class="id" type="var">T~2~</span>;
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hbeq</span>.\
   <span class="id" type="var">Case</span> "T~1~=TBool".\
     <span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="var">Case</span> "T~1~=TArrow T1\_1 T1\_2".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">andb\_true</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H0</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">H0</span>
<span class="id" type="keyword">as</span> [<span class="id"
type="var">Hbeq1</span> <span class="id" type="var">Hbeq2</span>].\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHT1\_1</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">Hbeq1</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHT1\_2</span>
<span class="id" type="keyword">in</span> <span class="id"
type="var">Hbeq2</span>. <span class="id" type="tactic">subst</span>...
<span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

The Typechecker {.section}
---------------

<div class="paragraph">

</div>

Now here's the typechecker. It works by walking over the structure of
the given term, returning either <span class="inlinecode"><span
class="id" type="var">Some</span></span> <span class="inlinecode"><span
class="id" type="var">T</span></span> or <span class="inlinecode"><span
class="id" type="var">None</span></span>. Each time we make a recursive
call to find out the types of the subterms, we need to pattern-match on
the results to make sure that they are not <span
class="inlinecode"><span class="id" type="var">None</span></span>. Also,
in the <span class="inlinecode"><span class="id"
type="var">tapp</span></span> case, we use pattern matching to extract
the left- and right-hand sides of the function's arrow type (and fail if
the type of the function is not <span class="inlinecode"><span
class="id" type="var">TArrow</span></span> <span
class="inlinecode"><span class="id" type="var">T~11~</span></span> <span
class="inlinecode"><span class="id" type="var">T~12~</span></span> for
some <span class="inlinecode"><span class="id"
type="var">T~1~</span></span> and <span class="inlinecode"><span
class="id" type="var">T~2~</span></span>).

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">type\_check</span> (<span
style="font-family: serif; font-size:85%;">Γ</span>:<span class="id"
type="var">context</span>) (<span class="id" type="var">t</span>:<span
class="id" type="var">tm</span>) : <span class="id"
type="var">option</span> <span class="id" type="var">ty</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">t</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">tvar</span> <span class="id"
type="var">x</span> ⇒ <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span>\
   | <span class="id" type="var">tabs</span> <span class="id"
type="var">x</span> <span class="id" type="var">T~11~</span> <span
class="id" type="var">t~12~</span> ⇒ <span class="id"
type="keyword">match</span> <span class="id"
type="var">type\_check</span> (<span class="id" type="var">extend</span>
<span style="font-family: serif; font-size:85%;">Γ</span> <span
class="id" type="var">x</span> <span class="id" type="var">T~11~</span>)
<span class="id" type="var">t~12~</span> <span class="id"
type="keyword">with</span>\
                           | <span class="id" type="var">Some</span>
<span class="id" type="var">T~12~</span> ⇒ <span class="id"
type="var">Some</span> (<span class="id" type="var">TArrow</span> <span
class="id" type="var">T~11~</span> <span class="id"
type="var">T~12~</span>)\
                           | <span class="id" type="var">\_</span> ⇒
<span class="id" type="var">None</span>\
                         <span class="id" type="keyword">end</span>\
   | <span class="id" type="var">tapp</span> <span class="id"
type="var">t~1~</span> <span class="id" type="var">t~2~</span> ⇒ <span
class="id" type="keyword">match</span> <span class="id"
type="var">type\_check</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span>, <span class="id" type="var">type\_check</span>
<span style="font-family: serif; font-size:85%;">Γ</span> <span
class="id" type="var">t~2~</span> <span class="id"
type="keyword">with</span>\
                       | <span class="id" type="var">Some</span> (<span
class="id" type="var">TArrow</span> <span class="id"
type="var">T~11~</span> <span class="id" type="var">T~12~</span>),<span
class="id" type="var">Some</span> <span class="id"
type="var">T~2~</span> ⇒\
                         <span class="id" type="keyword">if</span> <span
class="id" type="var">beq\_ty</span> <span class="id"
type="var">T~11~</span> <span class="id" type="var">T~2~</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">Some</span> <span class="id" type="var">T~12~</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">None</span>\
                       | <span class="id" type="var">\_</span>,\_ ⇒
<span class="id" type="var">None</span>\
                     <span class="id" type="keyword">end</span>\
   | <span class="id" type="var">ttrue</span> ⇒ <span class="id"
type="var">Some</span> <span class="id" type="var">TBool</span>\
   | <span class="id" type="var">tfalse</span> ⇒ <span class="id"
type="var">Some</span> <span class="id" type="var">TBool</span>\
   | <span class="id" type="var">tif</span> <span class="id"
type="var">x</span> <span class="id" type="var">t</span> <span
class="id" type="var">f</span> ⇒ <span class="id"
type="keyword">match</span> <span class="id"
type="var">type\_check</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">x</span> <span class="id" type="keyword">with</span>\
                      | <span class="id" type="var">Some</span> <span
class="id" type="var">TBool</span> ⇒\
                        <span class="id" type="keyword">match</span>
<span class="id" type="var">type\_check</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span>, <span class="id" type="var">type\_check</span>
<span style="font-family: serif; font-size:85%;">Γ</span> <span
class="id" type="var">f</span> <span class="id"
type="keyword">with</span>\
                          | <span class="id" type="var">Some</span>
<span class="id" type="var">T~1~</span>, <span class="id"
type="var">Some</span> <span class="id" type="var">T~2~</span> ⇒\
                            <span class="id" type="keyword">if</span>
<span class="id" type="var">beq\_ty</span> <span class="id"
type="var">T~1~</span> <span class="id" type="var">T~2~</span> <span
class="id" type="keyword">then</span> <span class="id"
type="var">Some</span> <span class="id" type="var">T~1~</span> <span
class="id" type="keyword">else</span> <span class="id"
type="var">None</span>\
                          | <span class="id" type="var">\_</span>,\_ ⇒
<span class="id" type="var">None</span>\
                        <span class="id" type="keyword">end</span>\
                      | <span class="id" type="var">\_</span> ⇒ <span
class="id" type="var">None</span>\
                    <span class="id" type="keyword">end</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

Properties {.section}
----------

<div class="paragraph">

</div>

To verify that this typechecking algorithm is the correct one, we show
that it is *sound* and *complete* for the original <span
class="inlinecode"><span class="id" type="var">has\_type</span></span>
relation — that is, <span class="inlinecode"><span class="id"
type="var">type\_check</span></span> and <span class="inlinecode"><span
class="id" type="var">has\_type</span></span> define the same partial
function.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">type\_checking\_sound</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span>,\
   <span class="id" type="var">type\_check</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> = <span class="id" type="var">Some</span> <span
class="id" type="var">T</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">eauto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span>. <span class="id" type="tactic">generalize</span>
<span class="id" type="tactic">dependent</span> <span
style="font-family: serif; font-size:85%;">Γ</span>.\
   <span class="id" type="var">t\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">t</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">T</span> <span class="id" type="var">Htc</span>; <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">Htc</span>.\
   <span class="id" type="var">Case</span> "tvar"...\
   <span class="id" type="var">Case</span> "tapp".\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">type\_check</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">TO1</span>.\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">type\_check</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~2~</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">TO2</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">TO1</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">T~1~</span>|]; <span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">inversion</span>;\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">T~1~</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">T~11~</span> <span class="id"
type="var">T~12~</span>]; <span class="id" type="tactic">try</span>
<span class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">TO2</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">T~2~</span>|]; <span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">beq\_ty</span> <span class="id" type="var">T~11~</span> <span
class="id" type="var">T~2~</span>) <span class="id"
type="var">eqn</span>: <span class="id" type="var">Heqb</span>;\
     <span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">beq\_ty\_\_eq</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Heqb</span>.\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span>; <span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "tabs".\
     <span class="id" type="tactic">rename</span> <span class="id"
type="var">i</span> <span class="id" type="var">into</span> <span
class="id" type="var">y</span>. <span class="id"
type="tactic">rename</span> <span class="id" type="var">t</span> <span
class="id" type="var">into</span> <span class="id"
type="var">T~1~</span>.\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">extend</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">y</span> <span class="id" type="var">T~1~</span>) <span
class="id" type="keyword">as</span> <span class="id"
type="var">G'</span>.\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">type\_check</span> <span class="id" type="var">G'</span>
<span class="id" type="var">t0</span>) <span class="id"
type="keyword">as</span> <span class="id" type="var">TO2</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">TO2</span>; <span class="id" type="tactic">try</span> <span
class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span>; <span class="id" type="tactic">subst</span>...\
   <span class="id" type="var">Case</span> "ttrue"...\
   <span class="id" type="var">Case</span> "tfalse"...\
   <span class="id" type="var">Case</span> "tif".\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">type\_check</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~1~</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">TOc</span>.\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">type\_check</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~2~</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">TO1</span>.\
     <span class="id" type="var">remember</span> (<span class="id"
type="var">type\_check</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t~3~</span>) <span class="id" type="keyword">as</span> <span
class="id" type="var">TO2</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">TOc</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">Tc</span>|]; <span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">Tc</span>; <span class="id" type="tactic">try</span> <span
class="id" type="var">solve</span> <span class="id"
type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">TO1</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">T~1~</span>|]; <span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">TO2</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">T~2~</span>|]; <span class="id"
type="tactic">try</span> <span class="id" type="var">solve</span> <span
class="id" type="tactic">by</span> <span class="id"
type="tactic">inversion</span>.\
     <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">beq\_ty</span> <span class="id" type="var">T~1~</span> <span
class="id" type="var">T~2~</span>) <span class="id"
type="var">eqn</span>:<span class="id" type="var">Heqb</span>;\
     <span class="id" type="tactic">try</span> <span class="id"
type="var">solve</span> <span class="id" type="tactic">by</span> <span
class="id" type="tactic">inversion</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">beq\_ty\_\_eq</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Heqb</span>.\
     <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H0</span>. <span class="id" type="tactic">subst</span>. <span
class="id" type="tactic">subst</span>...\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">type\_checking\_complete</span> : <span
style="font-family: arial;">∀</span><span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span>,\
   <span class="id" type="var">has\_type</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">type\_check</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> = <span class="id" type="var">Some</span> <span
class="id" type="var">T</span>.\
 <span class="id" type="keyword">Proof</span> <span class="id"
type="keyword">with</span> <span class="id" type="tactic">auto</span>.\
   <span class="id" type="tactic">intros</span> <span
style="font-family: serif; font-size:85%;">Γ</span> <span class="id"
type="var">t</span> <span class="id" type="var">T</span> <span
class="id" type="var">Hty</span>.\
   <span class="id" type="var">has\_type\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Hty</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">simpl</span>.\
   <span class="id" type="var">Case</span> "T\_Var"...\
   <span class="id" type="var">Case</span> "T\_Abs". <span class="id"
type="tactic">rewrite</span> <span class="id"
type="var">IHHty</span>...\
   <span class="id" type="var">Case</span> "T\_App".\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHHty1</span>. <span class="id" type="tactic">rewrite</span>
<span class="id" type="var">IHHty2</span>.\
     <span class="id" type="tactic">rewrite</span> (<span class="id"
type="var">beq\_ty\_refl</span> <span class="id"
type="var">T~11~</span>)...\
   <span class="id" type="var">Case</span> "T\_True"...\
   <span class="id" type="var">Case</span> "T\_False"...\
   <span class="id" type="var">Case</span> "T\_If". <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">IHHty1</span>.
<span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHHty2</span>.\
     <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">IHHty3</span>. <span class="id" type="tactic">rewrite</span>
(<span class="id" type="var">beq\_ty\_refl</span> <span class="id"
type="var">T</span>)...\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">End</span> <span class="id"
type="var">STLCChecker</span>.\
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
