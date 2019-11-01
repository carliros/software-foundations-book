<div id="page">

<div id="header">

</div>

<div id="main">

HoareAsLogic<span class="subtitle">Hoare Logic as a Logic</span> {.libtitle}
================================================================

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

The presentation of Hoare logic in chapter <span
class="inlinecode"><span class="id" type="var">Hoare</span></span> could
be described as "model-theoretic": the proof rules for each of the
constructors were presented as *theorems* about the evaluation behavior
of programs, and proofs of program correctness (validity of Hoare
triples) were constructed by combining these theorems directly in Coq.
<div class="paragraph">

</div>

Another way of presenting Hoare logic is to define a completely separate
proof system — a set of axioms and inference rules that talk about
commands, Hoare triples, etc. — and then say that a proof of a Hoare
triple is a valid derivation in *that* logic. We can do this by giving
an inductive definition of *valid derivations* in this new logic.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">hoare\_proof</span> : <span class="id"
type="var">Assertion</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">com</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Assertion</span> <span style="font-family: arial;">→</span>
<span class="id" type="keyword">Type</span> :=\
   | <span class="id" type="var">H\_Skip</span> : <span
style="font-family: arial;">∀</span><span class="id"
type="var">P</span>,\
       <span class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P</span> (<span class="id" type="var">SKIP</span>) <span
class="id" type="var">P</span>\
   | <span class="id" type="var">H\_Asgn</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">Q</span>
<span class="id" type="var">V</span> <span class="id"
type="var">a</span>,\
       <span class="id" type="var">hoare\_proof</span> (<span class="id"
type="var">assn\_sub</span> <span class="id" type="var">V</span> <span
class="id" type="var">a</span> <span class="id" type="var">Q</span>)
(<span class="id" type="var">V</span> ::= <span class="id"
type="var">a</span>) <span class="id" type="var">Q</span>\
   | <span class="id" type="var">H\_Seq</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">c</span> <span class="id"
type="var">Q</span> <span class="id" type="var">d</span> <span
class="id" type="var">R</span>,\
       <span class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P</span> <span class="id" type="var">c</span> <span
class="id" type="var">Q</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">hoare\_proof</span> <span class="id" type="var">Q</span>
<span class="id" type="var">d</span> <span class="id"
type="var">R</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P</span> (<span class="id" type="var">c</span>;;<span
class="id" type="var">d</span>) <span class="id" type="var">R</span>\
   | <span class="id" type="var">H\_If</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span> <span class="id"
type="var">b</span> <span class="id" type="var">c1</span> <span
class="id" type="var">c2</span>,\
     <span class="id" type="var">hoare\_proof</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">P</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span>) <span class="id" type="var">c1</span>
<span class="id" type="var">Q</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">hoare\_proof</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">P</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">∧</span> \~(<span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span>)) <span class="id" type="var">c2</span>
<span class="id" type="var">Q</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P</span> (<span class="id" type="var">IFB</span> <span
class="id" type="var">b</span> <span class="id" type="var">THEN</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">ELSE</span> <span class="id" type="var">c2</span> <span
class="id" type="var">FI</span>) <span class="id" type="var">Q</span>\
   | <span class="id" type="var">H\_While</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">b</span> <span class="id"
type="var">c</span>,\
     <span class="id" type="var">hoare\_proof</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">st</span> ⇒ <span
class="id" type="var">P</span> <span class="id" type="var">st</span>
<span style="font-family: arial;">∧</span> <span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span>) <span class="id" type="var">c</span>
<span class="id" type="var">P</span> <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P</span> (<span class="id" type="var">WHILE</span> <span
class="id" type="var">b</span> <span class="id" type="var">DO</span>
<span class="id" type="var">c</span> <span class="id"
type="var">END</span>) (<span class="id" type="keyword">fun</span> <span
class="id" type="var">st</span> ⇒ <span class="id" type="var">P</span>
<span class="id" type="var">st</span> <span
style="font-family: arial;">∧</span> ¬ (<span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span>))\
   | <span class="id" type="var">H\_Consequence</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">P'</span> <span class="id" type="var">Q'</span> :
<span class="id" type="var">Assertion</span>) <span class="id"
type="var">c</span>,\
     <span class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P'</span> <span class="id" type="var">c</span> <span
class="id" type="var">Q'</span> <span
style="font-family: arial;">→</span>\
     (<span style="font-family: arial;">∀</span><span class="id"
type="var">st</span>, <span class="id" type="var">P</span> <span
class="id" type="var">st</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P'</span> <span class="id" type="var">st</span>) <span
style="font-family: arial;">→</span>\
     (<span style="font-family: arial;">∀</span><span class="id"
type="var">st</span>, <span class="id" type="var">Q'</span> <span
class="id" type="var">st</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span> <span class="id" type="var">st</span>) <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P</span> <span class="id" type="var">c</span> <span
class="id" type="var">Q</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span>
"hoare\_proof\_cases" <span class="id" type="var">tactic</span>(<span
class="id" type="var">first</span>) <span class="id"
type="var">ident</span>(<span class="id" type="var">c</span>) :=\
   <span class="id" type="var">first</span>;\
   [ <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "H\_Skip" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"H\_Asgn" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "H\_Seq"\
   | <span class="id" type="var">Case\_aux</span> <span class="id"
type="var">c</span> "H\_If" | <span class="id"
type="var">Case\_aux</span> <span class="id" type="var">c</span>
"H\_While" | <span class="id" type="var">Case\_aux</span> <span
class="id" type="var">c</span> "H\_Consequence" ].\
\

</div>

<div class="doc">

We don't need to include axioms corresponding to <span
class="inlinecode"><span class="id"
type="var">hoare\_consequence\_pre</span></span> or <span
class="inlinecode"><span class="id"
type="var">hoare\_consequence\_post</span></span>, because these can be
proven easily from <span class="inlinecode"><span class="id"
type="var">H\_Consequence</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">H\_Consequence\_pre</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">P'</span>: <span class="id"
type="var">Assertion</span>) <span class="id" type="var">c</span>,\
     <span class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P'</span> <span class="id" type="var">c</span> <span
class="id" type="var">Q</span> <span
style="font-family: arial;">→</span>\
     (<span style="font-family: arial;">∀</span><span class="id"
type="var">st</span>, <span class="id" type="var">P</span> <span
class="id" type="var">st</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">P'</span> <span class="id" type="var">st</span>) <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P</span> <span class="id" type="var">c</span> <span
class="id" type="var">Q</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">H\_Consequence\_post</span> : <span
style="font-family: arial;">∀</span>(<span class="id"
type="var">P</span> <span class="id" type="var">Q</span> <span
class="id" type="var">Q'</span> : <span class="id"
type="var">Assertion</span>) <span class="id" type="var">c</span>,\
     <span class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P</span> <span class="id" type="var">c</span> <span
class="id" type="var">Q'</span> <span
style="font-family: arial;">→</span>\
     (<span style="font-family: arial;">∀</span><span class="id"
type="var">st</span>, <span class="id" type="var">Q'</span> <span
class="id" type="var">st</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Q</span> <span class="id" type="var">st</span>) <span
style="font-family: arial;">→</span>\
     <span class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P</span> <span class="id" type="var">c</span> <span
class="id" type="var">Q</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

Now, for example, let's construct a proof object representing a
derivation for the hoare triple
<div class="paragraph">

</div>

<div class="code code-tight">

      <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">assn\_sub</span> <span class="id" type="var">X</span> (<span
class="id" type="var">X</span>+1) (<span class="id"
type="var">assn\_sub</span> <span class="id" type="var">X</span> (<span
class="id" type="var">X</span>+2) (<span class="id"
type="var">X</span>=3))<span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">X</span>::=<span class="id" type="var">X</span>+1;; <span
class="id" type="var">X</span>::=<span class="id"
type="var">X</span>+2 <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">X</span>=3<span
style="letter-spacing:-.4em;">}</span>}.
<div class="paragraph">

</div>

</div>

We can use Coq's tactics to help us construct the proof object.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">sample\_proof</span>\
              : <span class="id" type="var">hoare\_proof</span>\
                  (<span class="id" type="var">assn\_sub</span> <span
class="id" type="var">X</span> (<span class="id" type="var">APlus</span>
(<span class="id" type="var">AId</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">ANum</span> 1))\
                    (<span class="id" type="var">assn\_sub</span> <span
class="id" type="var">X</span> (<span class="id" type="var">APlus</span>
(<span class="id" type="var">AId</span> <span class="id"
type="var">X</span>) (<span class="id" type="var">ANum</span> 2))\
                      (<span class="id" type="keyword">fun</span> <span
class="id" type="var">st</span> ⇒ <span class="id" type="var">st</span>
<span class="id" type="var">X</span> = 3) ))\
                  (<span class="id" type="var">X</span> ::= <span
class="id" type="var">APlus</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">X</span>) (<span
class="id" type="var">ANum</span> 1);; (<span class="id"
type="var">X</span> ::= <span class="id" type="var">APlus</span> (<span
class="id" type="var">AId</span> <span class="id" type="var">X</span>)
(<span class="id" type="var">ANum</span> 2)))\
                  (<span class="id" type="keyword">fun</span> <span
class="id" type="var">st</span> ⇒ <span class="id" type="var">st</span>
<span class="id" type="var">X</span> = 3).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Seq</span>; <span class="id" type="tactic">apply</span>
<span class="id" type="var">H\_Asgn</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="comment">(\*\
 Print sample\_proof.\
 ====\>\
   H\_Seq\
     (assn\_sub X (APlus (AId X) (ANum 1))\

       (assn\_sub X (APlus (AId X) (ANum 2)) (fun st : state =\> st X = VNat 3)))\
     (X ::= APlus (AId X) (ANum 1))\

    (assn\_sub X (APlus (AId X) (ANum 2)) (fun st : state =\> st X = VNat 3))\
     (X ::= APlus (AId X) (ANum 2)) (fun st : state =\> st X = VNat 3)\
     (H\_Asgn\

       (assn\_sub X (APlus (AId X) (ANum 2)) (fun st : state =\> st X = VNat 3))\
        X (APlus (AId X) (ANum 1)))\

    (H\_Asgn (fun st : state =\> st X = VNat 3) X (APlus (AId X) (ANum 2)))\
 \*)</span>\
\

</div>

<div class="doc">

#### Exercise: 2 stars (hoare\_proof\_sound) {.section}

Prove that such proof objects represent true claims.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_proof\_sound</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">c</span> <span class="id"
type="var">Q</span>,\
   <span class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P</span> <span class="id" type="var">c</span> <span
class="id" type="var">Q</span> <span
style="font-family: arial;">→</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

We can also use Coq's reasoning facilities to prove metatheorems about
Hoare Logic. For example, here are the analogs of two theorems we saw in
chapter <span class="inlinecode"><span class="id"
type="var">Hoare</span></span> — this time expressed in terms of the
syntax of Hoare Logic derivations (provability) rather than directly in
terms of the semantics of Hoare triples.
<div class="paragraph">

</div>

The first one says that, for every <span class="inlinecode"><span
class="id" type="var">P</span></span> and <span class="inlinecode"><span
class="id" type="var">c</span></span>, the assertion <span
class="inlinecode"><span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">P</span><span
style="letter-spacing:-.4em;">}</span>}</span> <span
class="inlinecode"><span class="id" type="var">c</span></span> <span
class="inlinecode"><span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">True</span><span
style="letter-spacing:-.4em;">}</span>}</span> is *provable* in Hoare
Logic. Note that the proof is more complex than the semantic proof in
<span class="inlinecode"><span class="id"
type="var">Hoare</span></span>: we actually need to perform an induction
over the structure of the command <span class="inlinecode"><span
class="id" type="var">c</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">H\_Post\_True\_deriv</span>:\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">c</span> <span class="id" type="var">P</span>, <span
class="id" type="var">hoare\_proof</span> <span class="id"
type="var">P</span> <span class="id" type="var">c</span> (<span
class="id" type="keyword">fun</span> <span class="id"
type="var">\_</span> ⇒ <span class="id" type="var">True</span>).\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intro</span> <span class="id"
type="var">c</span>.\
   <span class="id" type="var">com\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">c</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intro</span> <span class="id" type="var">P</span>.\
   <span class="id" type="var">Case</span> "SKIP".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Consequence</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">H\_Skip</span>.\
     <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>.\
     <span class="comment">(\* Proof of True \*)</span>\
     <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">I</span>.\
   <span class="id" type="var">Case</span> "::=".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Consequence\_pre</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">H\_Asgn</span>.\
     <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">I</span>.\
   <span class="id" type="var">Case</span> ";;".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Consequence\_pre</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Seq</span>.\
     <span class="id" type="tactic">apply</span> (<span class="id"
type="var">IHc1</span> (<span class="id" type="keyword">fun</span> <span
class="id" type="var">\_</span> ⇒ <span class="id"
type="var">True</span>)).\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHc2</span>.\
     <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">I</span>.\
   <span class="id" type="var">Case</span> "IFB".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">H\_Consequence\_pre</span> <span class="id"
type="keyword">with</span> (<span class="id" type="keyword">fun</span>
<span class="id" type="var">\_</span> ⇒ <span class="id"
type="var">True</span>).\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">H\_If</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHc1</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHc2</span>.\
     <span class="id" type="tactic">intros</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">I</span>.\
   <span class="id" type="var">Case</span> "WHILE".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Consequence</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_While</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHc</span>.\
     <span class="id" type="tactic">intros</span>; <span class="id"
type="tactic">apply</span> <span class="id" type="var">I</span>.\
     <span class="id" type="tactic">intros</span>; <span class="id"
type="tactic">apply</span> <span class="id" type="var">I</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Similarly, we can show that <span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">False</span><span
style="letter-spacing:-.4em;">}</span>}</span> <span
class="inlinecode"><span class="id" type="var">c</span></span> <span
class="inlinecode"><span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">Q</span><span
style="letter-spacing:-.4em;">}</span>}</span> is provable for any <span
class="inlinecode"><span class="id" type="var">c</span></span> and <span
class="inlinecode"><span class="id" type="var">Q</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">False\_and\_P\_imp</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">Q</span>,\
   <span class="id" type="var">False</span> <span
style="font-family: arial;">∧</span> <span class="id"
type="var">P</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">Q</span> [<span
class="id" type="var">CONTRA</span> <span class="id"
type="var">HP</span>].\
   <span class="id" type="tactic">destruct</span> <span class="id"
type="var">CONTRA</span>.\
 <span class="id" type="keyword">Qed</span>.\
\
 <span class="id" type="keyword">Tactic Notation</span>
"pre\_false\_helper" <span class="id" type="var">constr</span>(<span
class="id" type="var">CONSTR</span>) :=\
   <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Consequence\_pre</span>;\
     [<span class="id" type="tactic">eapply</span> <span class="id"
type="var">CONSTR</span> | <span class="id" type="tactic">intros</span>
? <span class="id" type="var">CONTRA</span>; <span class="id"
type="tactic">destruct</span> <span class="id"
type="var">CONTRA</span>].\
\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">H\_Pre\_False\_deriv</span>:\
   <span style="font-family: arial;">∀</span><span class="id"
type="var">c</span> <span class="id" type="var">Q</span>, <span
class="id" type="var">hoare\_proof</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">\_</span> ⇒ <span
class="id" type="var">False</span>) <span class="id" type="var">c</span>
<span class="id" type="var">Q</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span>.\
   <span class="id" type="var">com\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">c</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intro</span> <span class="id" type="var">Q</span>.\
   <span class="id" type="var">Case</span> "SKIP". <span class="id"
type="var">pre\_false\_helper</span> <span class="id"
type="var">H\_Skip</span>.\
   <span class="id" type="var">Case</span> "::=". <span class="id"
type="var">pre\_false\_helper</span> <span class="id"
type="var">H\_Asgn</span>.\
   <span class="id" type="var">Case</span> ";;". <span class="id"
type="var">pre\_false\_helper</span> <span class="id"
type="var">H\_Seq</span>. <span class="id" type="tactic">apply</span>
<span class="id" type="var">IHc1</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">IHc2</span>.\
   <span class="id" type="var">Case</span> "IFB".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">H\_If</span>; <span class="id" type="tactic">eapply</span>
<span class="id" type="var">H\_Consequence\_pre</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHc1</span>. <span class="id" type="tactic">intro</span>.
<span class="id" type="tactic">eapply</span> <span class="id"
type="var">False\_and\_P\_imp</span>.\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHc2</span>. <span class="id" type="tactic">intro</span>.
<span class="id" type="tactic">eapply</span> <span class="id"
type="var">False\_and\_P\_imp</span>.\
   <span class="id" type="var">Case</span> "WHILE".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Consequence\_post</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_While</span>.\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Consequence\_pre</span>.\
       <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHc</span>.\
       <span class="id" type="tactic">intro</span>. <span class="id"
type="tactic">eapply</span> <span class="id"
type="var">False\_and\_P\_imp</span>.\
     <span class="id" type="tactic">intro</span>. <span class="id"
type="tactic">simpl</span>. <span class="id" type="tactic">eapply</span>
<span class="id" type="var">False\_and\_P\_imp</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

As a last step, we can show that the set of <span
class="inlinecode"><span class="id"
type="var">hoare\_proof</span></span> axioms is sufficient to prove any
true fact about (partial) correctness. More precisely, any semantic
Hoare triple that we can prove can also be proved from these axioms.
Such a set of axioms is said to be *relatively complete*.
<div class="paragraph">

</div>

This proof is inspired by the one at
http://www.ps.uni-saarland.de/courses/sem-ws11/script/Hoare.html
<div class="paragraph">

</div>

To prove this fact, we'll need to invent some intermediate assertions
using a technical device known as *weakest preconditions*. Given a
command <span class="inlinecode"><span class="id"
type="var">c</span></span> and a desired postcondition assertion <span
class="inlinecode"><span class="id" type="var">Q</span></span>, the
weakest precondition <span class="inlinecode"><span class="id"
type="var">wp</span></span> <span class="inlinecode"><span class="id"
type="var">c</span></span> <span class="inlinecode"><span class="id"
type="var">Q</span></span> is an assertion <span
class="inlinecode"><span class="id" type="var">P</span></span> such that
<span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>}</span>
<span class="inlinecode"><span class="id" type="var">c</span></span>
<span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}</span>
holds, and moreover, for any other assertion <span
class="inlinecode"><span class="id" type="var">P'</span></span>, if
<span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P'</span><span style="letter-spacing:-.4em;">}</span>}</span>
<span class="inlinecode"><span class="id" type="var">c</span></span>
<span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>}</span>
holds then <span class="inlinecode"><span class="id"
type="var">P'</span></span> <span class="inlinecode"><span
style="font-family: arial;">→</span></span> <span
class="inlinecode"><span class="id" type="var">P</span></span>. We can
more directly define this as follows:

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">wp</span> (<span class="id" type="var">c</span>:<span
class="id" type="var">com</span>) (<span class="id"
type="var">Q</span>:<span class="id" type="var">Assertion</span>) :
<span class="id" type="var">Assertion</span> :=\
   <span class="id" type="keyword">fun</span> <span class="id"
type="var">s</span> ⇒ <span style="font-family: arial;">∀</span><span
class="id" type="var">s'</span>, <span class="id" type="var">c</span> /
<span class="id" type="var">s</span> <span
style="font-family: arial;">⇓</span> <span class="id"
type="var">s'</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">Q</span> <span class="id" type="var">s'</span>.\
\

</div>

<div class="doc">

#### Exercise: 1 star (wp\_is\_precondition) {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">wp\_is\_precondition</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">Q</span>,\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">wp</span> <span class="id" type="var">c</span> <span
class="id" type="var">Q</span><span
style="letter-spacing:-.4em;">}</span>} <span class="id"
type="var">c</span> <span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">Q</span><span
style="letter-spacing:-.4em;">}</span>}.\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 1 star (wp\_is\_weakest) {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">wp\_is\_weakest</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">Q</span> <span class="id"
type="var">P'</span>,\
    <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P'</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">→</span> <span
style="font-family: arial;">∀</span><span class="id"
type="var">st</span>, <span class="id" type="var">P'</span> <span
class="id" type="var">st</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">wp</span> <span class="id" type="var">c</span> <span
class="id" type="var">Q</span> <span class="id" type="var">st</span>.\
 <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\
\

</div>

<div class="doc">

The following utility lemma will also be useful.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Lemma</span> <span class="id"
type="var">bassn\_eval\_false</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">b</span>
<span class="id" type="var">st</span>, ¬ <span class="id"
type="var">bassn</span> <span class="id" type="var">b</span> <span
class="id" type="var">st</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b</span> = <span class="id"
type="var">false</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">b</span> <span class="id" type="var">st</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">unfold</span> <span class="id" type="var">bassn</span>
<span class="id" type="keyword">in</span> <span class="id"
type="var">H</span>. <span class="id" type="tactic">destruct</span>
(<span class="id" type="var">beval</span> <span class="id"
type="var">st</span> <span class="id" type="var">b</span>).\
     <span class="id" type="var">exfalso</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>. <span
class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="tactic">reflexivity</span>.\
 <span class="id" type="keyword">Qed</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 4 stars (hoare\_proof\_complete) {.section}

Complete the proof of the theorem.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">hoare\_proof\_complete</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">P</span>
<span class="id" type="var">c</span> <span class="id"
type="var">Q</span>,\
   <span style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>} <span
class="id" type="var">c</span> <span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">Q</span><span style="letter-spacing:-.4em;">}</span>} <span
style="font-family: arial;">→</span> <span class="id"
type="var">hoare\_proof</span> <span class="id" type="var">P</span>
<span class="id" type="var">c</span> <span class="id"
type="var">Q</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">P</span> <span class="id" type="var">c</span>. <span
class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">P</span>.\
   <span class="id" type="var">com\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">c</span>)
<span class="id" type="var">Case</span>; <span class="id"
type="tactic">intros</span> <span class="id" type="var">P</span> <span
class="id" type="var">Q</span> <span class="id" type="var">HT</span>.\
   <span class="id" type="var">Case</span> "SKIP".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Consequence</span>.\
      <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Skip</span>.\
       <span class="id" type="tactic">intros</span>. <span class="id"
type="var">eassumption</span>.\
       <span class="id" type="tactic">intro</span> <span class="id"
type="var">st</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">HT</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">E\_Skip</span>.\
   <span class="id" type="var">Case</span> "::=".\
     <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Consequence</span>.\
       <span class="id" type="tactic">eapply</span> <span class="id"
type="var">H\_Asgn</span>.\
       <span class="id" type="tactic">intro</span> <span class="id"
type="var">st</span>. <span class="id" type="tactic">apply</span> <span
class="id" type="var">HT</span>. <span class="id"
type="var">econstructor</span>. <span class="id"
type="tactic">reflexivity</span>.\
       <span class="id" type="tactic">intros</span>; <span class="id"
type="tactic">assumption</span>.\
   <span class="id" type="var">Case</span> ";;".\
     <span class="id" type="tactic">apply</span> <span class="id"
type="var">H\_Seq</span> <span class="id" type="keyword">with</span>
(<span class="id" type="var">wp</span> <span class="id"
type="var">c2</span> <span class="id" type="var">Q</span>).\
      <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHc1</span>.\
        <span class="id" type="tactic">intros</span> <span class="id"
type="var">st</span> <span class="id" type="var">st'</span> <span
class="id" type="var">E1</span> <span class="id" type="var">H</span>.
<span class="id" type="tactic">unfold</span> <span class="id"
type="var">wp</span>. <span class="id" type="tactic">intros</span> <span
class="id" type="var">st''</span> <span class="id"
type="var">E2</span>.\
          <span class="id" type="tactic">eapply</span> <span class="id"
type="var">HT</span>. <span class="id" type="var">econstructor</span>;
<span class="id" type="var">eassumption</span>. <span class="id"
type="tactic">assumption</span>.\
      <span class="id" type="tactic">eapply</span> <span class="id"
type="var">IHc2</span>. <span class="id" type="tactic">intros</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span> <span class="id" type="var">E1</span> <span
class="id" type="var">H</span>. <span class="id"
type="tactic">apply</span> <span class="id" type="var">H</span>; <span
class="id" type="tactic">assumption</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

Finally, we might hope that our axiomatic Hoare logic is *decidable*;
that is, that there is an (terminating) algorithm (a *decision
procedure*) that can determine whether or not a given Hoare triple is
valid (derivable). But such a decision procedure cannot exist!
<div class="paragraph">

</div>

Consider the triple <span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">True</span><span
style="letter-spacing:-.4em;">}</span>}</span> <span
class="inlinecode"><span class="id" type="var">c</span></span> <span
class="inlinecode"><span style="letter-spacing:-.4em;">{</span>{<span
class="id" type="var">False</span><span
style="letter-spacing:-.4em;">}</span>}</span>. This triple is valid if
and only if <span class="inlinecode"><span class="id"
type="var">c</span></span> is non-terminating. So any algorithm that
could determine validity of arbitrary triples could solve the Halting
Problem.
<div class="paragraph">

</div>

Similarly, the triple <span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">True</span>}</span> <span class="inlinecode"><span class="id"
type="var">SKIP</span></span> <span class="inlinecode"><span
style="letter-spacing:-.4em;">{</span>{<span class="id"
type="var">P</span><span style="letter-spacing:-.4em;">}</span>}</span>
is valid if and only if <span class="inlinecode"><span
style="font-family: arial;">∀</span></span> <span
class="inlinecode"><span class="id" type="var">s</span>,</span> <span
class="inlinecode"><span class="id" type="var">P</span></span> <span
class="inlinecode"><span class="id" type="var">s</span></span> is valid,
where <span class="inlinecode"><span class="id"
type="var">P</span></span> is an arbitrary assertion of Coq's logic. But
it is known that there can be no decision procedure for this logic.
<div class="paragraph">

</div>

<div class="paragraph">

</div>

Overall, this axiomatic style of presentation gives a clearer picture of
what it means to "give a proof in Hoare logic." However, it is not
entirely satisfactory from the point of view of writing down such proofs
in practice: it is quite verbose. The section of chapter <span
class="inlinecode"><span class="id" type="var">Hoare2</span></span> on
formalizing decorated programs shows how we can do even better.
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
