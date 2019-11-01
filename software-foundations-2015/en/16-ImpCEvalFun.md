<div id="page">

<div id="header">

</div>

<div id="main">

ImpCEvalFun<span class="subtitle">Evaluation Function for Imp</span> {.libtitle}
====================================================================

<div class="code code-tight">

</div>

<div class="doc">

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Evaluation Function {.section}
===================

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Imp</span>.\
\

</div>

<div class="doc">

Here's a first try at an evaluation function for commands, omitting
<span class="inlinecode"><span class="id"
type="var">WHILE</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">ceval\_step1</span> (<span class="id" type="var">st</span> :
<span class="id" type="var">state</span>) (<span class="id"
type="var">c</span> : <span class="id" type="var">com</span>) : <span
class="id" type="var">state</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">c</span> <span class="id" type="keyword">with</span>\
     | <span class="id" type="var">SKIP</span> ⇒\
         <span class="id" type="var">st</span>\
     | <span class="id" type="var">l</span> ::= <span class="id"
type="var">a1</span> ⇒\
         <span class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">l</span> (<span
class="id" type="var">aeval</span> <span class="id" type="var">st</span>
<span class="id" type="var">a1</span>)\
     | <span class="id" type="var">c1</span> ;; <span class="id"
type="var">c2</span> ⇒\
         <span class="id" type="keyword">let</span> <span class="id"
type="var">st'</span> := <span class="id" type="var">ceval\_step1</span>
<span class="id" type="var">st</span> <span class="id"
type="var">c1</span> <span class="id" type="keyword">in</span>\
         <span class="id" type="var">ceval\_step1</span> <span
class="id" type="var">st'</span> <span class="id" type="var">c2</span>\
     | <span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span> ⇒\
         <span class="id" type="keyword">if</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b</span>)\
           <span class="id" type="keyword">then</span> <span class="id"
type="var">ceval\_step1</span> <span class="id" type="var">st</span>
<span class="id" type="var">c1</span>\
           <span class="id" type="keyword">else</span> <span class="id"
type="var">ceval\_step1</span> <span class="id" type="var">st</span>
<span class="id" type="var">c2</span>\
     | <span class="id" type="var">WHILE</span> <span class="id"
type="var">b1</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c1</span> <span class="id" type="var">END</span>
⇒\
         <span class="id" type="var">st</span> <span
class="comment">(\* bogus \*)</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

In a traditional functional programming language like ML or Haskell we
could write the WHILE case as follows:
        | WHILE b1 DO c1 END => 
            if (beval st b1) 
              then ceval_step1 st (c1;; WHILE b1 DO c1 END)
              else st 

Coq doesn't accept such a definition (<span class="inlinecode"><span
class="id" type="var">Error</span>:</span> <span
class="inlinecode"><span class="id" type="var">Cannot</span></span>
<span class="inlinecode"><span class="id" type="var">guess</span></span>
<span class="inlinecode"><span class="id"
type="var">decreasing</span></span> <span class="inlinecode"><span
class="id" type="var">argument</span></span> <span
class="inlinecode"><span class="id" type="var">of</span></span> <span
class="inlinecode"><span class="id" type="var">fix</span></span>)
because the function we want to define is not guaranteed to terminate.
Indeed, the changed <span class="inlinecode"><span class="id"
type="var">ceval\_step1</span></span> function applied to the <span
class="inlinecode"><span class="id" type="var">loop</span></span>
program from <span class="inlinecode"><span class="id"
type="var">Imp.v</span></span> would never terminate. Since Coq is not
just a functional programming language, but also a consistent logic, any
potentially non-terminating function needs to be rejected. Here is an
invalid(!) Coq program showing what would go wrong if Coq allowed
non-terminating recursive functions:
         Fixpoint loop_false (n : nat) : False := loop_false n.

That is, propositions like <span class="inlinecode"><span class="id"
type="var">False</span></span> would become provable (e.g. <span
class="inlinecode"><span class="id" type="var">loop\_false</span></span>
<span class="inlinecode">0</span> would be a proof of <span
class="inlinecode"><span class="id" type="var">False</span></span>),
which would be a disaster for Coq's logical consistency.
<div class="paragraph">

</div>

Thus, because it doesn't terminate on all inputs, the full version of
<span class="inlinecode"><span class="id"
type="var">ceval\_step1</span></span> cannot be written in Coq — at
least not without one additional trick...
<div class="paragraph">

</div>

Second try, using an extra numeric argument as a "step index" to ensure
that evaluation always terminates.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">ceval\_step2</span> (<span class="id" type="var">st</span> :
<span class="id" type="var">state</span>) (<span class="id"
type="var">c</span> : <span class="id" type="var">com</span>) (<span
class="id" type="var">i</span> : <span class="id" type="var">nat</span>)
: <span class="id" type="var">state</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">i</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">O</span> ⇒ <span class="id"
type="var">empty\_state</span>\
   | <span class="id" type="var">S</span> <span class="id"
type="var">i'</span> ⇒\
     <span class="id" type="keyword">match</span> <span class="id"
type="var">c</span> <span class="id" type="keyword">with</span>\
       | <span class="id" type="var">SKIP</span> ⇒\
           <span class="id" type="var">st</span>\
       | <span class="id" type="var">l</span> ::= <span class="id"
type="var">a1</span> ⇒\
           <span class="id" type="var">update</span> <span class="id"
type="var">st</span> <span class="id" type="var">l</span> (<span
class="id" type="var">aeval</span> <span class="id" type="var">st</span>
<span class="id" type="var">a1</span>)\
       | <span class="id" type="var">c1</span> ;; <span class="id"
type="var">c2</span> ⇒\
           <span class="id" type="keyword">let</span> <span class="id"
type="var">st'</span> := <span class="id" type="var">ceval\_step2</span>
<span class="id" type="var">st</span> <span class="id"
type="var">c1</span> <span class="id" type="var">i'</span> <span
class="id" type="keyword">in</span>\
           <span class="id" type="var">ceval\_step2</span> <span
class="id" type="var">st'</span> <span class="id" type="var">c2</span>
<span class="id" type="var">i'</span>\
       | <span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span> ⇒\
           <span class="id" type="keyword">if</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b</span>)\
             <span class="id" type="keyword">then</span> <span
class="id" type="var">ceval\_step2</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">i'</span>\
             <span class="id" type="keyword">else</span> <span
class="id" type="var">ceval\_step2</span> <span class="id"
type="var">st</span> <span class="id" type="var">c2</span> <span
class="id" type="var">i'</span>\
       | <span class="id" type="var">WHILE</span> <span class="id"
type="var">b1</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c1</span> <span class="id" type="var">END</span>
⇒\
           <span class="id" type="keyword">if</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b1</span>)\
           <span class="id" type="keyword">then</span> <span class="id"
type="keyword">let</span> <span class="id" type="var">st'</span> :=
<span class="id" type="var">ceval\_step2</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">i'</span> <span class="id"
type="keyword">in</span>\
                <span class="id" type="var">ceval\_step2</span> <span
class="id" type="var">st'</span> <span class="id" type="var">c</span>
<span class="id" type="var">i'</span>\
           <span class="id" type="keyword">else</span> <span class="id"
type="var">st</span>\
     <span class="id" type="keyword">end</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

*Note*: It is tempting to think that the index <span
class="inlinecode"><span class="id" type="var">i</span></span> here is
counting the "number of steps of evaluation." But if you look closely
you'll see that this is not the case: for example, in the rule for
sequencing, the same <span class="inlinecode"><span class="id"
type="var">i</span></span> is passed to both recursive calls.
Understanding the exact way that <span class="inlinecode"><span
class="id" type="var">i</span></span> is treated will be important in
the proof of <span class="inlinecode"><span class="id"
type="var">ceval\_\_ceval\_step</span></span>, which is given as an
exercise below.
<div class="paragraph">

</div>

Third try, returning an <span class="inlinecode"><span class="id"
type="var">option</span></span> <span class="inlinecode"><span
class="id" type="var">state</span></span> instead of just a <span
class="inlinecode"><span class="id" type="var">state</span></span> so
that we can distinguish between normal and abnormal termination.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">ceval\_step3</span> (<span class="id" type="var">st</span> :
<span class="id" type="var">state</span>) (<span class="id"
type="var">c</span> : <span class="id" type="var">com</span>) (<span
class="id" type="var">i</span> : <span class="id"
type="var">nat</span>)\
                     : <span class="id" type="var">option</span> <span
class="id" type="var">state</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">i</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">O</span> ⇒ <span class="id"
type="var">None</span>\
   | <span class="id" type="var">S</span> <span class="id"
type="var">i'</span> ⇒\
     <span class="id" type="keyword">match</span> <span class="id"
type="var">c</span> <span class="id" type="keyword">with</span>\
       | <span class="id" type="var">SKIP</span> ⇒\
           <span class="id" type="var">Some</span> <span class="id"
type="var">st</span>\
       | <span class="id" type="var">l</span> ::= <span class="id"
type="var">a1</span> ⇒\
           <span class="id" type="var">Some</span> (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">l</span> (<span class="id" type="var">aeval</span>
<span class="id" type="var">st</span> <span class="id"
type="var">a1</span>))\
       | <span class="id" type="var">c1</span> ;; <span class="id"
type="var">c2</span> ⇒\
           <span class="id" type="keyword">match</span> (<span
class="id" type="var">ceval\_step3</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">i'</span>) <span class="id"
type="keyword">with</span>\
           | <span class="id" type="var">Some</span> <span class="id"
type="var">st'</span> ⇒ <span class="id" type="var">ceval\_step3</span>
<span class="id" type="var">st'</span> <span class="id"
type="var">c2</span> <span class="id" type="var">i'</span>\
           | <span class="id" type="var">None</span> ⇒ <span class="id"
type="var">None</span>\
           <span class="id" type="keyword">end</span>\
       | <span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span> ⇒\
           <span class="id" type="keyword">if</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b</span>)\
             <span class="id" type="keyword">then</span> <span
class="id" type="var">ceval\_step3</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">i'</span>\
             <span class="id" type="keyword">else</span> <span
class="id" type="var">ceval\_step3</span> <span class="id"
type="var">st</span> <span class="id" type="var">c2</span> <span
class="id" type="var">i'</span>\
       | <span class="id" type="var">WHILE</span> <span class="id"
type="var">b1</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c1</span> <span class="id" type="var">END</span>
⇒\
           <span class="id" type="keyword">if</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b1</span>)\
           <span class="id" type="keyword">then</span> <span class="id"
type="keyword">match</span> (<span class="id"
type="var">ceval\_step3</span> <span class="id" type="var">st</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">i'</span>) <span class="id" type="keyword">with</span>\
                | <span class="id" type="var">Some</span> <span
class="id" type="var">st'</span> ⇒ <span class="id"
type="var">ceval\_step3</span> <span class="id" type="var">st'</span>
<span class="id" type="var">c</span> <span class="id"
type="var">i'</span>\
                | <span class="id" type="var">None</span> ⇒ <span
class="id" type="var">None</span>\
                <span class="id" type="keyword">end</span>\
           <span class="id" type="keyword">else</span> <span class="id"
type="var">Some</span> <span class="id" type="var">st</span>\
     <span class="id" type="keyword">end</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

We can improve the readability of this definition by introducing a bit
of auxiliary notation to hide the "plumbing" involved in repeatedly
matching against optional states.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Notation</span> "'LETOPT' x \<== e1
'IN' e2"\
    := (<span class="id" type="keyword">match</span> <span class="id"
type="var">e1</span> <span class="id" type="keyword">with</span>\
          | <span class="id" type="var">Some</span> <span class="id"
type="var">x</span> ⇒ <span class="id" type="var">e2</span>\
          | <span class="id" type="var">None</span> ⇒ <span class="id"
type="var">None</span>\
        <span class="id" type="keyword">end</span>)\
    (<span class="id" type="var">right</span> <span class="id"
type="var">associativity</span>, <span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 60).\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">ceval\_step</span> (<span class="id" type="var">st</span> :
<span class="id" type="var">state</span>) (<span class="id"
type="var">c</span> : <span class="id" type="var">com</span>) (<span
class="id" type="var">i</span> : <span class="id"
type="var">nat</span>)\
                     : <span class="id" type="var">option</span> <span
class="id" type="var">state</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">i</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">O</span> ⇒ <span class="id"
type="var">None</span>\
   | <span class="id" type="var">S</span> <span class="id"
type="var">i'</span> ⇒\
     <span class="id" type="keyword">match</span> <span class="id"
type="var">c</span> <span class="id" type="keyword">with</span>\
       | <span class="id" type="var">SKIP</span> ⇒\
           <span class="id" type="var">Some</span> <span class="id"
type="var">st</span>\
       | <span class="id" type="var">l</span> ::= <span class="id"
type="var">a1</span> ⇒\
           <span class="id" type="var">Some</span> (<span class="id"
type="var">update</span> <span class="id" type="var">st</span> <span
class="id" type="var">l</span> (<span class="id" type="var">aeval</span>
<span class="id" type="var">st</span> <span class="id"
type="var">a1</span>))\
       | <span class="id" type="var">c1</span> ;; <span class="id"
type="var">c2</span> ⇒\
           <span class="id" type="var">LETOPT</span> <span class="id"
type="var">st'</span> \<== <span class="id"
type="var">ceval\_step</span> <span class="id" type="var">st</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">i'</span> <span class="id" type="var">IN</span>\
           <span class="id" type="var">ceval\_step</span> <span
class="id" type="var">st'</span> <span class="id" type="var">c2</span>
<span class="id" type="var">i'</span>\
       | <span class="id" type="var">IFB</span> <span class="id"
type="var">b</span> <span class="id" type="var">THEN</span> <span
class="id" type="var">c1</span> <span class="id" type="var">ELSE</span>
<span class="id" type="var">c2</span> <span class="id"
type="var">FI</span> ⇒\
           <span class="id" type="keyword">if</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b</span>)\
             <span class="id" type="keyword">then</span> <span
class="id" type="var">ceval\_step</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">i'</span>\
             <span class="id" type="keyword">else</span> <span
class="id" type="var">ceval\_step</span> <span class="id"
type="var">st</span> <span class="id" type="var">c2</span> <span
class="id" type="var">i'</span>\
       | <span class="id" type="var">WHILE</span> <span class="id"
type="var">b1</span> <span class="id" type="var">DO</span> <span
class="id" type="var">c1</span> <span class="id" type="var">END</span>
⇒\
           <span class="id" type="keyword">if</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b1</span>)\
           <span class="id" type="keyword">then</span> <span class="id"
type="var">LETOPT</span> <span class="id" type="var">st'</span> \<==
<span class="id" type="var">ceval\_step</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">i'</span> <span class="id" type="var">IN</span>\
                <span class="id" type="var">ceval\_step</span> <span
class="id" type="var">st'</span> <span class="id" type="var">c</span>
<span class="id" type="var">i'</span>\
           <span class="id" type="keyword">else</span> <span class="id"
type="var">Some</span> <span class="id" type="var">st</span>\
     <span class="id" type="keyword">end</span>\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">test\_ceval</span> (<span class="id"
type="var">st</span>:<span class="id" type="var">state</span>) (<span
class="id" type="var">c</span>:<span class="id" type="var">com</span>)
:=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">ceval\_step</span> <span class="id" type="var">st</span>
<span class="id" type="var">c</span> 500 <span class="id"
type="keyword">with</span>\
   | <span class="id" type="var">None</span> ⇒ <span class="id"
type="var">None</span>\
   | <span class="id" type="var">Some</span> <span class="id"
type="var">st</span> ⇒ <span class="id" type="var">Some</span> (<span
class="id" type="var">st</span> <span class="id" type="var">X</span>,
<span class="id" type="var">st</span> <span class="id"
type="var">Y</span>, <span class="id" type="var">st</span> <span
class="id" type="var">Z</span>)\
   <span class="id" type="keyword">end</span>.\
\
 <span class="comment">(\* Eval compute in \
      (test\_ceval empty\_state \
          (X ::= ANum 2;;\
           IFB BLe (AId X) (ANum 1)\
             THEN Y ::= ANum 3 \
             ELSE Z ::= ANum 4\
           FI)).\
    ====\>\
       Some (2, 0, 4)   \*)</span>\
\

</div>

<div class="doc">

#### Exercise: 2 stars (pup\_to\_n) {.section}

Write an Imp program that sums the numbers from <span
class="inlinecode">1</span> to <span class="inlinecode"><span class="id"
type="var">X</span></span> (inclusive: <span class="inlinecode">1</span>
<span class="inlinecode">+</span> <span class="inlinecode">2</span>
<span class="inlinecode">+</span> <span class="inlinecode">...</span>
<span class="inlinecode">+</span> <span class="inlinecode"><span
class="id" type="var">X</span></span>) in the variable <span
class="inlinecode"><span class="id" type="var">Y</span></span>. Make
sure your solution satisfies the test that follows.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">pup\_to\_n</span> : <span class="id" type="var">com</span>
:=\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">admit</span>.\
\
 <span class="comment">(\* \
 Example pup\_to\_n\_1 : \
   test\_ceval (update empty\_state X 5) pup\_to\_n\
   = Some (0, 15, 0).\
 Proof. reflexivity. Qed.\
 \*)</span>\

</div>

<div class="doc">

☐
<div class="paragraph">

</div>

#### Exercise: 2 stars, optional (peven) {.section}

Write a <span class="inlinecode"><span class="id"
type="var">While</span></span> program that sets <span
class="inlinecode"><span class="id" type="var">Z</span></span> to <span
class="inlinecode">0</span> if <span class="inlinecode"><span class="id"
type="var">X</span></span> is even and sets <span
class="inlinecode"><span class="id" type="var">Z</span></span> to <span
class="inlinecode">1</span> otherwise. Use <span
class="inlinecode"><span class="id" type="var">ceval\_test</span></span>
to test your program.

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

Equivalence of Relational and Step-Indexed Evaluation {.section}
=====================================================

<div class="paragraph">

</div>

As with arithmetic and boolean expressions, we'd hope that the two
alternative definitions of evaluation actually boil down to the same
thing. This section shows that this is the case. Make sure you
understand the statements of the theorems and can follow the structure
of the proofs.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_step\_\_ceval</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span>,\
       (<span style="font-family: arial;">∃</span><span class="id"
type="var">i</span>, <span class="id" type="var">ceval\_step</span>
<span class="id" type="var">st</span> <span class="id"
type="var">c</span> <span class="id" type="var">i</span> = <span
class="id" type="var">Some</span> <span class="id"
type="var">st'</span>) <span style="font-family: arial;">→</span>\
       <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span> <span class="id" type="var">H</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">i</span> <span class="id" type="var">E</span>].\
   <span class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st'</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">st</span>.\
   <span class="id" type="tactic">generalize</span> <span class="id"
type="tactic">dependent</span> <span class="id" type="var">c</span>.\
   <span class="id" type="tactic">induction</span> <span class="id"
type="var">i</span> <span class="id" type="keyword">as</span> [| <span
class="id" type="var">i'</span> ].\
\
   <span class="id" type="var">Case</span> "i = 0 -- contradictory".\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span> <span class="id" type="var">H</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>.\
\
   <span class="id" type="var">Case</span> "i = S i'".\
     <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span> <span class="id" type="var">H</span>.\
     <span class="id" type="var">com\_cases</span> (<span class="id"
type="tactic">destruct</span> <span class="id" type="var">c</span>)
<span class="id" type="var">SCase</span>;\
            <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">H</span>; <span
class="id" type="tactic">inversion</span> <span class="id"
type="var">H</span>; <span class="id" type="tactic">subst</span>; <span
class="id" type="tactic">clear</span> <span class="id"
type="var">H</span>.\
       <span class="id" type="var">SCase</span> "SKIP". <span class="id"
type="tactic">apply</span> <span class="id" type="var">E\_Skip</span>.\
       <span class="id" type="var">SCase</span> "::=". <span class="id"
type="tactic">apply</span> <span class="id" type="var">E\_Ass</span>.
<span class="id" type="tactic">reflexivity</span>.\
\
       <span class="id" type="var">SCase</span> ";;".\
         <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">ceval\_step</span> <span class="id"
type="var">st</span> <span class="id" type="var">c1</span> <span
class="id" type="var">i'</span>) <span class="id"
type="var">eqn</span>:<span class="id" type="var">Heqr1</span>.\
         <span class="id" type="var">SSCase</span> "Evaluation of r1
terminates normally".\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_Seq</span> <span class="id" type="keyword">with</span>
<span class="id" type="var">s</span>.\
             <span class="id" type="tactic">apply</span> <span
class="id" type="var">IHi'</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">Heqr1</span>.
<span class="id" type="tactic">reflexivity</span>.\
             <span class="id" type="tactic">apply</span> <span
class="id" type="var">IHi'</span>. <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H1</span>. <span class="id"
type="tactic">assumption</span>.\
         <span class="id" type="var">SSCase</span> "Otherwise --
contradiction".\
           <span class="id" type="tactic">inversion</span> <span
class="id" type="var">H1</span>.\
\
       <span class="id" type="var">SCase</span> "IFB".\
         <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">beval</span> <span class="id" type="var">st</span>
<span class="id" type="var">b</span>) <span class="id"
type="var">eqn</span>:<span class="id" type="var">Heqr</span>.\
         <span class="id" type="var">SSCase</span> "r = true".\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_IfTrue</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">Heqr</span>.
<span class="id" type="tactic">reflexivity</span>.\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHi'</span>. <span class="id"
type="tactic">assumption</span>.\
         <span class="id" type="var">SSCase</span> "r = false".\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_IfFalse</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">Heqr</span>.
<span class="id" type="tactic">reflexivity</span>.\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">IHi'</span>. <span class="id"
type="tactic">assumption</span>.\
\
       <span class="id" type="var">SCase</span> "WHILE". <span
class="id" type="tactic">destruct</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b</span>) <span class="id" type="var">eqn</span>
:<span class="id" type="var">Heqr</span>.\
         <span class="id" type="var">SSCase</span> "r = true".\
          <span class="id" type="tactic">destruct</span> (<span
class="id" type="var">ceval\_step</span> <span class="id"
type="var">st</span> <span class="id" type="var">c</span> <span
class="id" type="var">i'</span>) <span class="id"
type="var">eqn</span>:<span class="id" type="var">Heqr1</span>.\
           <span class="id" type="var">SSSCase</span> "r1 = Some s".\
             <span class="id" type="tactic">apply</span> <span
class="id" type="var">E\_WhileLoop</span> <span class="id"
type="keyword">with</span> <span class="id" type="var">s</span>. <span
class="id" type="tactic">rewrite</span> <span class="id"
type="var">Heqr</span>. <span class="id"
type="tactic">reflexivity</span>.\
             <span class="id" type="tactic">apply</span> <span
class="id" type="var">IHi'</span>. <span class="id"
type="tactic">rewrite</span> <span class="id" type="var">Heqr1</span>.
<span class="id" type="tactic">reflexivity</span>.\
             <span class="id" type="tactic">apply</span> <span
class="id" type="var">IHi'</span>. <span class="id"
type="tactic">simpl</span> <span class="id" type="keyword">in</span>
<span class="id" type="var">H1</span>. <span class="id"
type="tactic">assumption</span>.\
           <span class="id" type="var">SSSCase</span> "r1 = None".\
             <span class="id" type="tactic">inversion</span> <span
class="id" type="var">H1</span>.\
         <span class="id" type="var">SSCase</span> "r = false".\
           <span class="id" type="tactic">inversion</span> <span
class="id" type="var">H1</span>.\
           <span class="id" type="tactic">apply</span> <span class="id"
type="var">E\_WhileEnd</span>.\
           <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">←</span> <span class="id"
type="var">Heqr</span>. <span class="id" type="tactic">subst</span>.
<span class="id" type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 4 stars (ceval\_step\_\_ceval\_inf) {.section}

Write an informal proof of <span class="inlinecode"><span class="id"
type="var">ceval\_step\_\_ceval</span></span>, following the usual
template. (The template for case analysis on an inductively defined
value should look the same as for induction, except that there is no
induction hypothesis.) Make your proof communicate the main ideas to a
human reader; do not simply transcribe the steps of the formal proof.
<div class="paragraph">

</div>

<span class="comment">(\* FILL IN HERE \*)</span>\
 ☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_step\_more</span>: <span
style="font-family: arial;">∀</span><span class="id"
type="var">i1</span> <span class="id" type="var">i2</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>
<span class="id" type="var">c</span>,\
   <span class="id" type="var">i1</span> ≤ <span class="id"
type="var">i2</span> <span style="font-family: arial;">→</span>\
   <span class="id" type="var">ceval\_step</span> <span class="id"
type="var">st</span> <span class="id" type="var">c</span> <span
class="id" type="var">i1</span> = <span class="id"
type="var">Some</span> <span class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
   <span class="id" type="var">ceval\_step</span> <span class="id"
type="var">st</span> <span class="id" type="var">c</span> <span
class="id" type="var">i2</span> = <span class="id"
type="var">Some</span> <span class="id" type="var">st'</span>.\
 <span class="id" type="keyword">Proof</span>.\
 <span class="id" type="tactic">induction</span> <span class="id"
type="var">i1</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">i1'</span>]; <span class="id"
type="tactic">intros</span> <span class="id" type="var">i2</span> <span
class="id" type="var">st</span> <span class="id" type="var">st'</span>
<span class="id" type="var">c</span> <span class="id"
type="var">Hle</span> <span class="id" type="var">Hceval</span>.\
   <span class="id" type="var">Case</span> "i1 = 0".\
     <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hceval</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hceval</span>.\
   <span class="id" type="var">Case</span> "i1 = S i1'".\
     <span class="id" type="tactic">destruct</span> <span class="id"
type="var">i2</span> <span class="id" type="keyword">as</span> [|<span
class="id" type="var">i2'</span>]. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">Hle</span>.\
     <span class="id" type="tactic">assert</span> (<span class="id"
type="var">Hle'</span>: <span class="id" type="var">i1'</span> ≤ <span
class="id" type="var">i2'</span>) <span class="id"
type="tactic">by</span> <span class="id" type="tactic">omega</span>.\
     <span class="id" type="var">com\_cases</span> (<span class="id"
type="tactic">destruct</span> <span class="id" type="var">c</span>)
<span class="id" type="var">SCase</span>.\
     <span class="id" type="var">SCase</span> "SKIP".\
       <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hceval</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hceval</span>.\
       <span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> "::=".\
       <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hceval</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hceval</span>.\
       <span class="id" type="tactic">reflexivity</span>.\
     <span class="id" type="var">SCase</span> ";;".\
       <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hceval</span>.
<span class="id" type="tactic">simpl</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">ceval\_step</span> <span class="id" type="var">st</span>
<span class="id" type="var">c1</span> <span class="id"
type="var">i1'</span>) <span class="id" type="var">eqn</span>:<span
class="id" type="var">Heqst1'o</span>.\
       <span class="id" type="var">SSCase</span> "st1'o = Some".\
         <span class="id" type="tactic">apply</span> (<span class="id"
type="var">IHi1'</span> <span class="id" type="var">i2'</span>) <span
class="id" type="keyword">in</span> <span class="id"
type="var">Heqst1'o</span>; <span class="id" type="tactic">try</span>
<span class="id" type="tactic">assumption</span>.\
         <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">Heqst1'o</span>. <span class="id" type="tactic">simpl</span>.
<span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hceval</span>.\
         <span class="id" type="tactic">apply</span> (<span class="id"
type="var">IHi1'</span> <span class="id" type="var">i2'</span>) <span
class="id" type="keyword">in</span> <span class="id"
type="var">Hceval</span>; <span class="id" type="tactic">try</span>
<span class="id" type="tactic">assumption</span>.\
       <span class="id" type="var">SSCase</span> "st1'o = None".\
         <span class="id" type="tactic">inversion</span> <span
class="id" type="var">Hceval</span>.\
\
     <span class="id" type="var">SCase</span> "IFB".\
       <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hceval</span>.
<span class="id" type="tactic">simpl</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b</span>); <span class="id"
type="tactic">apply</span> (<span class="id" type="var">IHi1'</span>
<span class="id" type="var">i2'</span>) <span class="id"
type="keyword">in</span> <span class="id" type="var">Hceval</span>;
<span class="id" type="tactic">assumption</span>.\
\
     <span class="id" type="var">SCase</span> "WHILE".\
       <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hceval</span>.
<span class="id" type="tactic">simpl</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">beval</span> <span class="id" type="var">st</span> <span
class="id" type="var">b</span>); <span class="id"
type="tactic">try</span> <span class="id"
type="tactic">assumption</span>.\
       <span class="id" type="tactic">destruct</span> (<span class="id"
type="var">ceval\_step</span> <span class="id" type="var">st</span>
<span class="id" type="var">c</span> <span class="id"
type="var">i1'</span>) <span class="id" type="var">eqn</span>: <span
class="id" type="var">Heqst1'o</span>.\
       <span class="id" type="var">SSCase</span> "st1'o = Some".\
         <span class="id" type="tactic">apply</span> (<span class="id"
type="var">IHi1'</span> <span class="id" type="var">i2'</span>) <span
class="id" type="keyword">in</span> <span class="id"
type="var">Heqst1'o</span>; <span class="id" type="tactic">try</span>
<span class="id" type="tactic">assumption</span>.\
         <span class="id" type="tactic">rewrite</span> <span
style="font-family: arial;">→</span> <span class="id"
type="var">Heqst1'o</span>. <span class="id" type="tactic">simpl</span>.
<span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hceval</span>.\
         <span class="id" type="tactic">apply</span> (<span class="id"
type="var">IHi1'</span> <span class="id" type="var">i2'</span>) <span
class="id" type="keyword">in</span> <span class="id"
type="var">Hceval</span>; <span class="id" type="tactic">try</span>
<span class="id" type="tactic">assumption</span>.\
       <span class="id" type="var">SSCase</span> "i1'o = None".\
         <span class="id" type="tactic">simpl</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">Hceval</span>.
<span class="id" type="tactic">inversion</span> <span class="id"
type="var">Hceval</span>. <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

#### Exercise: 3 stars (ceval\_\_ceval\_step) {.section}

Finish the following proof. You'll need <span class="inlinecode"><span
class="id" type="var">ceval\_step\_more</span></span> in a few places,
as well as some basic facts about <span class="inlinecode">≤</span> and
<span class="inlinecode"><span class="id" type="var">plus</span></span>.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_\_ceval\_step</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span>,\
       <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span> <span
style="font-family: arial;">→</span>\
       <span style="font-family: arial;">∃</span><span class="id"
type="var">i</span>, <span class="id" type="var">ceval\_step</span>
<span class="id" type="var">st</span> <span class="id"
type="var">c</span> <span class="id" type="var">i</span> = <span
class="id" type="var">Some</span> <span class="id"
type="var">st'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span> <span class="id"
type="var">Hce</span>.\
   <span class="id" type="var">ceval\_cases</span> (<span class="id"
type="tactic">induction</span> <span class="id" type="var">Hce</span>)
<span class="id" type="var">Case</span>.\
   <span class="comment">(\* FILL IN HERE \*)</span> <span class="id"
type="var">Admitted</span>.\

</div>

<div class="doc">

☐

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_and\_ceval\_step\_coincide</span>: <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st'</span>,\
       <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st'</span>\
   <span style="font-family: arial;">↔</span> <span
style="font-family: arial;">∃</span><span class="id"
type="var">i</span>, <span class="id" type="var">ceval\_step</span>
<span class="id" type="var">st</span> <span class="id"
type="var">c</span> <span class="id" type="var">i</span> = <span
class="id" type="var">Some</span> <span class="id"
type="var">st'</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st'</span>.\
   <span class="id" type="tactic">split</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">ceval\_\_ceval\_step</span>. <span class="id"
type="tactic">apply</span> <span class="id"
type="var">ceval\_step\_\_ceval</span>.\
 <span class="id" type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Determinism of Evaluation (Simpler Proof) {.section}
=========================================

<div class="paragraph">

</div>

Here's a slicker proof showing that the evaluation relation is
deterministic, using the fact that the relational and step-indexed
definition of evaluation are the same.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Theorem</span> <span class="id"
type="var">ceval\_deterministic'</span> : <span
style="font-family: arial;">∀</span><span class="id" type="var">c</span>
<span class="id" type="var">st</span> <span class="id"
type="var">st1</span> <span class="id" type="var">st2</span>,\
      <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st1</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">c</span> / <span class="id"
type="var">st</span> <span style="font-family: arial;">⇓</span> <span
class="id" type="var">st2</span> <span
style="font-family: arial;">→</span>\
      <span class="id" type="var">st1</span> = <span class="id"
type="var">st2</span>.\
 <span class="id" type="keyword">Proof</span>.\
   <span class="id" type="tactic">intros</span> <span class="id"
type="var">c</span> <span class="id" type="var">st</span> <span
class="id" type="var">st1</span> <span class="id" type="var">st2</span>
<span class="id" type="var">He1</span> <span class="id"
type="var">He2</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ceval\_\_ceval\_step</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">He1</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ceval\_\_ceval\_step</span> <span class="id"
type="keyword">in</span> <span class="id" type="var">He2</span>.\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">He1</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">i1</span> <span class="id" type="var">E1</span>].\
   <span class="id" type="tactic">inversion</span> <span class="id"
type="var">He2</span> <span class="id" type="keyword">as</span> [<span
class="id" type="var">i2</span> <span class="id" type="var">E2</span>].\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ceval\_step\_more</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">i2</span> :=
<span class="id" type="var">i1</span> + <span class="id"
type="var">i2</span>) <span class="id" type="keyword">in</span> <span
class="id" type="var">E1</span>.\
   <span class="id" type="tactic">apply</span> <span class="id"
type="var">ceval\_step\_more</span> <span class="id"
type="keyword">with</span> (<span class="id" type="var">i2</span> :=
<span class="id" type="var">i1</span> + <span class="id"
type="var">i2</span>) <span class="id" type="keyword">in</span> <span
class="id" type="var">E2</span>.\
   <span class="id" type="tactic">rewrite</span> <span class="id"
type="var">E1</span> <span class="id" type="keyword">in</span> <span
class="id" type="var">E2</span>. <span class="id"
type="tactic">inversion</span> <span class="id" type="var">E2</span>.
<span class="id" type="tactic">reflexivity</span>.\
   <span class="id" type="tactic">omega</span>. <span class="id"
type="tactic">omega</span>. <span class="id" type="keyword">Qed</span>.\
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
