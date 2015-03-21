<div id="page">

<div id="header">

</div>

<div id="main">

Extraction<span class="subtitle">Extracting ML from Coq</span> {.libtitle}
==============================================================

<div class="code code-tight">

</div>

<div class="doc">

<div class="paragraph">

</div>

Basic Extraction {.section}
================

<div class="paragraph">

</div>

In its simplest form, program extraction from Coq is completely
straightforward.
<div class="paragraph">

</div>

First we say what language we want to extract into. Options are OCaml
(the most mature), Haskell (which mostly works), and Scheme (a bit out
of date).

</div>

<div class="code code-tight">

\
 <span class="id" type="var">Extraction</span> <span class="id"
type="var">Language</span> <span class="id" type="var">Ocaml</span>.\
\

</div>

<div class="doc">

Now we load up the Coq environment with some definitions, either
directly or by importing them from other modules.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">SfLib</span>.\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id"
type="var">ImpCEvalFun</span>.\
\

</div>

<div class="doc">

Finally, we tell Coq the name of a definition to extract and the name of
a file to put the extracted code into.

</div>

<div class="code code-tight">

\
 <span class="id" type="var">Extraction</span> "imp1.ml" <span
class="id" type="var">ceval\_step</span>.\
\

</div>

<div class="doc">

When Coq processes this command, it generates a file <span
class="inlinecode"><span class="id" type="var">imp1.ml</span></span>
containing an extracted version of <span class="inlinecode"><span
class="id" type="var">ceval\_step</span></span>, together with
everything that it recursively depends on. Have a look at this file now.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Controlling Extraction of Specific Types {.section}
========================================

<div class="paragraph">

</div>

We can tell Coq to extract certain <span class="inlinecode"><span
class="id" type="keyword">Inductive</span></span> definitions to
specific OCaml types. For each one, we must say
<div class="paragraph">

</div>

-   how the Coq type itself should be represented in OCaml, and
-   how each constructor should be translated.

</div>

<div class="code code-tight">

\
 <span class="id" type="var">Extract</span> <span class="id"
type="keyword">Inductive</span> <span class="id" type="var">bool</span>
⇒ "bool" [ "true" "false" ].\
\

</div>

<div class="doc">

Also, for non-enumeration types (where the constructors take arguments),
we give an OCaml expression that can be used as a "recursor" over
elements of the type. (Think Church numerals.)

</div>

<div class="code code-tight">

\
 <span class="id" type="var">Extract</span> <span class="id"
type="keyword">Inductive</span> <span class="id" type="var">nat</span> ⇒
"int"\
   [ "0" "(fun x <span style="font-family: arial;">→</span> x + 1)" ]\
   "(fun zero succ n <span style="font-family: arial;">→</span>\
       if n=0 then zero () else succ (n-1))".\
\

</div>

<div class="doc">

We can also extract defined constants to specific OCaml terms or
operators.

</div>

<div class="code code-tight">

\
 <span class="id" type="var">Extract</span> <span class="id"
type="var">Constant</span> <span class="id" type="var">plus</span> ⇒
"( + )".\
 <span class="id" type="var">Extract</span> <span class="id"
type="var">Constant</span> <span class="id" type="var">mult</span> ⇒ "(
× )".\
 <span class="id" type="var">Extract</span> <span class="id"
type="var">Constant</span> <span class="id" type="var">beq\_nat</span> ⇒
"( = )".\
\

</div>

<div class="doc">

Important: It is entirely *your responsibility* to make sure that the
translations you're proving make sense. For example, it might be
tempting to include this one
<div class="paragraph">

</div>

<div class="code code-tight">

      <span class="id" type="var">Extract</span> <span class="id"
type="var">Constant</span> <span class="id"
type="var">minus</span> ⇒ "( - )".
<div class="paragraph">

</div>

</div>

but doing so could lead to serious confusion! (Why?)

</div>

<div class="code code-tight">

\
 <span class="id" type="var">Extraction</span> "imp2.ml" <span
class="id" type="var">ceval\_step</span>.\
\

</div>

<div class="doc">

Have a look at the file <span class="inlinecode"><span class="id"
type="var">imp2.ml</span></span>. Notice how the fundamental definitions
have changed from <span class="inlinecode"><span class="id"
type="var">imp1.ml</span></span>.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

A Complete Example {.section}
==================

<div class="paragraph">

</div>

To use our extracted evaluator to run Imp programs, all we need to add
is a tiny driver program that calls the evaluator and somehow prints out
the result.
<div class="paragraph">

</div>

For simplicity, we'll print results by dumping out the first four memory
locations in the final state.
<div class="paragraph">

</div>

Also, to make it easier to type in examples, let's extract a parser from
the <span class="inlinecode"><span class="id"
type="var">ImpParser</span></span> Coq module. To do this, we need a few
more declarations to set up the right correspondence between Coq strings
and lists of OCaml characters.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Ascii</span>
<span class="id" type="var">String</span>.\
 <span class="id" type="var">Extract</span> <span class="id"
type="keyword">Inductive</span> <span class="id" type="var">ascii</span>
⇒ <span class="id" type="var">char</span>\
 [\
 "(× If this appears, you're using Ascii internals. Please don't \*)
(fun (b0,b1,b2,b3,b4,b5,b6,b7) <span
style="font-family: arial;">→</span> let f b i = if b then 1 lsl i else
0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f
b6 6 + f b7 7))"\
 ]\
 "(× If this appears, you're using Ascii internals. Please don't \*)
(fun f c <span style="font-family: arial;">→</span> let n = Char.code c
in let h i = (n land (1 lsl i)) ≠ 0 in f (h 0) (h 1) (h 2) (h 3) (h 4)
(h 5) (h 6) (h 7))".\
 <span class="id" type="var">Extract</span> <span class="id"
type="var">Constant</span> <span class="id" type="var">zero</span> ⇒
"'\\000'".\
 <span class="id" type="var">Extract</span> <span class="id"
type="var">Constant</span> <span class="id" type="var">one</span> ⇒
"'\\001'".\
 <span class="id" type="var">Extract</span> <span class="id"
type="var">Constant</span> <span class="id" type="var">shift</span> ⇒\
  "fun b c <span style="font-family: arial;">→</span> Char.chr
(((Char.code c) lsl 1) land 255 + if b then 1 else 0)".\
 <span class="id" type="var">Extract</span> <span class="id"
type="var">Inlined</span> <span class="id" type="var">Constant</span>
<span class="id" type="var">ascii\_dec</span> ⇒ "(=)".\
\

</div>

<div class="doc">

We also need one more variant of booleans.

</div>

<div class="code code-tight">

\
 <span class="id" type="var">Extract</span> <span class="id"
type="keyword">Inductive</span> <span class="id"
type="var">sumbool</span> ⇒ "bool" ["true" "false"].\
\

</div>

<div class="doc">

The extraction is the same as always.

</div>

<div class="code code-tight">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Imp</span>.\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id"
type="var">ImpParser</span>.\
 <span class="id" type="var">Extraction</span> "imp.ml" <span class="id"
type="var">empty\_state</span> <span class="id"
type="var">ceval\_step</span> <span class="id" type="var">parse</span>.\
\

</div>

<div class="doc">

Now let's run our generated Imp evaluator. First, have a look at <span
class="inlinecode"><span class="id"
type="var">impdriver.ml</span></span>. (This was written by hand, not
extracted.)
<div class="paragraph">

</div>

Next, compile the driver together with the extracted code and execute
it, as follows.
       ocamlc -w -20 -w -26 -o impdriver imp.mli imp.ml impdriver.ml
        ./impdriver

(The <span class="inlinecode">-<span class="id"
type="var">w</span></span> flags to <span class="inlinecode"><span
class="id" type="var">ocamlc</span></span> are just there to suppress a
few spurious warnings.)

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Discussion {.section}
==========

<div class="paragraph">

</div>

Since we've proved that the <span class="inlinecode"><span class="id"
type="var">ceval\_step</span></span> function behaves the same as the
<span class="inlinecode"><span class="id" type="var">ceval</span></span>
relation in an appropriate sense, the extracted program can be viewed as
a *certified* Imp interpreter. (Of course, the parser is not certified
in any interesting sense, since we didn't prove anything about it.)
<div class="paragraph">

</div>

</div>

<div class="code code-tight">

</div>

</div>

<div id="footer">

------------------------------------------------------------------------

[Index](http://www.cis.upenn.edu/~bcpierce/sf/current/coqindex.html)

</div>

</div>
