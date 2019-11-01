<div id="page">

<div id="header">

</div>

<div id="main">

ImpParser<span class="subtitle">Lexing and Parsing in Coq</span> {.libtitle}
================================================================

<div class="code code-tight">

</div>

<div class="doc">

<div class="paragraph">

</div>

The development of the <span class="inlinecode"><span class="id"
type="var">Imp</span></span> language in Imp.v completely ignores issues
of concrete syntax — how an ascii string that a programmer might write
gets translated into the abstract syntax trees defined by the datatypes
<span class="inlinecode"><span class="id" type="var">aexp</span></span>,
<span class="inlinecode"><span class="id" type="var">bexp</span></span>,
and <span class="inlinecode"><span class="id"
type="var">com</span></span>. In this file we illustrate how the rest of
the story can be filled in by building a simple lexical analyzer and
parser using Coq's functional programming facilities.
<div class="paragraph">

</div>

This development is not intended to be understood in detail: the
explanations are fairly terse and there are no exercises. The main point
is simply to demonstrate that it can be done. You are invited to look
through the code — most of it is not very complicated, though the parser
relies on some "monadic" programming idioms that may require a little
work to make out — but most readers will probably want to just skip down
to the Examples section at the very end to get the punchline.

</div>

<div class="code code-tight">

\

</div>

<div class="doc">

Internals {.section}
=========

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">SfLib</span>.\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Imp</span>.\
\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">String</span>.\
 <span class="id" type="keyword">Require</span> <span class="id"
type="keyword">Import</span> <span class="id" type="var">Ascii</span>.\
\
 <span class="id" type="keyword">Open</span> <span class="id"
type="keyword">Scope</span> <span class="id"
type="var">list\_scope</span>.\
\

</div>

<div class="doc">

Lexical Analysis {.section}
----------------

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">isWhite</span> (<span class="id" type="var">c</span> : <span
class="id" type="var">ascii</span>) : <span class="id"
type="var">bool</span> :=\
   <span class="id" type="keyword">let</span> <span class="id"
type="var">n</span> := <span class="id" type="var">nat\_of\_ascii</span>
<span class="id" type="var">c</span> <span class="id"
type="keyword">in</span>\
   <span class="id" type="var">orb</span> (<span class="id"
type="var">orb</span> (<span class="id" type="var">beq\_nat</span> <span
class="id" type="var">n</span> 32) <span
class="comment">(\* space \*)</span>\
            (<span class="id" type="var">beq\_nat</span> <span
class="id" type="var">n</span> 9)) <span
class="comment">(\* tab \*)</span>\
       (<span class="id" type="var">orb</span> (<span class="id"
type="var">beq\_nat</span> <span class="id" type="var">n</span> 10)
<span class="comment">(\* linefeed \*)</span>\
            (<span class="id" type="var">beq\_nat</span> <span
class="id" type="var">n</span> 13)). <span
class="comment">(\* Carriage return. \*)</span>\
\
 <span class="id" type="keyword">Notation</span> "x '\<=?' y" := (<span
class="id" type="var">ble\_nat</span> <span class="id"
type="var">x</span> <span class="id" type="var">y</span>)\
   (<span class="id" type="tactic">at</span> <span class="id"
type="var">level</span> 70, <span class="id" type="var">no</span> <span
class="id" type="var">associativity</span>) : <span class="id"
type="var">nat\_scope</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">isLowerAlpha</span> (<span class="id" type="var">c</span> :
<span class="id" type="var">ascii</span>) : <span class="id"
type="var">bool</span> :=\
   <span class="id" type="keyword">let</span> <span class="id"
type="var">n</span> := <span class="id" type="var">nat\_of\_ascii</span>
<span class="id" type="var">c</span> <span class="id"
type="keyword">in</span>\
     <span class="id" type="var">andb</span> (97 \<=? <span class="id"
type="var">n</span>) (<span class="id" type="var">n</span> \<=? 122).\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">isAlpha</span> (<span class="id" type="var">c</span> : <span
class="id" type="var">ascii</span>) : <span class="id"
type="var">bool</span> :=\
   <span class="id" type="keyword">let</span> <span class="id"
type="var">n</span> := <span class="id" type="var">nat\_of\_ascii</span>
<span class="id" type="var">c</span> <span class="id"
type="keyword">in</span>\
     <span class="id" type="var">orb</span> (<span class="id"
type="var">andb</span> (65 \<=? <span class="id" type="var">n</span>)
(<span class="id" type="var">n</span> \<=? 90))\
         (<span class="id" type="var">andb</span> (97 \<=? <span
class="id" type="var">n</span>) (<span class="id" type="var">n</span>
\<=? 122)).\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">isDigit</span> (<span class="id" type="var">c</span> : <span
class="id" type="var">ascii</span>) : <span class="id"
type="var">bool</span> :=\
   <span class="id" type="keyword">let</span> <span class="id"
type="var">n</span> := <span class="id" type="var">nat\_of\_ascii</span>
<span class="id" type="var">c</span> <span class="id"
type="keyword">in</span>\
      <span class="id" type="var">andb</span> (48 \<=? <span class="id"
type="var">n</span>) (<span class="id" type="var">n</span> \<=? 57).\
\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">chartype</span> := <span class="id" type="var">white</span> |
<span class="id" type="var">alpha</span> | <span class="id"
type="var">digit</span> | <span class="id" type="var">other</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">classifyChar</span> (<span class="id" type="var">c</span> :
<span class="id" type="var">ascii</span>) : <span class="id"
type="var">chartype</span> :=\
   <span class="id" type="keyword">if</span> <span class="id"
type="var">isWhite</span> <span class="id" type="var">c</span> <span
class="id" type="keyword">then</span>\
     <span class="id" type="var">white</span>\
   <span class="id" type="keyword">else</span> <span class="id"
type="keyword">if</span> <span class="id" type="var">isAlpha</span>
<span class="id" type="var">c</span> <span class="id"
type="keyword">then</span>\
     <span class="id" type="var">alpha</span>\
   <span class="id" type="keyword">else</span> <span class="id"
type="keyword">if</span> <span class="id" type="var">isDigit</span>
<span class="id" type="var">c</span> <span class="id"
type="keyword">then</span>\
     <span class="id" type="var">digit</span>\
   <span class="id" type="keyword">else</span>\
     <span class="id" type="var">other</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">list\_of\_string</span> (<span class="id" type="var">s</span>
: <span class="id" type="var">string</span>) : <span class="id"
type="var">list</span> <span class="id" type="var">ascii</span> :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">s</span> <span class="id" type="keyword">with</span>\
   | <span class="id" type="var">EmptyString</span> ⇒ []\
   | <span class="id" type="var">String</span> <span class="id"
type="var">c</span> <span class="id" type="var">s</span> ⇒ <span
class="id" type="var">c</span> :: (<span class="id"
type="var">list\_of\_string</span> <span class="id"
type="var">s</span>)\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">string\_of\_list</span> (<span class="id"
type="var">xs</span> : <span class="id" type="var">list</span> <span
class="id" type="var">ascii</span>) : <span class="id"
type="var">string</span> :=\
   <span class="id" type="var">fold\_right</span> <span class="id"
type="var">String</span> <span class="id" type="var">EmptyString</span>
<span class="id" type="var">xs</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">token</span> := <span class="id" type="var">string</span>.\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">tokenize\_helper</span> (<span class="id"
type="var">cls</span> : <span class="id" type="var">chartype</span>)
(<span class="id" type="var">acc</span> <span class="id"
type="var">xs</span> : <span class="id" type="var">list</span> <span
class="id" type="var">ascii</span>)\
                        : <span class="id" type="var">list</span> (<span
class="id" type="var">list</span> <span class="id"
type="var">ascii</span>) :=\
   <span class="id" type="keyword">let</span> <span class="id"
type="var">tk</span> := <span class="id" type="keyword">match</span>
<span class="id" type="var">acc</span> <span class="id"
type="keyword">with</span> [] ⇒ [] | <span class="id"
type="var">\_</span>::\_ ⇒ [<span class="id" type="var">rev</span> <span
class="id" type="var">acc</span>] <span class="id"
type="keyword">end</span> <span class="id" type="keyword">in</span>\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">xs</span> <span class="id" type="keyword">with</span>\
   | [] ⇒ <span class="id" type="var">tk</span>\
   | (<span class="id" type="var">x</span>::<span class="id"
type="var">xs'</span>) ⇒\
     <span class="id" type="keyword">match</span> <span class="id"
type="var">cls</span>, <span class="id" type="var">classifyChar</span>
<span class="id" type="var">x</span>, <span class="id"
type="var">x</span> <span class="id" type="keyword">with</span>\
     | <span class="id" type="var">\_</span>, <span class="id"
type="var">\_</span>, "(" ⇒ <span class="id" type="var">tk</span> ++
["("]::(<span class="id" type="var">tokenize\_helper</span> <span
class="id" type="var">other</span> [] <span class="id"
type="var">xs'</span>)\
     | <span class="id" type="var">\_</span>, <span class="id"
type="var">\_</span>, ")" ⇒ <span class="id" type="var">tk</span> ++
[")"]::(<span class="id" type="var">tokenize\_helper</span> <span
class="id" type="var">other</span> [] <span class="id"
type="var">xs'</span>)\
     | <span class="id" type="var">\_</span>, <span class="id"
type="var">white</span>, <span class="id" type="var">\_</span> ⇒ <span
class="id" type="var">tk</span> ++ (<span class="id"
type="var">tokenize\_helper</span> <span class="id"
type="var">white</span> [] <span class="id" type="var">xs'</span>)\
     | <span class="id" type="var">alpha</span>,<span class="id"
type="var">alpha</span>,<span class="id" type="var">x</span> ⇒ <span
class="id" type="var">tokenize\_helper</span> <span class="id"
type="var">alpha</span> (<span class="id" type="var">x</span>::<span
class="id" type="var">acc</span>) <span class="id"
type="var">xs'</span>\
     | <span class="id" type="var">digit</span>,<span class="id"
type="var">digit</span>,<span class="id" type="var">x</span> ⇒ <span
class="id" type="var">tokenize\_helper</span> <span class="id"
type="var">digit</span> (<span class="id" type="var">x</span>::<span
class="id" type="var">acc</span>) <span class="id"
type="var">xs'</span>\
     | <span class="id" type="var">other</span>,<span class="id"
type="var">other</span>,<span class="id" type="var">x</span> ⇒ <span
class="id" type="var">tokenize\_helper</span> <span class="id"
type="var">other</span> (<span class="id" type="var">x</span>::<span
class="id" type="var">acc</span>) <span class="id"
type="var">xs'</span>\
     | <span class="id" type="var">\_</span>,<span class="id"
type="var">tp</span>,<span class="id" type="var">x</span> ⇒ <span
class="id" type="var">tk</span> ++ (<span class="id"
type="var">tokenize\_helper</span> <span class="id" type="var">tp</span>
[<span class="id" type="var">x</span>] <span class="id"
type="var">xs'</span>)\
     <span class="id" type="keyword">end</span>\
   <span class="id" type="keyword">end</span> %<span class="id"
type="var">char</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">tokenize</span> (<span class="id" type="var">s</span> : <span
class="id" type="var">string</span>) : <span class="id"
type="var">list</span> <span class="id" type="var">string</span> :=\
   <span class="id" type="var">map</span> <span class="id"
type="var">string\_of\_list</span> (<span class="id"
type="var">tokenize\_helper</span> <span class="id"
type="var">white</span> [] (<span class="id"
type="var">list\_of\_string</span> <span class="id"
type="var">s</span>)).\
\
 <span class="id" type="keyword">Example</span> <span class="id"
type="var">tokenize\_ex1</span> :\
     <span class="id" type="var">tokenize</span> "abc12==3
223\*(3+(a+c))" %<span class="id" type="var">string</span>\
   = ["abc"; "12"; "=="; "3"; "223";\
        "×"; "("; "3"; "+"; "(";\
        "a"; "+"; "c"; ")"; ")"]%<span class="id"
type="var">string</span>.\
 <span class="id" type="keyword">Proof</span>. <span class="id"
type="tactic">reflexivity</span>. <span class="id"
type="keyword">Qed</span>.\
\

</div>

<div class="doc">

Parsing {.section}
-------

</div>

<div class="code code-space">

\

</div>

<div class="doc">

### Options with Errors {.section}

</div>

<div class="code code-space">

\
 <span class="comment">(\* An option with error messages. \*)</span>\
 <span class="id" type="keyword">Inductive</span> <span class="id"
type="var">optionE</span> (<span class="id" type="var">X</span>:<span
class="id" type="keyword">Type</span>) : <span class="id"
type="keyword">Type</span> :=\
   | <span class="id" type="var">SomeE</span> : <span class="id"
type="var">X</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">optionE</span> <span class="id"
type="var">X</span>\
   | <span class="id" type="var">NoneE</span> : <span class="id"
type="var">string</span> <span style="font-family: arial;">→</span>
<span class="id" type="var">optionE</span> <span class="id"
type="var">X</span>.\
\
 <span class="id" type="keyword">Implicit Arguments</span> <span
class="id" type="var">SomeE</span> [[<span class="id"
type="var">X</span>]].\
 <span class="id" type="keyword">Implicit Arguments</span> <span
class="id" type="var">NoneE</span> [[<span class="id"
type="var">X</span>]].\
\
 <span
class="comment">(\* Some syntactic sugar to make writing nested match-expressions on\
    optionE more convenient. \*)</span>\
\
 <span class="id" type="keyword">Notation</span> "'DO' ( x , y ) \<== e1
; e2"\
    := (<span class="id" type="keyword">match</span> <span class="id"
type="var">e1</span> <span class="id" type="keyword">with</span>\
          | <span class="id" type="var">SomeE</span> (<span class="id"
type="var">x</span>,<span class="id" type="var">y</span>) ⇒ <span
class="id" type="var">e2</span>\
          | <span class="id" type="var">NoneE</span> <span class="id"
type="var">err</span> ⇒ <span class="id" type="var">NoneE</span> <span
class="id" type="var">err</span>\
        <span class="id" type="keyword">end</span>)\
    (<span class="id" type="var">right</span> <span class="id"
type="var">associativity</span>, <span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 60).\
\
 <span class="id" type="keyword">Notation</span> "'DO' ( x , y ) \<-- e1
; e2 'OR' e3"\
    := (<span class="id" type="keyword">match</span> <span class="id"
type="var">e1</span> <span class="id" type="keyword">with</span>\
          | <span class="id" type="var">SomeE</span> (<span class="id"
type="var">x</span>,<span class="id" type="var">y</span>) ⇒ <span
class="id" type="var">e2</span>\
          | <span class="id" type="var">NoneE</span> <span class="id"
type="var">err</span> ⇒ <span class="id" type="var">e3</span>\
        <span class="id" type="keyword">end</span>)\
    (<span class="id" type="var">right</span> <span class="id"
type="var">associativity</span>, <span class="id"
type="tactic">at</span> <span class="id" type="var">level</span> 60,
<span class="id" type="var">e2</span> <span class="id"
type="tactic">at</span> <span class="id" type="var">next</span> <span
class="id" type="var">level</span>).\
\

</div>

<div class="doc">

### Symbol Table {.section}

</div>

<div class="code code-space">

\
 <span class="comment">(\* Build a mapping from <span
class="inlinecode"><span class="id"
type="var">tokens</span></span> to <span class="inlinecode"><span
class="id" type="var">nats</span></span>.  A real parser would do\
    this incrementally as it encountered new symbols, but passing\
    around the symbol table inside the parsing functions is a bit\
    inconvenient, so instead we do it as a first pass. \*)</span>\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">build\_symtable</span> (<span class="id" type="var">xs</span>
: <span class="id" type="var">list</span> <span class="id"
type="var">token</span>) (<span class="id" type="var">n</span> : <span
class="id" type="var">nat</span>) : (<span class="id"
type="var">token</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">nat</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">xs</span> <span class="id" type="keyword">with</span>\
   | [] ⇒ (<span class="id" type="keyword">fun</span> <span class="id"
type="var">s</span> ⇒ <span class="id" type="var">n</span>)\
   | <span class="id" type="var">x</span>::<span class="id"
type="var">xs</span> ⇒\
     <span class="id" type="keyword">if</span> (<span class="id"
type="var">forallb</span> <span class="id"
type="var">isLowerAlpha</span> (<span class="id"
type="var">list\_of\_string</span> <span class="id"
type="var">x</span>))\
      <span class="id" type="keyword">then</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">s</span> ⇒ <span
class="id" type="keyword">if</span> <span class="id"
type="var">string\_dec</span> <span class="id" type="var">s</span> <span
class="id" type="var">x</span> <span class="id"
type="keyword">then</span> <span class="id" type="var">n</span> <span
class="id" type="keyword">else</span> (<span class="id"
type="var">build\_symtable</span> <span class="id" type="var">xs</span>
(<span class="id" type="var">S</span> <span class="id"
type="var">n</span>) <span class="id" type="var">s</span>))\
      <span class="id" type="keyword">else</span> <span class="id"
type="var">build\_symtable</span> <span class="id" type="var">xs</span>
<span class="id" type="var">n</span>\
   <span class="id" type="keyword">end</span>.\
\

</div>

<div class="doc">

### Generic Combinators for Building Parsers {.section}

</div>

<div class="code code-space">

\
 <span class="id" type="keyword">Open</span> <span class="id"
type="keyword">Scope</span> <span class="id"
type="var">string\_scope</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">parser</span> (<span class="id" type="var">T</span> : <span
class="id" type="keyword">Type</span>) :=\
   <span class="id" type="var">list</span> <span class="id"
type="var">token</span> <span style="font-family: arial;">→</span> <span
class="id" type="var">optionE</span> (<span class="id"
type="var">T</span> × <span class="id" type="var">list</span> <span
class="id" type="var">token</span>).\
\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">many\_helper</span> {<span class="id" type="var">T</span>}
(<span class="id" type="var">p</span> : <span class="id"
type="var">parser</span> <span class="id" type="var">T</span>) <span
class="id" type="var">acc</span> <span class="id"
type="var">steps</span> <span class="id" type="var">xs</span> :=\
 <span class="id" type="keyword">match</span> <span class="id"
type="var">steps</span>, <span class="id" type="var">p</span> <span
class="id" type="var">xs</span> <span class="id"
type="keyword">with</span>\
 | 0, <span class="id" type="var">\_</span> ⇒ <span class="id"
type="var">NoneE</span> "Too many recursive calls"\
 | <span class="id" type="var">\_</span>, <span class="id"
type="var">NoneE</span> <span class="id" type="var">\_</span> ⇒ <span
class="id" type="var">SomeE</span> ((<span class="id"
type="var">rev</span> <span class="id" type="var">acc</span>), <span
class="id" type="var">xs</span>)\
 | <span class="id" type="var">S</span> <span class="id"
type="var">steps'</span>, <span class="id" type="var">SomeE</span>
(<span class="id" type="var">t</span>, <span class="id"
type="var">xs'</span>) ⇒ <span class="id" type="var">many\_helper</span>
<span class="id" type="var">p</span> (<span class="id"
type="var">t</span>::<span class="id" type="var">acc</span>) <span
class="id" type="var">steps'</span> <span class="id"
type="var">xs'</span>\
 <span class="id" type="keyword">end</span>.\
\
 <span
class="comment">(\* A (step-indexed) parser which expects zero or more <span
class="inlinecode"><span class="id"
type="var">p</span></span>s \*)</span>\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">many</span> {<span class="id" type="var">T</span>} (<span
class="id" type="var">p</span> : <span class="id"
type="var">parser</span> <span class="id" type="var">T</span>) (<span
class="id" type="var">steps</span> : <span class="id"
type="var">nat</span>) : <span class="id" type="var">parser</span>
(<span class="id" type="var">list</span> <span class="id"
type="var">T</span>) :=\
   <span class="id" type="var">many\_helper</span> <span class="id"
type="var">p</span> [] <span class="id" type="var">steps</span>.\
\
 <span
class="comment">(\* A parser which expects a given token, followed by p \*)</span>\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">firstExpect</span> {<span class="id" type="var">T</span>}
(<span class="id" type="var">t</span> : <span class="id"
type="var">token</span>) (<span class="id" type="var">p</span> : <span
class="id" type="var">parser</span> <span class="id"
type="var">T</span>) : <span class="id" type="var">parser</span> <span
class="id" type="var">T</span> :=\
   <span class="id" type="keyword">fun</span> <span class="id"
type="var">xs</span> ⇒ <span class="id" type="keyword">match</span>
<span class="id" type="var">xs</span> <span class="id"
type="keyword">with</span>\
               | <span class="id" type="var">x</span>::<span class="id"
type="var">xs'</span> ⇒ <span class="id" type="keyword">if</span> <span
class="id" type="var">string\_dec</span> <span class="id"
type="var">x</span> <span class="id" type="var">t</span>\
                            <span class="id" type="keyword">then</span>
<span class="id" type="var">p</span> <span class="id"
type="var">xs'</span>\
                           <span class="id" type="keyword">else</span>
<span class="id" type="var">NoneE</span> ("expected '" ++ <span
class="id" type="var">t</span> ++ "'.")\
               | [] ⇒ <span class="id" type="var">NoneE</span>
("expected '" ++ <span class="id" type="var">t</span> ++ "'.")\
             <span class="id" type="keyword">end</span>.\
\
 <span
class="comment">(\* A parser which expects a particular token \*)</span>\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">expect</span> (<span class="id" type="var">t</span> : <span
class="id" type="var">token</span>) : <span class="id"
type="var">parser</span> <span class="id" type="var">unit</span> :=\
   <span class="id" type="var">firstExpect</span> <span class="id"
type="var">t</span> (<span class="id" type="keyword">fun</span> <span
class="id" type="var">xs</span> ⇒ <span class="id"
type="var">SomeE</span>(<span class="id" type="var">tt</span>, <span
class="id" type="var">xs</span>)).\
\

</div>

<div class="doc">

### A Recursive-Descent Parser for Imp {.section}

</div>

<div class="code code-space">

\
 <span class="comment">(\* Identifiers \*)</span>\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">parseIdentifier</span> (<span class="id"
type="var">symtable</span> :<span class="id"
type="var">string</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span>) (<span class="id" type="var">xs</span>
: <span class="id" type="var">list</span> <span class="id"
type="var">token</span>)\
                          : <span class="id" type="var">optionE</span>
(<span class="id" type="var">id</span> × <span class="id"
type="var">list</span> <span class="id" type="var">token</span>) :=\
 <span class="id" type="keyword">match</span> <span class="id"
type="var">xs</span> <span class="id" type="keyword">with</span>\
 | [] ⇒ <span class="id" type="var">NoneE</span> "Expected identifier"\
 | <span class="id" type="var">x</span>::<span class="id"
type="var">xs'</span> ⇒\
     <span class="id" type="keyword">if</span> <span class="id"
type="var">forallb</span> <span class="id"
type="var">isLowerAlpha</span> (<span class="id"
type="var">list\_of\_string</span> <span class="id" type="var">x</span>)
<span class="id" type="keyword">then</span>\
       <span class="id" type="var">SomeE</span> (<span class="id"
type="var">Id</span> (<span class="id" type="var">symtable</span> <span
class="id" type="var">x</span>), <span class="id"
type="var">xs'</span>)\
     <span class="id" type="keyword">else</span>\
       <span class="id" type="var">NoneE</span> ("Illegal
identifier:'" ++ <span class="id" type="var">x</span> ++ "'")\
 <span class="id" type="keyword">end</span>.\
\
 <span class="comment">(\* Numbers \*)</span>\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">parseNumber</span> (<span class="id" type="var">xs</span> :
<span class="id" type="var">list</span> <span class="id"
type="var">token</span>) : <span class="id" type="var">optionE</span>
(<span class="id" type="var">nat</span> × <span class="id"
type="var">list</span> <span class="id" type="var">token</span>) :=\
 <span class="id" type="keyword">match</span> <span class="id"
type="var">xs</span> <span class="id" type="keyword">with</span>\
 | [] ⇒ <span class="id" type="var">NoneE</span> "Expected number"\
 | <span class="id" type="var">x</span>::<span class="id"
type="var">xs'</span> ⇒\
     <span class="id" type="keyword">if</span> <span class="id"
type="var">forallb</span> <span class="id" type="var">isDigit</span>
(<span class="id" type="var">list\_of\_string</span> <span class="id"
type="var">x</span>) <span class="id" type="keyword">then</span>\
       <span class="id" type="var">SomeE</span> (<span class="id"
type="var">fold\_left</span> (<span class="id" type="keyword">fun</span>
<span class="id" type="var">n</span> <span class="id"
type="var">d</span> ⇒\
                         10 × <span class="id" type="var">n</span> +
(<span class="id" type="var">nat\_of\_ascii</span> <span class="id"
type="var">d</span> - <span class="id" type="var">nat\_of\_ascii</span>
"0"%<span class="id" type="var">char</span>))\
                 (<span class="id" type="var">list\_of\_string</span>
<span class="id" type="var">x</span>)\
                 0,\
               <span class="id" type="var">xs'</span>)\
     <span class="id" type="keyword">else</span>\
       <span class="id" type="var">NoneE</span> "Expected number"\
 <span class="id" type="keyword">end</span>.\
\
 <span class="comment">(\* Parse arithmetic expressions \*)</span>\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">parsePrimaryExp</span> (<span class="id"
type="var">steps</span>:<span class="id" type="var">nat</span>) <span
class="id" type="var">symtable</span> (<span class="id"
type="var">xs</span> : <span class="id" type="var">list</span> <span
class="id" type="var">token</span>)\
    : <span class="id" type="var">optionE</span> (<span class="id"
type="var">aexp</span> × <span class="id" type="var">list</span> <span
class="id" type="var">token</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">steps</span> <span class="id" type="keyword">with</span>\
   | 0 ⇒ <span class="id" type="var">NoneE</span> "Too many recursive
calls"\
   | <span class="id" type="var">S</span> <span class="id"
type="var">steps'</span> ⇒\
       <span class="id" type="var">DO</span> (<span class="id"
type="var">i</span>, <span class="id" type="var">rest</span>) \<-- <span
class="id" type="var">parseIdentifier</span> <span class="id"
type="var">symtable</span> <span class="id" type="var">xs</span> ;\
           <span class="id" type="var">SomeE</span> (<span class="id"
type="var">AId</span> <span class="id" type="var">i</span>, <span
class="id" type="var">rest</span>)\
       <span class="id" type="var">OR</span> <span class="id"
type="var">DO</span> (<span class="id" type="var">n</span>, <span
class="id" type="var">rest</span>) \<-- <span class="id"
type="var">parseNumber</span> <span class="id" type="var">xs</span> ;\
           <span class="id" type="var">SomeE</span> (<span class="id"
type="var">ANum</span> <span class="id" type="var">n</span>, <span
class="id" type="var">rest</span>)\
       <span class="id" type="var">OR</span> (<span class="id"
type="var">DO</span> (<span class="id" type="var">e</span>, <span
class="id" type="var">rest</span>) \<== <span class="id"
type="var">firstExpect</span> "(" (<span class="id"
type="var">parseSumExp</span> <span class="id" type="var">steps'</span>
<span class="id" type="var">symtable</span>) <span class="id"
type="var">xs</span>;\
           <span class="id" type="var">DO</span> (<span class="id"
type="var">u</span>, <span class="id" type="var">rest'</span>) \<==
<span class="id" type="var">expect</span> ")" <span class="id"
type="var">rest</span> ;\
           <span class="id" type="var">SomeE</span>(<span class="id"
type="var">e</span>,<span class="id" type="var">rest'</span>))\
   <span class="id" type="keyword">end</span>\
 <span class="id" type="keyword">with</span> <span class="id"
type="var">parseProductExp</span> (<span class="id"
type="var">steps</span>:<span class="id" type="var">nat</span>) <span
class="id" type="var">symtable</span> (<span class="id"
type="var">xs</span> : <span class="id" type="var">list</span> <span
class="id" type="var">token</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">steps</span> <span class="id" type="keyword">with</span>\
   | 0 ⇒ <span class="id" type="var">NoneE</span> "Too many recursive
calls"\
   | <span class="id" type="var">S</span> <span class="id"
type="var">steps'</span> ⇒\
     <span class="id" type="var">DO</span> (<span class="id"
type="var">e</span>, <span class="id" type="var">rest</span>) \<==\
       <span class="id" type="var">parsePrimaryExp</span> <span
class="id" type="var">steps'</span> <span class="id"
type="var">symtable</span> <span class="id" type="var">xs</span> ;\
     <span class="id" type="var">DO</span> (<span class="id"
type="var">es</span>, <span class="id" type="var">rest'</span>) \<==\
       <span class="id" type="var">many</span> (<span class="id"
type="var">firstExpect</span> "×" (<span class="id"
type="var">parsePrimaryExp</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>))
<span class="id" type="var">steps'</span> <span class="id"
type="var">rest</span>;\
     <span class="id" type="var">SomeE</span> (<span class="id"
type="var">fold\_left</span> <span class="id" type="var">AMult</span>
<span class="id" type="var">es</span> <span class="id"
type="var">e</span>, <span class="id" type="var">rest'</span>)\
   <span class="id" type="keyword">end</span>\
 <span class="id" type="keyword">with</span> <span class="id"
type="var">parseSumExp</span> (<span class="id"
type="var">steps</span>:<span class="id" type="var">nat</span>) <span
class="id" type="var">symtable</span> (<span class="id"
type="var">xs</span> : <span class="id" type="var">list</span> <span
class="id" type="var">token</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">steps</span> <span class="id" type="keyword">with</span>\
   | 0 ⇒ <span class="id" type="var">NoneE</span> "Too many recursive
calls"\
   | <span class="id" type="var">S</span> <span class="id"
type="var">steps'</span> ⇒\
     <span class="id" type="var">DO</span> (<span class="id"
type="var">e</span>, <span class="id" type="var">rest</span>) \<==\
       <span class="id" type="var">parseProductExp</span> <span
class="id" type="var">steps'</span> <span class="id"
type="var">symtable</span> <span class="id" type="var">xs</span> ;\
     <span class="id" type="var">DO</span> (<span class="id"
type="var">es</span>, <span class="id" type="var">rest'</span>) \<==\
       <span class="id" type="var">many</span> (<span class="id"
type="keyword">fun</span> <span class="id" type="var">xs</span> ⇒\
              <span class="id" type="var">DO</span> (<span class="id"
type="var">e</span>,<span class="id" type="var">rest'</span>) \<--\
                <span class="id" type="var">firstExpect</span> "+"
(<span class="id" type="var">parseProductExp</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">xs</span>;\
                                  <span class="id"
type="var">SomeE</span> ( (<span class="id" type="var">true</span>,
<span class="id" type="var">e</span>), <span class="id"
type="var">rest'</span>)\
              <span class="id" type="var">OR</span> <span class="id"
type="var">DO</span> (<span class="id" type="var">e</span>,<span
class="id" type="var">rest'</span>) \<==\
                <span class="id" type="var">firstExpect</span> "-"
(<span class="id" type="var">parseProductExp</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">xs</span>;\
                                  <span class="id"
type="var">SomeE</span> ( (<span class="id" type="var">false</span>,
<span class="id" type="var">e</span>), <span class="id"
type="var">rest'</span>))\
                             <span class="id" type="var">steps'</span>
<span class="id" type="var">rest</span>;\
       <span class="id" type="var">SomeE</span> (<span class="id"
type="var">fold\_left</span> (<span class="id" type="keyword">fun</span>
<span class="id" type="var">e0</span> <span class="id"
type="var">term</span> ⇒\
                           <span class="id" type="keyword">match</span>
<span class="id" type="var">term</span> <span class="id"
type="keyword">with</span>\
                             (<span class="id" type="var">true</span>,
<span class="id" type="var">e</span>) ⇒ <span class="id"
type="var">APlus</span> <span class="id" type="var">e0</span> <span
class="id" type="var">e</span>\
                           | (<span class="id" type="var">false</span>,
<span class="id" type="var">e</span>) ⇒ <span class="id"
type="var">AMinus</span> <span class="id" type="var">e0</span> <span
class="id" type="var">e</span>\
                           <span class="id" type="keyword">end</span>)\
                        <span class="id" type="var">es</span> <span
class="id" type="var">e</span>,\
              <span class="id" type="var">rest'</span>)\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">parseAExp</span> := <span class="id"
type="var">parseSumExp</span>.\
\
 <span class="comment">(\* Parsing boolean expressions. \*)</span>\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">parseAtomicExp</span> (<span class="id"
type="var">steps</span>:<span class="id" type="var">nat</span>) (<span
class="id" type="var">symtable</span> : <span class="id"
type="var">string</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span>) (<span class="id" type="var">xs</span>
: <span class="id" type="var">list</span> <span class="id"
type="var">token</span>) :=\
 <span class="id" type="keyword">match</span> <span class="id"
type="var">steps</span> <span class="id" type="keyword">with</span>\
   | 0 ⇒ <span class="id" type="var">NoneE</span> "Too many recursive
calls"\
   | <span class="id" type="var">S</span> <span class="id"
type="var">steps'</span> ⇒\
      <span class="id" type="var">DO</span> (<span class="id"
type="var">u</span>,<span class="id" type="var">rest</span>) \<-- <span
class="id" type="var">expect</span> "true" <span class="id"
type="var">xs</span>;\
          <span class="id" type="var">SomeE</span> (<span class="id"
type="var">BTrue</span>,<span class="id" type="var">rest</span>)\
      <span class="id" type="var">OR</span> <span class="id"
type="var">DO</span> (<span class="id" type="var">u</span>,<span
class="id" type="var">rest</span>) \<-- <span class="id"
type="var">expect</span> "false" <span class="id" type="var">xs</span>;\
          <span class="id" type="var">SomeE</span> (<span class="id"
type="var">BFalse</span>,<span class="id" type="var">rest</span>)\
      <span class="id" type="var">OR</span> <span class="id"
type="var">DO</span> (<span class="id" type="var">e</span>,<span
class="id" type="var">rest</span>) \<-- <span class="id"
type="var">firstExpect</span> "not" (<span class="id"
type="var">parseAtomicExp</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">xs</span>;\
          <span class="id" type="var">SomeE</span> (<span class="id"
type="var">BNot</span> <span class="id" type="var">e</span>, <span
class="id" type="var">rest</span>)\
      <span class="id" type="var">OR</span> <span class="id"
type="var">DO</span> (<span class="id" type="var">e</span>,<span
class="id" type="var">rest</span>) \<-- <span class="id"
type="var">firstExpect</span> "(" (<span class="id"
type="var">parseConjunctionExp</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">xs</span>;\
           (<span class="id" type="var">DO</span> (<span class="id"
type="var">u</span>,<span class="id" type="var">rest'</span>) \<== <span
class="id" type="var">expect</span> ")" <span class="id"
type="var">rest</span>; <span class="id" type="var">SomeE</span> (<span
class="id" type="var">e</span>, <span class="id"
type="var">rest'</span>))\
      <span class="id" type="var">OR</span> <span class="id"
type="var">DO</span> (<span class="id" type="var">e</span>, <span
class="id" type="var">rest</span>) \<== <span class="id"
type="var">parseProductExp</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>
<span class="id" type="var">xs</span> ;\
             (<span class="id" type="var">DO</span> (<span class="id"
type="var">e'</span>, <span class="id" type="var">rest'</span>) \<--\
               <span class="id" type="var">firstExpect</span> "=="
(<span class="id" type="var">parseAExp</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">rest</span> ;\
               <span class="id" type="var">SomeE</span> (<span
class="id" type="var">BEq</span> <span class="id" type="var">e</span>
<span class="id" type="var">e'</span>, <span class="id"
type="var">rest'</span>)\
              <span class="id" type="var">OR</span> <span class="id"
type="var">DO</span> (<span class="id" type="var">e'</span>, <span
class="id" type="var">rest'</span>) \<--\
                <span class="id" type="var">firstExpect</span> "≤"
(<span class="id" type="var">parseAExp</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">rest</span> ;\
                <span class="id" type="var">SomeE</span> (<span
class="id" type="var">BLe</span> <span class="id" type="var">e</span>
<span class="id" type="var">e'</span>, <span class="id"
type="var">rest'</span>)\
              <span class="id" type="var">OR</span>\
                <span class="id" type="var">NoneE</span> "Expected '=='
or '≤' after arithmetic expression")\
 <span class="id" type="keyword">end</span>\
 <span class="id" type="keyword">with</span> <span class="id"
type="var">parseConjunctionExp</span> (<span class="id"
type="var">steps</span>:<span class="id" type="var">nat</span>) (<span
class="id" type="var">symtable</span> : <span class="id"
type="var">string</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span>) (<span class="id" type="var">xs</span>
: <span class="id" type="var">list</span> <span class="id"
type="var">token</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">steps</span> <span class="id" type="keyword">with</span>\
   | 0 ⇒ <span class="id" type="var">NoneE</span> "Too many recursive
calls"\
   | <span class="id" type="var">S</span> <span class="id"
type="var">steps'</span> ⇒\
     <span class="id" type="var">DO</span> (<span class="id"
type="var">e</span>, <span class="id" type="var">rest</span>) \<==\
       <span class="id" type="var">parseAtomicExp</span> <span
class="id" type="var">steps'</span> <span class="id"
type="var">symtable</span> <span class="id" type="var">xs</span> ;\
     <span class="id" type="var">DO</span> (<span class="id"
type="var">es</span>, <span class="id" type="var">rest'</span>) \<==\
       <span class="id" type="var">many</span> (<span class="id"
type="var">firstExpect</span> "&&" (<span class="id"
type="var">parseAtomicExp</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>))
<span class="id" type="var">steps'</span> <span class="id"
type="var">rest</span>;\
     <span class="id" type="var">SomeE</span> (<span class="id"
type="var">fold\_left</span> <span class="id" type="var">BAnd</span>
<span class="id" type="var">es</span> <span class="id"
type="var">e</span>, <span class="id" type="var">rest'</span>)\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">parseBExp</span> := <span class="id"
type="var">parseConjunctionExp</span>.\
\
 <span class="comment">(\* \
 Eval compute in \
   (parseProductExp 100 (tokenize "x\*y\*(x\*x)\*x")).\
\
 Eval compute in \

  (parseDisjunctionExp 100 (tokenize "not((x==x||x\*x\<=(x\*x)\*x)&&x==x)")). \
 \*)</span>\
\
 <span class="comment">(\* Parsing commands \*)</span>\
 <span class="id" type="keyword">Fixpoint</span> <span class="id"
type="var">parseSimpleCommand</span> (<span class="id"
type="var">steps</span>:<span class="id" type="var">nat</span>) (<span
class="id" type="var">symtable</span>:<span class="id"
type="var">string</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span>) (<span class="id" type="var">xs</span>
: <span class="id" type="var">list</span> <span class="id"
type="var">token</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">steps</span> <span class="id" type="keyword">with</span>\
   | 0 ⇒ <span class="id" type="var">NoneE</span> "Too many recursive
calls"\
   | <span class="id" type="var">S</span> <span class="id"
type="var">steps'</span> ⇒\
     <span class="id" type="var">DO</span> (<span class="id"
type="var">u</span>, <span class="id" type="var">rest</span>) \<-- <span
class="id" type="var">expect</span> "SKIP" <span class="id"
type="var">xs</span>;\
       <span class="id" type="var">SomeE</span> (<span class="id"
type="var">SKIP</span>, <span class="id" type="var">rest</span>)\
     <span class="id" type="var">OR</span> <span class="id"
type="var">DO</span> (<span class="id" type="var">e</span>,<span
class="id" type="var">rest</span>) \<--\
          <span class="id" type="var">firstExpect</span> "IF" (<span
class="id" type="var">parseBExp</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">xs</span>;\
        <span class="id" type="var">DO</span> (<span class="id"
type="var">c</span>,<span class="id" type="var">rest'</span>) \<==\
          <span class="id" type="var">firstExpect</span> "THEN" (<span
class="id" type="var">parseSequencedCommand</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">rest</span>;\
        <span class="id" type="var">DO</span> (<span class="id"
type="var">c'</span>,<span class="id" type="var">rest''</span>) \<==\
          <span class="id" type="var">firstExpect</span> "ELSE" (<span
class="id" type="var">parseSequencedCommand</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">rest'</span>;\
        <span class="id" type="var">DO</span> (<span class="id"
type="var">u</span>,<span class="id" type="var">rest'''</span>) \<==\
          <span class="id" type="var">expect</span> "END" <span
class="id" type="var">rest''</span>;\
        <span class="id" type="var">SomeE</span>(<span class="id"
type="var">IFB</span> <span class="id" type="var">e</span> <span
class="id" type="var">THEN</span> <span class="id" type="var">c</span>
<span class="id" type="var">ELSE</span> <span class="id"
type="var">c'</span> <span class="id" type="var">FI</span>, <span
class="id" type="var">rest'''</span>)\
     <span class="id" type="var">OR</span> <span class="id"
type="var">DO</span> (<span class="id" type="var">e</span>,<span
class="id" type="var">rest</span>) \<--\
          <span class="id" type="var">firstExpect</span> "WHILE" (<span
class="id" type="var">parseBExp</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">xs</span>;\
        <span class="id" type="var">DO</span> (<span class="id"
type="var">c</span>,<span class="id" type="var">rest'</span>) \<==\
          <span class="id" type="var">firstExpect</span> "DO" (<span
class="id" type="var">parseSequencedCommand</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">rest</span>;\
        <span class="id" type="var">DO</span> (<span class="id"
type="var">u</span>,<span class="id" type="var">rest''</span>) \<==\
          <span class="id" type="var">expect</span> "END" <span
class="id" type="var">rest'</span>;\
        <span class="id" type="var">SomeE</span>(<span class="id"
type="var">WHILE</span> <span class="id" type="var">e</span> <span
class="id" type="var">DO</span> <span class="id" type="var">c</span>
<span class="id" type="var">END</span>, <span class="id"
type="var">rest''</span>)\
     <span class="id" type="var">OR</span> <span class="id"
type="var">DO</span> (<span class="id" type="var">i</span>, <span
class="id" type="var">rest</span>) \<==\
          <span class="id" type="var">parseIdentifier</span> <span
class="id" type="var">symtable</span> <span class="id"
type="var">xs</span>;\
        <span class="id" type="var">DO</span> (<span class="id"
type="var">e</span>, <span class="id" type="var">rest'</span>) \<==\
          <span class="id" type="var">firstExpect</span> ":=" (<span
class="id" type="var">parseAExp</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">rest</span>;\
        <span class="id" type="var">SomeE</span>(<span class="id"
type="var">i</span> ::= <span class="id" type="var">e</span>, <span
class="id" type="var">rest'</span>)\
   <span class="id" type="keyword">end</span>\
\
 <span class="id" type="keyword">with</span> <span class="id"
type="var">parseSequencedCommand</span> (<span class="id"
type="var">steps</span>:<span class="id" type="var">nat</span>) (<span
class="id" type="var">symtable</span>:<span class="id"
type="var">string</span><span style="font-family: arial;">→</span><span
class="id" type="var">nat</span>) (<span class="id" type="var">xs</span>
: <span class="id" type="var">list</span> <span class="id"
type="var">token</span>) :=\
   <span class="id" type="keyword">match</span> <span class="id"
type="var">steps</span> <span class="id" type="keyword">with</span>\
   | 0 ⇒ <span class="id" type="var">NoneE</span> "Too many recursive
calls"\
   | <span class="id" type="var">S</span> <span class="id"
type="var">steps'</span> ⇒\
       <span class="id" type="var">DO</span> (<span class="id"
type="var">c</span>, <span class="id" type="var">rest</span>) \<==\
         <span class="id" type="var">parseSimpleCommand</span> <span
class="id" type="var">steps'</span> <span class="id"
type="var">symtable</span> <span class="id" type="var">xs</span>;\
       <span class="id" type="var">DO</span> (<span class="id"
type="var">c'</span>, <span class="id" type="var">rest'</span>) \<--\
         <span class="id" type="var">firstExpect</span> ";;" (<span
class="id" type="var">parseSequencedCommand</span> <span class="id"
type="var">steps'</span> <span class="id" type="var">symtable</span>)
<span class="id" type="var">rest</span>;\
         <span class="id" type="var">SomeE</span>(<span class="id"
type="var">c</span> ;; <span class="id" type="var">c'</span>, <span
class="id" type="var">rest'</span>)\
       <span class="id" type="var">OR</span>\
         <span class="id" type="var">SomeE</span>(<span class="id"
type="var">c</span>, <span class="id" type="var">rest</span>)\
   <span class="id" type="keyword">end</span>.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">bignumber</span> := 1000.\
\
 <span class="id" type="keyword">Definition</span> <span class="id"
type="var">parse</span> (<span class="id" type="var">str</span> : <span
class="id" type="var">string</span>) : <span class="id"
type="var">optionE</span> (<span class="id" type="var">com</span> ×
<span class="id" type="var">list</span> <span class="id"
type="var">token</span>) :=\
   <span class="id" type="keyword">let</span> <span class="id"
type="var">tokens</span> := <span class="id" type="var">tokenize</span>
<span class="id" type="var">str</span> <span class="id"
type="keyword">in</span>\
   <span class="id" type="var">parseSequencedCommand</span> <span
class="id" type="var">bignumber</span> (<span class="id"
type="var">build\_symtable</span> <span class="id"
type="var">tokens</span> 0) <span class="id" type="var">tokens</span>.\
\

</div>

<div class="doc">

Examples {.section}
========

</div>

<div class="code code-space">

\
 <span class="comment">(\*\
 Eval compute in parse "\
     IF x == y + 1 + 2 - y \* 6 + 3 THEN\
       x := x \* 1;;\
       y := 0\
     ELSE\
       SKIP\
     END  ".\
 ====\>\
     SomeE\
        (IFB BEq (AId (Id 0))\
                 (APlus\

                   (AMinus (APlus (APlus (AId (Id 1)) (ANum 1)) (ANum 2))\
                       (AMult (AId (Id 1)) (ANum 6))) \
                    (ANum 3))\
         THEN Id 0 ::= AMult (AId (Id 0)) (ANum 1);; Id 1 ::= ANum 0\
         ELSE SKIP FI, <span class="inlinecode"></span>)\
 \*)</span>\
\
 <span class="comment">(\*\
 Eval compute in parse "\
     SKIP;;\
     z:=x\*y\*(x\*x);;\
     WHILE x==x DO\
       IF z \<= z\*z && not x == 2 THEN\
         x := z;;\
         y := z\
       ELSE\
         SKIP\
       END;;\
       SKIP\
     END;;\
     x:=z  ".\
 ====\> \
      SomeE\
         (SKIP;;\
          Id 0 ::= AMult (AMult (AId (Id 1)) (AId (Id 2)))\
                         (AMult (AId (Id 1)) (AId (Id 1)));;\
          WHILE BEq (AId (Id 1)) (AId (Id 1)) DO \

           IFB BAnd (BLe (AId (Id 0)) (AMult (AId (Id 0)) (AId (Id 0))))\
                      (BNot (BEq (AId (Id 1)) (ANum 2)))\
               THEN Id 1 ::= AId (Id 0);; Id 2 ::= AId (Id 0) \
               ELSE SKIP FI;; \
            SKIP \
          END;; \
          Id 1 ::= AId (Id 0), \
         <span class="inlinecode"></span>) \
 \*)</span>\
\
 <span class="comment">(\*\
 Eval compute in parse "\
    SKIP;;\
    z:=x\*y\*(x\*x);;\
    WHILE x==x DO\
      IF z \<= z\*z && not x == 2 THEN\
        x := z;;\
        y := z\
      ELSE\
        SKIP\
      END;;\
      SKIP\
    END;;\
    x:=z  ".\
 =====\> \
       SomeE\
          (SKIP;;\
           Id 0 ::= AMult (AMult (AId (Id 1)) (AId (Id 2)))\
                 (AMult (AId (Id 1)) (AId (Id 1)));;\
           WHILE BEq (AId (Id 1)) (AId (Id 1)) DO \

            IFB BAnd (BLe (AId (Id 0)) (AMult (AId (Id 0)) (AId (Id 0))))\
                      (BNot (BEq (AId (Id 1)) (ANum 2)))\
               THEN Id 1 ::= AId (Id 0);; \
                    Id 2 ::= AId (Id 0) \
               ELSE SKIP \
             FI;; \
             SKIP \
           END;;\
           Id 1 ::= AId (Id 0), \
          <span class="inlinecode"></span>).\
 \*)</span>\
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
