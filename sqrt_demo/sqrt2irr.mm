
  $( Declare the primitive constant symbols for propositional calculus. $)
  $c ( $.  $( Left parenthesis $)
  $c ) $.  $( Right parenthesis $)
  $c -> $.  $( Right arrow (read:  "implies") $)
  $c -. $.  $( Right handle (read:  "not") $)
  $c wff $.  $( Well-formed formula symbol (read:  "the following symbol
                sequence is a wff") $)
  $c |- $.

  $( $j
    syntax 'wff';
    syntax '|-' as 'wff';
    unambiguous 'klr 5';
  $)

  $( Introduce some variable names we will use to represent well-formed
     formulas (wff's). $)
  $v ph $.  $( Greek phi $)
  $v ps $.  $( Greek psi $)
  $v ch $.  $( Greek chi $)
  $v th $.  $( Greek theta $)
  $v ta $.  $( Greek tau $)
  $v et $.  $( Greek eta $)
  $v ze $.  $( Greek zeta $)
  $v si $.  $( Greek sigma $)
  $v rh $.  $( Greek rho $)
  $v mu $.  $( Greek mu $)
  $v la $.  $( Greek lambda $)
  $v ka $.
  $( Let variable ` ph ` be a wff. $)
  wph $f wff ph $.
  $( Let variable ` ps ` be a wff. $)
  wps $f wff ps $.
  $( Let variable ` ch ` be a wff. $)
  wch $f wff ch $.
  $( Let variable ` th ` be a wff. $)
  wth $f wff th $.
  $( Let variable ` ta ` be a wff. $)
  wta $f wff ta $.
  $( Let variable ` et ` be a wff. $)
  wet $f wff et $.
  $( Let variable ` ze ` be a wff. $)
  wze $f wff ze $.
  $( Let variable ` si ` be a wff. $)
  wsi $f wff si $.
  $( Let variable ` rh ` be a wff. $)
  wrh $f wff rh $.
  $( Let variable ` mu ` be a wff. $)
  wmu $f wff mu $.
  $( Let variable ` la ` be a wff. $)
  wla $f wff la $.
  $( Let variable ` ka ` be a wff. $)
  wka $f wff ka $.



$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Propositional calculus
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  Propositional calculus deals with general truths about well-formed formulas
  (wffs) regardless of how they are constructed.  The simplest propositional
  truth is ` ( ph -> ph ) ` , which can be read "if something is true, then it
  is true" - rather trivial and obvious, but nonetheless it must be proved from
  the axioms (see Theorem id
 ~ http://us.metamath.org/mpeuni/id.html
 ).

  Our system of propositional calculus consists of three basic axioms and
  another axiom that defines the modus-ponens inference rule.  It is attributed
  to Jan Lukasiewicz (pronounced woo-kah-SHAY-vitch) and was popularized by
  Alonzo Church, who called it system P2.  (Thanks to Ted Ulrich for this
  information.)  These axioms are ax-1
 ~ http://us.metamath.org/mpeuni/ax-1.html
 , ax-2
 ~ http://us.metamath.org/mpeuni/ax-2.html
 , ax-3
 ~ http://us.metamath.org/mpeuni/ax-3.html
 , and (for modus
  ponens) ax-mp
 ~ http://us.metamath.org/mpeuni/ax-mp.html
 . Some closely followed texts include [Margaris] for the
  axioms and [WhiteheadRussell] for the theorems.

  The propositional calculus used here is the classical system widely used by
  mathematicians.  In particular, this logic system accepts the "law of the
  excluded middle" as proven in exmid
 ~ http://us.metamath.org/mpeuni/exmid.html
 , which says that a logical statement
  is either true or not true.  This is an essential distinction of classical
  logic and is not a theorem of intuitionistic logic.

  All 194 axioms, definitions, and theorems for propositional calculus in
  _Principia Mathematica_ (specifically *1.2 through *5.75) are axioms or
  formally proven.  See the Bibliographic Cross-References at ~ mmbiblio.html
  for a complete cross-reference from sources used to its formalization in the
  Metamath Proof Explorer.

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Recursively define primitive wffs for propositional calculus
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( If ` ph ` is a wff, so is ` -. ph ` or "not ` ph ` ".  Part of the
     recursive definition of a wff (well-formed formula).  In classical logic
     (which is our logic), a wff is interpreted as either true or false.  So if
     ` ph ` is true, then ` -. ph ` is false; if ` ph ` is false, then
     ` -. ph ` is true.  Traditionally, Greek letters are used to represent
     wffs, and we follow this convention.  In propositional calculus, we define
     only wffs built up from other wffs, i.e. there is no starting or "atomic"
     wff.  Later, in predicate calculus, we will extend the basic wff
     definition by including atomic wffs ( weq
 ~ http://us.metamath.org/mpeuni/weq.html
 and wel
 ~ http://us.metamath.org/mpeuni/wel.html
 ). $)
  wn $a wff -. ph $.

  $( If ` ph ` and ` ps ` are wff's, so is ` ( ph -> ps ) ` or " ` ph ` implies
     ` ps ` ".  Part of the recursive definition of a wff.  The resulting wff
     is (interpreted as) false when ` ph ` is true and ` ps ` is false; it is
     true otherwise.  Think of the truth table for an OR gate with input ` ph `
     connected through an inverter.  After we state the axioms of propositional
     calculus ( ax-1
 ~ http://us.metamath.org/mpeuni/ax-1.html
 , ax-2
 ~ http://us.metamath.org/mpeuni/ax-2.html
 , ax-3
 ~ http://us.metamath.org/mpeuni/ax-3.html
 , and ax-mp
 ~ http://us.metamath.org/mpeuni/ax-mp.html
 ) and define the
     biconditional ( df-bi
 ~ http://us.metamath.org/mpeuni/df-bi.html
 ), the constant true ` T. ` ( df-tru
 ~ http://us.metamath.org/mpeuni/df-tru.html
 ), and the
     constant false ` F. ` ( df-fal
 ~ http://us.metamath.org/mpeuni/df-fal.html
 ), we will be able to prove these truth
     table values: ` ( ( T. -> T. ) <-> T. ) ` ( truimtru
 ~ http://us.metamath.org/mpeuni/truimtru.html
 ),
     ` ( ( T. -> F. ) <-> F. ) ` ( truimfal
 ~ http://us.metamath.org/mpeuni/truimfal.html
 ), ` ( ( F. -> T. ) <-> T. ) `
     ( falimtru
 ~ http://us.metamath.org/mpeuni/falimtru.html
 ), and ` ( ( F. -> F. ) <-> T. ) ` ( falimfal
 ~ http://us.metamath.org/mpeuni/falimfal.html
 ).  These
     have straightforward meanings, for example, ` ( ( T. -> T. ) <-> T. ) `
     just means "the value of ` ( T. -> T. ) ` is ` T. ` ".

     The left-hand wff is called the antecedent, and the right-hand wff is
     called the consequent.  In the case of ` ( ph -> ( ps -> ch ) ) ` , the
     middle ` ps ` may be informally called either an antecedent or part of the
     consequent depending on context.  Contrast with ` <-> ` ( df-bi
 ~ http://us.metamath.org/mpeuni/df-bi.html
 ),
     ` /\ ` ( df-an
 ~ http://us.metamath.org/mpeuni/df-an.html
 ), and ` \/ ` ( df-or
 ~ http://us.metamath.org/mpeuni/df-or.html
 ).

     This is called "material implication" and the arrow is usually read as
     "implies".  However, material implication is not identical to the meaning
     of "implies" in natural language.  For example, the word "implies" may
     suggest a causal relationship in natural language.  Material implication
     does not require any causal relationship.  Also, note that in material
     implication, if the consequent is true then the wff is always true (even
     if the antecedent is false).  Thus, if "implies" means material
     implication, it is true that "if the moon is made of green cheese that
     implies that 5=5" (because 5=5).  Similarly, if the antecedent is false,
     the wff is always true.  Thus, it is true that, "if the moon is made of
     green cheese that implies that 5=7" (because the moon is not actually made
     of green cheese).  A contradiction implies anything ( pm2.21i
 ~ http://us.metamath.org/mpeuni/pm2.21i.html
 ).  In
     short, material implication has a very specific technical definition, and
     misunderstandings of it are sometimes called "paradoxes of logical
     implication". $)
  wi $a wff ( ph -> ps ) $.



$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical implication
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The results in this section are based on implication only, and avoid ax-3
 ~ http://us.metamath.org/mpeuni/ax-3.html
 ,
  so are intuitionistic.  The system { ax-mp
 ~ http://us.metamath.org/mpeuni/ax-mp.html
 , ax-1
 ~ http://us.metamath.org/mpeuni/ax-1.html
 , ax-2
 ~ http://us.metamath.org/mpeuni/ax-2.html
 } axiomatizes
  what is sometimes called "intuitionistic implicational calculus" or "minimal
  implicational calculus".

  In an implication, the wff before the arrow is called the "antecedent" and
  the wff after the arrow is called the "consequent".

$)


  ${
    a1i.1 $e |- ph $.
    $( Inference introducing an antecedent.  Inference associated with ax-1
 ~ http://us.metamath.org/mpeuni/ax-1.html
 .
       Its associated inference is a1ii
 ~ http://us.metamath.org/mpeuni/a1ii.html
 .  See ~ conventions for a definition
       of "associated inference".  (Contributed by NM, 29-Dec-1992.) $)
    a1i $a |- ( ps -> ph ) $.
  $}


  ${
    mpd.1 $e |- ( ph -> ps ) $.
    mpd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( A modus ponens deduction.  A translation of natural deduction rule
       ` -> ` E ( ` -> ` elimination), see ~ natded .  Deduction form of
       ax-mp
 ~ http://us.metamath.org/mpeuni/ax-mp.html
 .  Inference associated with a2i
 ~ http://us.metamath.org/mpeuni/a2i.html
 .  Commuted form of mpcom
 ~ http://us.metamath.org/mpeuni/mpcom.html
 .
       (Contributed by NM, 29-Dec-1992.) $)
    mpd $a |- ( ph -> ch ) $.
  $}


  ${
    $( First of 2 premises for ~ syl . $)
    syl.1 $e |- ( ph -> ps ) $.
    $( Second of 2 premises for ~ syl . $)
    syl.2 $e |- ( ps -> ch ) $.
    $( An inference version of the transitive laws for implication imim2
 ~ http://us.metamath.org/mpeuni/imim2.html
 and
       imim1
 ~ http://us.metamath.org/mpeuni/imim1.html
 (and imim1i
 ~ http://us.metamath.org/mpeuni/imim1i.html
 and imim2i
 ~ http://us.metamath.org/mpeuni/imim2i.html
 ), which Russell and Whitehead call
       "the principle of the syllogism ... because ... the syllogism in Barbara
       is derived from [[ ~ syl ]" (quote after Theorem *2.06 of
       [WhiteheadRussell] p. 101).  Some authors call this law a "hypothetical
       syllogism".  Its associated inference is mp2b
 ~ http://us.metamath.org/mpeuni/mp2b.html
 .

       (A bit of trivia: this is the most commonly referenced assertion in our
       database (13449 times as of 22-Jul-2021).  In second place is eqid
 ~ http://us.metamath.org/mpeuni/eqid.html
       (9597 times), followed by adantr
 ~ http://us.metamath.org/mpeuni/adantr.html
 (8861 times), syl2anc
 ~ http://us.metamath.org/mpeuni/syl2anc.html
 (7421 times),
       adantl
 ~ http://us.metamath.org/mpeuni/adantl.html
 (6403 times), and ~ simpr (5829 times).  The Metamath program
       command 'show usage' shows the number of references.)

       (Contributed by NM, 30-Sep-1992.)  (Proof shortened by Mel L. O'Cat,
       20-Oct-2011.)  (Proof shortened by Wolf Lammen, 26-Jul-2012.) $)
    syl $a |- ( ph -> ch ) $.
  $}


  ${
    syld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    syld.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Syllogism deduction.  Deduction associated with ~ syl .  See
       ~ conventions for the meaning of "associated deduction" or "deduction
       form".  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Mel L.
       O'Cat, 19-Feb-2008.)  (Proof shortened by Wolf Lammen, 3-Aug-2012.) $)
    syld $a |- ( ph -> ( ps -> th ) ) $.

  $}

  ${
    mp2d.1 $e |- ( ph -> ps ) $.
    mp2d.2 $e |- ( ph -> ch ) $.
    mp2d.3 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.
    $( A double modus ponens deduction.  Deduction associated with mp2
 ~ http://us.metamath.org/mpeuni/mp2.html
 .
       (Contributed by NM, 23-May-2013.)  (Proof shortened by Wolf Lammen,
       23-Jul-2013.) $)
    mp2d $a |- ( ph -> th ) $.
  $}


  ${
    embantd.1 $e |- ( ph -> ps ) $.
    embantd.2 $e |- ( ph -> ( ch -> th ) ) $.
    $( Deduction embedding an antecedent.  (Contributed by Wolf Lammen,
       4-Oct-2013.) $)
    embantd $a |- ( ph -> ( ( ps -> ch ) -> th ) ) $.
  $}



  ${
    com3.1 $e |- ( ph -> ( ps -> ( ch -> th ) ) ) $.


    $( Commutation of antecedents.  Swap 1st and 3rd.  (Contributed by NM,
       25-Apr-1994.)  (Proof shortened by Wolf Lammen, 28-Jul-2012.) $)
    com13 $a |- ( ch -> ( ps -> ( ph -> th ) ) ) $.

  $}




$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical negation
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section makes our first use of the third axiom of propositional
  calculus, ax-3
 ~ http://us.metamath.org/mpeuni/ax-3.html
 .  It introduces logical negation.

$)



  ${
    pm2.21d.1 $e |- ( ph -> -. ps ) $.
    $( A contradiction implies anything.  Deduction associated with pm2.21
 ~ http://us.metamath.org/mpeuni/pm2.21.html
 .
       (Contributed by NM, 10-Feb-1996.) $)
    pm2.21d $a |- ( ph -> ( ps -> ch ) ) $.
  $}




$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical equivalence
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Definition df-bi
 ~ http://us.metamath.org/mpeuni/df-bi.html
 in this section is our first definition, which
  introduces and defines the biconditional connective ` <-> ` used to denote
  logical equivalence.  We define a wff of the form ` ( ph <-> ps ) ` as an
  abbreviation for ` -. ( ( ph -> ps ) -> -. ( ps -> ph ) ) ` .

  Unlike most traditional developments, we have chosen not to have a separate
  symbol such as "Df." to mean "is defined as".  Instead, we will later use the
  biconditional connective for this purpose ( df-an
 ~ http://us.metamath.org/mpeuni/df-an.html
 is its first use), as it
  allows to use logic to manipulate definitions directly.  This greatly
  simplifies many proofs since it eliminates the need for a separate mechanism
  for introducing and eliminating definitions.

  A note on definitions: definitions are required to be eliminable (that is, a
  theorem stated in terms of the defined symbol can also be stated without it)
  and conservative (that is, a theorem whose statement does not contain the
  defined symbol can be proved without using that definition).  This means that
  a definition does not increase the expressive power nor the deductive power,
  respectively, of a theory.  On the other hand, definitions are often useful
  to write shorter proofs, so in (i)set.mm we will generally not try to avoid
  them.  This is why, for instance, some theorems which do not contain
  disjunction in their statement are placed after the section on disjunction
  because a shorter proof using disjunction is possible.

$)

  $( Declare the biconditional connective. $)
  $c <-> $.

  $( Extend wff definition to include the biconditional connective. $)
  wb $a wff ( ph <-> ps ) $.


  ${
    imbitrrdi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    imbitrrdi.2 $e |- ( th <-> ch ) $.
    $( A mixed syllogism inference from a nested implication and a
       biconditional.  Useful for substituting an embedded consequent with a
       definition.  (Contributed by NM, 5-Aug-1993.) $)
    imbitrrdi $a |- ( ph -> ( ps -> th ) ) $.
  $}



  ${
    mpbird.min $e |- ( ph -> ch ) $.
    mpbird.maj $e |- ( ph -> ( ps <-> ch ) ) $.
    $( A deduction from a biconditional, related to modus ponens.  (Contributed
       by NM, 5-Aug-1993.) $)
    mpbird $a |- ( ph -> ps ) $.
  $}


  ${
    sylibrd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    sylibrd.2 $e |- ( ph -> ( th <-> ch ) ) $.
    $( A syllogism deduction.  (Contributed by NM, 3-Aug-1994.) $)
    sylibrd $a |- ( ph -> ( ps -> th ) ) $.
  $}


  ${
    bitri.1 $e |- ( ph <-> ps ) $.
    bitri.2 $e |- ( ps <-> ch ) $.
    $( An inference from transitive law for logical equivalence.  (Contributed
       by NM, 3-Jan-1993.)  (Proof shortened by Wolf Lammen, 13-Oct-2012.) $)
    bitri $a |- ( ph <-> ch ) $.
  $}


  ${
    bitr3d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitr3d.2 $e |- ( ph -> ( ps <-> th ) ) $.
    $( Deduction form of bitr3i
 ~ http://us.metamath.org/mpeuni/bitr3i.html
 .  (Contributed by NM, 14-May-1993.) $)
    bitr3d $a |- ( ph -> ( ch <-> th ) ) $.
  $}


  ${
    bitrdi.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    bitrdi.2 $e |- ( ch <-> th ) $.
    $( A syllogism inference from two biconditionals.  (Contributed by NM,
       12-Mar-1993.) $)
    bitrdi $a |- ( ph -> ( ps <-> th ) ) $.
  $}


  ${
    mtbir.1 $e |- -. ps $.
    mtbir.2 $e |- ( ph <-> ps ) $.
    $( An inference from a biconditional, related to modus tollens.
       (Contributed by NM, 15-Nov-1994.)  (Proof shortened by Wolf Lammen,
       14-Oct-2012.) $)
    mtbir $a |- -. ph $.
  $}


  ${
    imbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.


    $( Deduction adding a consequent to both sides of a logical equivalence.
       (Contributed by NM, 11-May-1993.)  (Proof shortened by Wolf Lammen,
       17-Sep-2013.) $)
    imbi1d $a |- ( ph -> ( ( ps -> th ) <-> ( ch -> th ) ) ) $.

  $}

  ${
    imbi12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    imbi12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Deduction joining two equivalences to form equivalence of implications.
       (Contributed by NM, 16-May-1993.) $)
    imbi12d $a |- ( ph -> ( ( ps -> th ) <-> ( ch -> ta ) ) ) $.

  $}




$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical conjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section defines conjunction of two formulas, denoted by infix " ` /\ ` "
  and read "and".  It is defined in terms of implication and negation, which is
  possible in classical logic (but not in intuitionistic logic: see iset.mm).

  After the definition, we briefly introduce conversion of simple expressions
  to and from conjunction.  Two simple operations called importation ( imp
 ~ http://us.metamath.org/mpeuni/imp.html
 )
  and exportation ( ~ ex ) follow.  In the propositions-as-types
  interpretation, they correspond to uncurrying and currying respectively. They
  are foundational for this section.  Most of the theorems proved here trace
  back to them, mostly indirectly, in a layered fashion, where more complex
  expressions are built from simpler ones.  Here are some of these successive
  layers:
  importation and exportation,
  commutativity and associativity laws,
  adding antecedents and simplifying,
  conjunction of consequents,
  syllogisms,
  etc.

  As indicated in the "note on definitions" in the section comment for logical
  equivalence, some theorems containing only implication, negation and
  conjunction are placed in the section after disjunction since theirs proofs
  use disjunction (although this is not required since definitions are
  conservative, see said section comment).

$)

  $( Declare connective for conjunction ("and"). $)
  $c /\ $.

  $( Extend wff definition to include conjunction ("and"). $)
  wa $a wff ( ph /\ ps ) $.


  ${
    ex.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Exportation inference.  (This theorem used to be labeled "exp" but was
       changed to "ex" so as not to conflict with the math token "exp", per the
       June 2006 Metamath spec change.)  A translation of natural deduction
       rule ` -> ` I ( ` -> ` introduction), see ~ natded .  (Contributed by
       NM, 3-Jan-1993.)  (Proof shortened by Eric Schmidt, 22-Dec-2006.) $)
    ex $a |- ( ph -> ( ps -> ch ) ) $.

  $}



  ${
    ancoms.1 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Inference commuting conjunction in antecedent.  (Contributed by NM,
       21-Apr-1994.) $)
    ancoms $a |- ( ( ps /\ ph ) -> ch ) $.
  $}


  $( Elimination of a conjunct.  Theorem *3.27 (Simp) of [WhiteheadRussell]
     p. 112.  (Contributed by NM, 3-Jan-1993.)  (Proof shortened by Wolf
     Lammen, 14-Jun-2022.) $)
  simpr $a |- ( ( ph /\ ps ) -> ps ) $.



  ${
    simpld.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  A translation of natural deduction
       rule ` /\ ` EL ( ` /\ ` elimination left), see ~ natded .  (Contributed
       by NM, 26-May-1993.) $)
    simpld $a |- ( ph -> ps ) $.
  $}

  ${
    simprd.1 $e |- ( ph -> ( ps /\ ch ) ) $.
    $( Deduction eliminating a conjunct.  (Contributed by NM, 14-May-1993.)  A
       translation of natural deduction rule ` /\ ` ER ( ` /\ ` elimination
       right), see ~ natded .  (Proof shortened by Wolf Lammen, 3-Oct-2013.) $)
    simprd $a |- ( ph -> ch ) $.
  $}


  ${
    jca.1 $e |- ( ph -> ps ) $.
    jca.2 $e |- ( ph -> ch ) $.
    $( Deduce conjunction of the consequents of two implications ("join
       consequents with 'and'").  Deduction form of pm3.2
 ~ http://us.metamath.org/mpeuni/pm3.2.html
 and pm3.2i
 ~ http://us.metamath.org/mpeuni/pm3.2i.html
 .  Its
       associated deduction is jcad
 ~ http://us.metamath.org/mpeuni/jcad.html
 .  Equivalent to the natural deduction
       rule ` /\ ` I ( ` /\ ` introduction), see ~ natded .  (Contributed by
       NM, 3-Jan-1993.)  (Proof shortened by Wolf Lammen, 25-Oct-2012.) $)
    jca $a |- ( ph -> ( ps /\ ch ) ) $.
  $}


  ${
    ancld.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction conjoining antecedent to left of consequent in nested
       implication.  (Contributed by NM, 15-Aug-1994.)  (Proof shortened by
       Wolf Lammen, 1-Nov-2012.) $)
    ancld $a |- ( ph -> ( ps -> ( ps /\ ch ) ) ) $.
  $}


  ${
    sylanbrc.1 $e |- ( ph -> ps ) $.
    sylanbrc.2 $e |- ( ph -> ch ) $.
    sylanbrc.3 $e |- ( th <-> ( ps /\ ch ) ) $.
    $( Syllogism inference.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    sylanbrc $a |- ( ph -> th ) $.
  $}


  ${
    syl2an.1 $e |- ( ph -> ps ) $.
    syl2an.2 $e |- ( ta -> ch ) $.
    syl2an.3 $e |- ( ( ps /\ ch ) -> th ) $.
    $( A double syllogism inference.  For an implication-only version, see
       syl2im
 ~ http://us.metamath.org/mpeuni/syl2im.html
 .  (Contributed by NM, 31-Jan-1997.) $)
    syl2an $a |- ( ( ph /\ ta ) -> th ) $.

  $}


  ${
    ad2ant.1 $e |- ( ph -> ps ) $.
    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.)  (Proof shortened by Wolf Lammen, 20-Nov-2012.) $)
    ad2antrr $a |- ( ( ( ph /\ ch ) /\ th ) -> ps ) $.

    $( Deduction adding two conjuncts to antecedent.  (Contributed by NM,
       19-Oct-1999.)  (Proof shortened by Wolf Lammen, 20-Nov-2012.) $)
    ad2antlr $a |- ( ( ( ch /\ ph ) /\ th ) -> ps ) $.


  $}



  $( Simplification of a conjunction.  (Contributed by NM, 18-Mar-2007.) $)
  simpll $a |- ( ( ( ph /\ ps ) /\ ch ) -> ph ) $.


  $( Simplification of a conjunction.  (Contributed by NM, 20-Mar-2007.) $)
  simplr $a |- ( ( ( ph /\ ps ) /\ ch ) -> ps ) $.




$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Logical disjunction
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section defines disjunction of two formulas, denoted by infix " ` \/ ` "
  and read "or".  It is defined in terms of implication and negation, which is
  possible in classical logic (but not in intuitionistic logic: see iset.mm).
  This section contains only theorems proved without df-an
 ~ http://us.metamath.org/mpeuni/df-an.html
 (theorems that are
  proved using df-an
 ~ http://us.metamath.org/mpeuni/df-an.html
 are deferred to the next section).  Basic theorems that
  help simplifying and applying disjunction are olc
 ~ http://us.metamath.org/mpeuni/olc.html
 , orc
 ~ http://us.metamath.org/mpeuni/orc.html
 , and orcom
 ~ http://us.metamath.org/mpeuni/orcom.html
 .

  As mentioned in the "note on definitions" in the section comment for logical
  equivalence, all theorems in this and the previous section can be stated in
  terms of implication and negation only.  Additionally, in classical logic
  (but not in intuitionistic logic: see iset.mm), it is also possible to
  translate conjunction into disjunction and conversely via the De Morgan law
  anor
 ~ http://us.metamath.org/mpeuni/anor.html
 : conjunction and disjunction are dual connectives.  Either is
  sufficient to develop all propositional calculus of the logic (together with
  implication and negation).  In practice, conjunction is more efficient, its
  big advantage being the possibility to use it to group antecedents in a
  convenient way, using imp
 ~ http://us.metamath.org/mpeuni/imp.html
 and ~ ex as noted in the previous section.

  An illustration of the conservativity of df-an
 ~ http://us.metamath.org/mpeuni/df-an.html
 is given by orim12dALT
 ~ http://us.metamath.org/mpeuni/orim12dALT.html
 ,
  which is an alternate proof of orim12d
 ~ http://us.metamath.org/mpeuni/orim12d.html
 not using df-an
 ~ http://us.metamath.org/mpeuni/df-an.html
 .

$)

  $( Declare connectives for disjunction ("or"). $)
  $c \/ $.

  $( Extend wff definition to include disjunction ("or"). $)
  wo $a wff ( ph \/ ps ) $.




$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Mixed connectives
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  This section gathers theorems of propositional calculus which use (either in
  their statement or proof) mixed connectives (at least conjunction and
  disjunction).

  As noted in the "note on definitions" in the section comment for logical
  equivalence, some theorem statements may contain for instance only
  conjunction or only disjunction, but both definitions are used in their
  proofs to make them shorter (this is exemplified in orim12d
 ~ http://us.metamath.org/mpeuni/orim12d.html
 versus
  orim12dALT
 ~ http://us.metamath.org/mpeuni/orim12dALT.html
 ).  These theorems are mostly grouped at the beginning of this
  section.

  The family of theorems starting with animorl
 ~ http://us.metamath.org/mpeuni/animorl.html
 focus on the relation between
  conjunction and disjunction and can be seen as the starting point of mixed
  connectives in statements.  This sectioning is not rigorously true, since for
  instance the section begins with jaao
 ~ http://us.metamath.org/mpeuni/jaao.html
 and related theorems.

$)


  $( Disjunction of antecedents.  Compare Theorem *4.77 of [WhiteheadRussell]
     p. 121.  (Contributed by NM, 30-May-1994.)  (Proof shortened by Wolf
     Lammen, 9-Dec-2012.) $)
  jaob $a |- ( ( ( ph \/ ch ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) ) ) $.




$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  True and false constants
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Universal quantifier for use by df-tru
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Even though it is not ordinarily part of propositional calculus, the
  universal quantifier ` A. ` is introduced here so that the soundness of
  Definition df-tru
 ~ http://us.metamath.org/mpeuni/df-tru.html
 can be checked by the same algorithm that is used for
  predicate calculus.  Its first real use is in Definition df-ex
 ~ http://us.metamath.org/mpeuni/df-ex.html
 in the
  predicate calculus section below.  For those who want propositional calculus
  to be self-contained, i.e., to use wff variables only, the alternate
  Definition dftru2
 ~ http://us.metamath.org/mpeuni/dftru2.html
 may be adopted and this subsection moved down to the
  start of the subsection with wex
 ~ http://us.metamath.org/mpeuni/wex.html
 below.  However, the use of dftru2
 ~ http://us.metamath.org/mpeuni/dftru2.html
 as a
  definition requires a more elaborate definition checking algorithm that we
  prefer to avoid.

$)

  $( Declare new symbols needed for predicate calculus. $)
  $c A. $.  $( "inverted A" universal quantifier (read:  "for all") $)
  $c setvar $.

$( $j syntax 'setvar'; bound 'setvar'; $)

$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Equality predicate for use by df-tru
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  Even though it is not ordinarily part of propositional calculus, the equality
  predicate ` = ` is introduced here so that the soundness of definition
  df-tru
 ~ http://us.metamath.org/mpeuni/df-tru.html
 can be checked by the same algorithm as is used for predicate
  calculus.  Its first real use is in Theorem weq
 ~ http://us.metamath.org/mpeuni/weq.html
 in the predicate calculus
  section below.  For those who want propositional calculus to be
  self-contained, i.e., to use wff variables only, the alternate definition
  dftru2
 ~ http://us.metamath.org/mpeuni/dftru2.html
 may be adopted and this subsection moved down to just above weq
 ~ http://us.metamath.org/mpeuni/weq.html
  below.  However, the use of dftru2
 ~ http://us.metamath.org/mpeuni/dftru2.html
 as a definition requires a more
  elaborate definition checking algorithm that we prefer to avoid.

$)

  $c class $.

  $( $j syntax 'class'; $)

  ${
    $v x $.
    $( Let ` x ` be an individual variable (temporary declaration). $)
    vx.cv $f setvar x $.
    $( This syntax construction states that a variable ` x ` , which has been
       declared to be a setvar variable by $f statement vx, is also a class
       expression.  This can be justified informally as follows.  We know that
       the class builder ` { y | y e. x } ` is a class by cab
 ~ http://us.metamath.org/mpeuni/cab.html
 .  Since (when
       ` y ` is distinct from ` x ` ) we have ` x = { y | y e. x } ` by
       cvjust
 ~ http://us.metamath.org/mpeuni/cvjust.html
 , we can argue that the syntax " ` class x ` " can be viewed as
       an abbreviation for " ` class { y | y e. x } ` ".  See the discussion
       under the definition of class in [Jech] p. 4 showing that "Every set can
       be considered to be a class".

       While it is tempting and perhaps occasionally useful to view ~ cv as a
       "type conversion" from a setvar variable to a class variable, keep in
       mind that ~ cv is intrinsically no different from any other
       class-building syntax such as cab
 ~ http://us.metamath.org/mpeuni/cab.html
 , cun
 ~ http://us.metamath.org/mpeuni/cun.html
 , or c0
 ~ http://us.metamath.org/mpeuni/c0.html
 .

       For a general discussion of the theory of classes and the role of ~ cv ,
       see ~ mmset.html#class .

       (The description above applies to set theory, not predicate calculus.
       The purpose of introducing ` class x ` here, and not in set theory where
       it belongs, is to allow to express, i.e., "prove", the weq
 ~ http://us.metamath.org/mpeuni/weq.html
 of
       predicate calculus from the ~ wceq of set theory, so that we do not
       overload the ` = ` connective with two syntax definitions.  This is done
       to prevent ambiguity that would complicate some Metamath parsers.) $)
    cv $a class x $.
    $( $j primitive 'cv'; $)
  $}

  $( Declare the equality predicate symbol. $)
  $c = $.  $( Equal sign (read:  'is equal to') $)

  ${
    $v A $.
    $v B $.
    $( Temporary declarations of ` A ` and ` B ` . $)
    cA.wceq $f class A $.
    cB.wceq $f class B $.
    $( Extend wff definition to include class equality.

       For a general discussion of the theory of classes, see
       ~ mmset.html#class .

       (The purpose of introducing ` wff A = B ` here, and not in set theory
       where it belongs, is to allow to express, i.e., "prove", the weq
 ~ http://us.metamath.org/mpeuni/weq.html
 of
       predicate calculus in terms of the ~ wceq of set theory, so that we do
       not "overload" the ` = ` connective with two syntax definitions.  This
       is done to prevent ambiguity that would complicate some Metamath
       parsers.  For example, some parsers - although not the Metamath program
       - stumble on the fact that the ` = ` in ` x = y ` could be the ` = ` of
       either weq
 ~ http://us.metamath.org/mpeuni/weq.html
 or ~ wceq , although mathematically it makes no difference.
       The class variables ` A ` and ` B ` are introduced temporarily for the
       purpose of this definition but otherwise not used in predicate calculus.
       See df-cleq
 ~ http://us.metamath.org/mpeuni/df-cleq.html
 for more information on the set theory usage of
       ~ wceq .) $)
    wceq $a wff A = B $.
    $( $j primitive 'wceq'; $)
  $}




$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Predicate calculus with equality:  Tarski's system S2 (1 rule, 6 schemes)
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

  Here we extend the language of wffs with predicate calculus, which allows
  to talk about individual objects in a domain of discourse (which for us will
  be the universe of all sets, so we call them "setvar variables") and make
  true/false statements about predicates, which are relationships between
  objects, such as whether or not two objects are equal.  In addition, we
  introduce universal quantification ("for all", e.g., ax-4
 ~ http://us.metamath.org/mpeuni/ax-4.html
 ) in order to
  make statements about whether a wff holds for every object in the domain of
  discourse.  Later we introduce existential quantification ("there exists",
  df-ex
 ~ http://us.metamath.org/mpeuni/df-ex.html
 ) which is defined in terms of universal quantification.

  Our axioms are really axiom _schemes_, and our wff and setvar variables are
  metavariables ranging over expressions in an underlying "object language".
  This is explained here:  ~ mmset.html#axiomnote .

  Our axiom system starts with the predicate calculus axiom schemes system S2
  of Tarski defined in his 1965 paper, "A Simplified Formalization of Predicate
  Logic with Identity" [Tarski].  System S2 is defined in the last paragraph on
  p. 77, and repeated on p. 81 of [KalishMontague].  We do not include scheme
  B5 (our sp
 ~ http://us.metamath.org/mpeuni/sp.html
 ) of system S2 since [KalishMontague] shows it to be logically
  redundant (Lemma 9, p. 87, which we prove as Theorem spw
 ~ http://us.metamath.org/mpeuni/spw.html
 below).

  Theorem spw
 ~ http://us.metamath.org/mpeuni/spw.html
 can be used to prove any _instance_ of sp
 ~ http://us.metamath.org/mpeuni/sp.html
 having mutually
  distinct setvar variables and no wff metavariables.  However, it seems that
  sp
 ~ http://us.metamath.org/mpeuni/sp.html
 in its general form cannot be derived from only Tarski's schemes.  We do
  not include B5 i.e. sp
 ~ http://us.metamath.org/mpeuni/sp.html
 as part of what we call "Tarski's system" because we
  want it to be the smallest set of axioms that is logically complete with
  no redundancies.  We later prove sp
 ~ http://us.metamath.org/mpeuni/sp.html
 as Theorem ~ axc5 using the auxiliary
  axiom schemes that make our system metalogically complete.

  Our version of Tarski's system S2 consists of propositional calculus
  ( ax-mp
 ~ http://us.metamath.org/mpeuni/ax-mp.html
 , ax-1
 ~ http://us.metamath.org/mpeuni/ax-1.html
 , ax-2
 ~ http://us.metamath.org/mpeuni/ax-2.html
 , ax-3
 ~ http://us.metamath.org/mpeuni/ax-3.html
 ) plus ax-gen
 ~ http://us.metamath.org/mpeuni/ax-gen.html
 , ax-4
 ~ http://us.metamath.org/mpeuni/ax-4.html
 , ax-5
 ~ http://us.metamath.org/mpeuni/ax-5.html
 ,
  ax-6
 ~ http://us.metamath.org/mpeuni/ax-6.html
 , ax-7
 ~ http://us.metamath.org/mpeuni/ax-7.html
 , ax-8
 ~ http://us.metamath.org/mpeuni/ax-8.html
 , and ax-9
 ~ http://us.metamath.org/mpeuni/ax-9.html
 .  The last three are equality axioms
  that represent three sub-schemes of Tarski's scheme B8.  Due to its
  side-condition ("where ` ph ` is an atomic formula and ` ps ` is obtained by
  replacing an occurrence of the variable ` x ` by the variable ` y ` "), we
  cannot represent his B8 directly without greatly complicating our scheme
  language, but the simpler schemes ax-7
 ~ http://us.metamath.org/mpeuni/ax-7.html
 , ax-8
 ~ http://us.metamath.org/mpeuni/ax-8.html
 , and ax-9
 ~ http://us.metamath.org/mpeuni/ax-9.html
 are sufficient
  for set theory and much easier to work with.

  Tarski's system is exactly equivalent to the traditional axiom system in most
  logic textbooks but has the advantage of being easy to manipulate with a
  computer program, and its simpler metalogic (with no built-in notions of
  "free variable" and "proper substitution") is arguably easier for a
  non-logician human to follow step by step in a proof (where "follow" means
  being able to identify the substitutions that were made, without necessarily
  a higher-level understanding).  In particular, it is logically complete in
  that it can derive all possible object-language theorems of predicate
  calculus with equality, i.e., the same theorems as the traditional system can
  derive.

  However, for efficiency (and indeed a key feature that makes Metamath
  successful), our system is designed to derive reusable theorem schemes
  (rather than object-language theorems) from other schemes.  From this
  "metalogical" point of view, Tarski's S2 is not complete.  For example, we
  cannot derive scheme sp
 ~ http://us.metamath.org/mpeuni/sp.html
 , even though (using spw
 ~ http://us.metamath.org/mpeuni/spw.html
 ) we can derive all
  instances of it that do not involve wff metavariables or bundled setvar
  variables.  (Two setvar variables are "bundled" if they can be substituted
  with the same setvar variable, i.e., do not have a "$d" disjoint variable
  condition.)  Later we will introduce auxiliary axiom schemes ax-10
 ~ http://us.metamath.org/mpeuni/ax-10.html
 ,
  ax-11
 ~ http://us.metamath.org/mpeuni/ax-11.html
 , ax-12
 ~ http://us.metamath.org/mpeuni/ax-12.html
 , and ax-13
 ~ http://us.metamath.org/mpeuni/ax-13.html
 that are metatheorems of Tarski's system
  (i.e. are logically redundant) but which give our system the property of
  "scheme completeness", allowing us to prove directly (instead of, say,
  by induction on formula length) all possible schemes that can be expressed in
  our language.

$)


$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Universal quantifier (continued); define "exists" and "not free"
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  The universal quantifier was introduced above in wal
 ~ http://us.metamath.org/mpeuni/wal.html
 for use by df-tru
 ~ http://us.metamath.org/mpeuni/df-tru.html
 .
  See the comments in that section.  In this section, we continue with the
  first "real" use of it.

$)

  $( Declare some names for individual variables. $)
  $v x $.
  $v y $.
  $v z $.
  $v w $.
  $v v $.
  $v u $.
  $v t $.
  $( Let ` x ` be an individual variable. $)
  vx $f setvar x $.
  $( Let ` y ` be an individual variable. $)
  vy $f setvar y $.
  $( Let ` z ` be an individual variable. $)
  vz $f setvar z $.
  $( Let ` w ` be an individual variable. $)
  vw $f setvar w $.
  $( Let ` v ` be an individual variable. $)
  vv $f setvar v $.
  $( Let ` u ` be an individual variable. $)
  vu $f setvar u $.
  $( Let ` t ` be an individual variable. $)
  vt $f setvar t $.


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Existential quantifier
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $( Declare the existential quantifier symbol. $)
  $c E. $.




$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Define proper substitution
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
  $( Left bracket $)
  $c / $.




$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Membership predicate
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the membership predicate symbol. $)
  $c e. $.  $( Stylized lowercase Greek letter epsilon. $)

  ${
    $v A $.
    $v B $.
    wcel.cA $f class A $.
    wcel.cB $f class B $.
    $( Extend wff definition to include the membership connective between
       classes.

       For a general discussion of the theory of classes, see
       ~ mmset.html#class .

       The purpose of introducing ` wff A e. B ` here is to allow to prove the
       wel
 ~ http://us.metamath.org/mpeuni/wel.html
 of predicate calculus in terms of the ~ wcel of set theory, so
       that we do not overload the ` e. ` connective with two syntax
       definitions.  This is done to prevent ambiguity that would complicate
       some Metamath parsers.  The class variables ` A ` and ` B ` are
       introduced temporarily for the purpose of this definition but otherwise
       not used in predicate calculus.  See df-clab
 ~ http://us.metamath.org/mpeuni/df-clab.html
 for more information on
       the set theory usage of ~ wcel . $)
    wcel $a wff A e. B $.
  $}


$(
###############################################################################
  ZF (ZERMELO-FRAENKEL) SET THEORY
###############################################################################

  Set theory uses the formalism of propositional and predicate calculus to
  assert properties of arbitrary mathematical objects called "sets".  A set can
  be an element of another set, and this relationship is indicated by the
  ` e. ` symbol.  Starting with the simplest mathematical object, called the
  empty set, set theory builds up more and more complex structures whose
  existence follows from the axioms, eventually resulting in extremely
  complicated sets that we identify with the real numbers and other familiar
  mathematical objects.

  A simplistic concept of sets, sometimes called "naive set theory", is
  vulnerable to a paradox called "Russell's Paradox" ( ru
 ~ http://us.metamath.org/mpeuni/ru.html
 ), a discovery that
  revolutionized the foundations of mathematics and logic.  Russell's Paradox
  spawned the development of set theories that countered the paradox, including
  the ZF set theory that is most widely used and is defined here.

  Except for Extensionality, the axioms basically say, "given an arbitrary set
  x (and, in the cases of Replacement and Regularity, provided that an
  antecedent is satisfied), there exists another set y based on or constructed
  from it, with the stated properties".  (The axiom of extensionality can also
  be restated this way as shown by axexte
 ~ http://us.metamath.org/mpeuni/axexte.html
 .) The individual axiom links
  provide more detailed descriptions.  We derive the redundant ZF axioms of
  Separation, Null Set, and Pairing from the others as theorems.

$)



$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  ZF Set Theory - start with the Axiom of Extensionality
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)




$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Classes
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)




$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Class equality
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-

  This section introduces class equality in df-cleq
 ~ http://us.metamath.org/mpeuni/df-cleq.html
 .

  Note that apart from the local introduction of class variables to state the
  syntax axioms ~ wceq and ~ wcel , this section is the first to use class
  variables.  Therefore, the file set.mm contains declarations of class
  variables at the beginning of this section (not visible on the webpages).

$)

  $( Declare variable symbols that will be used to represent classes.  Note
     that even though any class variable can be chosen to represent a class, it
     is usual to give mnemonic names, like using ` R ` and ` S ` for relations,
     ` F ` and ` G ` for functions, ` .0. ` for an additive identity, etc. $)
  $v ./\ $.
  $v .\/ $.
  $v .<_ $.
  $v .< $.
  $v .+ $.
  $v .- $.
  $v .X. $.
  $v ./ $.
  $v .^ $.
  $v .0. $.
  $v .1. $.
  $v .|| $.
  $v .~ $.
  $v ._|_ $.
  $v .+^ $.
  $v .+b $.
  $v .(+) $.
  $v .* $.
  $v .x. $.
  $v .xb $.
  $v ., $.
  $v .(x) $.
  $v .o. $.
  $v .0b $.

  $v A $.
  $v B $.
  $v C $.
  $v D $.
  $v P $.
  $v Q $.
  $v R $.
  $v S $.
  $v T $.
  $v U $.

  $( Let ` A ` be a class variable. $)
  cA $f class A $.
  $( Let ` B ` be a class variable. $)
  cB $f class B $.
  $( Let ` C ` be a class variable. $)
  cC $f class C $.

  $( Define a connective symbol for use as a class variable. $)
  c.pa $f class .|| $.

  $( Let ` D ` be a class variable. $)
  cD $f class D $.

  $( Define a connective symbol for use as a class variable. $)
  c.dv $f class ./ $.

  $( Let ` P ` be a class variable. $)
  cP $f class P $.

  $( Define a connective symbol for use as a class variable. $)
  c.pl $f class .+ $.
  $( Define a connective symbol for use as a class variable. $)
  c.pd $f class .+^ $.
  $( Define a connective symbol for use as a class variable. $)
  c.pb $f class .+b $.
  $( Define a connective symbol for use as a class variable. $)
  c.po $f class .(+) $.

  $( Let ` Q ` be a class variable. $)
  cQ $f class Q $.

  $( Define a connective symbol for use as a class variable. $)
  c.sm $f class .~ $.

  $( Let ` R ` be a class variable. $)
  cR $f class R $.
  $( Let ` S ` be a class variable. $)
  cS $f class S $.

  $( Define a connective symbol for use as a class variable. $)
  c.lt $f class .< $.
  $( Define a connective symbol for use as a class variable. $)
  c.xb $f class .xb $.

  $( Let ` T ` be a class variable. $)
  cT $f class T $.

  $( Define a connective symbol for use as a class variable. $)
  c.x $f class .x. $.
  $( Define a connective symbol for use as a class variable. $)
  c.xp $f class .X. $.
  $( Define a connective symbol for use as a class variable. $)
  c.xo $f class .(x) $.

  $( Let ` U ` be a class variable. $)
  cU $f class U $.

  $( Define a connective symbol for use as a class variable. $)
  c.1 $f class .1. $.

  $( Declare variable symbols that will be used to represent setvars. $)
  $v e $.
  $v f $.
  $v g $.
  $v h $.
  $v i $.
  $v j $.
  $v k $.
  $v m $.
  $v n $.
  $v o $.
  $v E $.
  $v F $.
  $v G $.
  $v H $.
  $v I $.
  $v J $.
  $v K $.
  $v L $.
  $v M $.
  $v N $.
  $v V $.
  $v W $.
  $v X $.
  $v Y $.
  $v Z $.
  $v O $.
  $v s $.
  $v r $.
  $v q $.
  $v p $.
  $v a $.
  $v b $.
  $v c $.
  $v d $.
  $v l $.

  $( Let ` e ` be an individual variable. $)
  ve $f setvar e $.
  $( Let ` f ` be an individual variable. $)
  vf $f setvar f $.
  $( Let ` g ` be an individual variable. $)
  vg $f setvar g $.
  $( Let ` h ` be an individual variable. $)
  vh $f setvar h $.
  $( Let ` i ` be an individual variable. $)
  vi $f setvar i $.
  $( Let ` j ` be an individual variable. $)
  vj $f setvar j $.
  $( Let ` k ` be an individual variable. $)
  vk $f setvar k $.
  $( Let ` m ` be an individual variable. $)
  vm $f setvar m $.
  $( Let ` n ` be an individual variable. $)
  vn $f setvar n $.
  $( Let ` o ` be an individual variable. $)
  vo $f setvar o $.

  $( Let ` E ` be a class variable. $)
  cE $f class E $.

  $( Define a connective symbol for use as a class variable. $)
  c.ex $f class .^ $.

  $( Let ` F ` be a class variable. $)
  cF $f class F $.
  $( Let ` G ` be a class variable. $)
  cG $f class G $.
  $( Let ` H ` be a class variable. $)
  cH $f class H $.

  $( Define a connective symbol for use as a class variable. $)
  c.xi $f class ., $.

  $( Let ` I ` be a class variable. $)
  cI $f class I $.

  $( Define a connective symbol for use as a class variable. $)
  c.as $f class .* $.

  $( Let ` J ` be a class variable. $)
  cJ $f class J $.

  $( Define a connective symbol for use as a class variable. $)
  c.or $f class .\/ $.

  $( Let ` K ` be a class variable. $)
  cK $f class K $.
  $( Let ` L ` be a class variable. $)
  cL $f class L $.

  $( Define a connective symbol for use as a class variable. $)
  c.le $f class .<_ $.

  $( Let ` M ` be a class variable. $)
  cM $f class M $.

  $( Define a connective symbol for use as a class variable. $)
  c.an $f class ./\ $.
  $( Define a connective symbol for use as a class variable. $)
  c.mi $f class .- $.

  $( Let ` N ` be a class variable. $)
  cN $f class N $.

  $( Define a connective symbol for use as a class variable. $)
  c.pe $f class ._|_ $.

  $( Let ` O ` be a class variable. $)
  cO $f class O $.
  $( Let ` V ` be a class variable. $)
  cV $f class V $.
  $( Let ` W ` be a class variable. $)
  cW $f class W $.
  $( Let ` X ` be a class variable. $)
  cX $f class X $.
  $( Let ` Y ` be a class variable. $)
  cY $f class Y $.

  $( Define a connective symbol for use as a class variable. $)
  c.0 $f class .0. $.
  $( Define a connective symbol for use as a class variable. $)
  c.0b $f class .0b $.
  $( Define a connective symbol for use as a class variable. $)
  c.op $f class .o. $.

  $( Let ` Z ` be a class variable. $)
  cZ $f class Z $.

  $( Let ` s ` be an individual variable. $)
  vs $f setvar s $.
  $( Let ` r ` be an individual variable. $)
  vr $f setvar r $.
  $( Let ` q ` be an individual variable. $)
  vq $f setvar q $.
  $( Let ` p ` be an individual variable. $)
  vp $f setvar p $.
  $( Let ` a ` be an individual variable. $)
  va $f setvar a $.
  $( Let ` b ` be an individual variable. $)
  vb $f setvar b $.
  $( Let ` c ` be an individual variable. $)
  vc $f setvar c $.
  $( Let ` d ` be an individual variable. $)
  vd $f setvar d $.
  $( Let ` l ` be an individual variable. $)
  vl $f setvar l $.


  ${
    eqtrd.1 $e |- ( ph -> A = B ) $.
    eqtrd.2 $e |- ( ph -> B = C ) $.
    $( An equality transitivity deduction.  (Contributed by NM,
       21-Jun-1993.) $)
    eqtrd $a |- ( ph -> A = C ) $.
  $}


  ${
    eqtr3d.1 $e |- ( ph -> A = B ) $.
    eqtr3d.2 $e |- ( ph -> A = C ) $.
    $( An equality transitivity equality deduction.  (Contributed by NM,
       18-Jul-1995.) $)
    eqtr3d $a |- ( ph -> B = C ) $.
  $}

  ${
    eqtr4d.1 $e |- ( ph -> A = B ) $.
    eqtr4d.2 $e |- ( ph -> C = B ) $.
    $( An equality transitivity equality deduction.  (Contributed by NM,
       18-Jul-1995.) $)
    eqtr4d $a |- ( ph -> A = C ) $.
  $}

  $( $j equality 'wceq' from 'eqid' 'eqcomi' 'eqtri'; $)


  ${
    3eqtr4d.1 $e |- ( ph -> A = B ) $.
    3eqtr4d.2 $e |- ( ph -> C = A ) $.
    3eqtr4d.3 $e |- ( ph -> D = B ) $.
    $( A deduction from three chained equalities.  (Contributed by NM,
       4-Aug-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    3eqtr4d $a |- ( ph -> C = D ) $.

  $}



$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Class membership
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


  ${
    eqeltrd.1 $e |- ( ph -> A = B ) $.
    eqeltrd.2 $e |- ( ph -> B e. C ) $.
    $( Substitution of equal classes into membership relation, deduction form.
       (Contributed by Raph Levien, 10-Dec-2002.) $)
    eqeltrd $a |- ( ph -> A e. C ) $.
  $}

  ${
    eqeltrrd.1 $e |- ( ph -> A = B ) $.
    eqeltrrd.2 $e |- ( ph -> A e. C ) $.
    $( Deduction that substitutes equal classes into membership.  (Contributed
       by NM, 14-Dec-2004.) $)
    eqeltrrd $a |- ( ph -> B e. C ) $.
  $}




$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Negated equality and membership
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)


$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Negated equality
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)

  $c =/= $.

  $( Extend wff notation to include inequality. $)
  wne $a wff A =/= B $.

  $( Define inequality.  (Contributed by NM, 26-May-1993.) $)
  df-ne $a |- ( A =/= B <-> -. A = B ) $.


  ${
    necon2ad.1 $e |- ( ph -> ( A = B -> -. ps ) ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       19-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.)  (Proof
       shortened by Wolf Lammen, 23-Nov-2019.) $)
    necon2ad $a |- ( ph -> ( ps -> A =/= B ) ) $.
  $}

  ${
    necon2bd.1 $e |- ( ph -> ( ps -> A =/= B ) ) $.
    $( Contrapositive inference for inequality.  (Contributed by NM,
       13-Apr-2007.) $)
    necon2bd $a |- ( ph -> ( A = B -> -. ps ) ) $.
  $}



  ${
    neeq1d.1 $e |- ( ph -> A = B ) $.


    $( Deduction for inequality.  (Contributed by NM, 25-Oct-1999.)  (Proof
       shortened by Wolf Lammen, 19-Nov-2019.) $)
    neeq2d $a |- ( ph -> ( C =/= A <-> C =/= B ) ) $.

  $}




$(
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
  Negated membership
-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-.-
$)


  $c e/ $.  $( Not an element of (membership symbol with slash through it). $)

  $( Extend wff notation to include negated membership. $)
  wnel $a wff A e/ B $.

  ${
    nelir.1 $e |- -. A e. B $.
    $( Inference associated with ~ df-nel .  (Contributed by BJ,
       7-Jul-2018.) $)
    nelir $a |- A e/ B $.
  $}

  $( Extend wff notation to include restricted universal quantification. $)
  wral $a wff A. x e. A ph $.

  ${
    rgen.1 $e |- ( x e. A -> ph ) $.
    $( Generalization rule for restricted quantification.  (Contributed by NM,
       19-Nov-1994.) $)
    rgen $a |- A. x e. A ph $.
  $}

  $( Extend wff notation to include restricted existential quantification. $)
  wrex $a wff E. x e. A ph $.

  $( Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.)  (Proof shortened by BJ,
     16-Jul-2021.) $)
  ralnex $a |- ( A. x e. A -. ph <-> -. E. x e. A ph ) $.

  ${
    nrex.1 $e |- ( x e. A -> -. ps ) $.
    $( Inference adding restricted existential quantifier to negated wff.
       (Contributed by NM, 16-Oct-2003.) $)
    nrex $a |- -. E. x e. A ps $.
  $}

  $( Restricted quantifier version of ~ 19.26 .  (Contributed by NM,
     28-Jan-1997.)  (Proof shortened by Andrew Salmon, 30-May-2011.) $)
  r19.26 $a |- ( A. x e. A ( ph /\ ps ) <->
               ( A. x e. A ph /\ A. x e. A ps ) ) $.

  ${
    $d x ph $.  $d x ps $.
    ralrimdva.1 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 2-Feb-2008.)  (Proof shortened
       by Wolf Lammen, 28-Dec-2019.) $)
    ralrimdva $a |- ( ph -> ( ps -> A. x e. A ch ) ) $.
  $}

  ${
    $d x ph $.
    ralbidva.1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted universal quantifier (deduction
       form).  (Contributed by NM, 4-Mar-1997.)  Reduce dependencies on axioms.
       (Revised by Wolf Lammen, 29-Dec-2019.) $)
    ralbidva $a |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $.
  $}

  ${
    $d x ph $.
    ralbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted universal quantifier (deduction
       form).  (Contributed by NM, 20-Nov-1994.)  Reduce dependencies on
       axioms.  (Revised by Wolf Lammen, 5-Dec-2019.) $)
    ralbidv $a |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $.
  $}

  ${
    $d x y A $.  $d y ph $.  $d x ps $.
    cbvralvw.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change the bound variable of a restricted universal quantifier using
       implicit substitution.  Version of ~ cbvralv with a disjoint variable
       condition, which does not require ~ ax-10 , ~ ax-11 , ~ ax-12 ,
       ~ ax-13 .  (Contributed by NM, 28-Jan-1997.)  Avoid ~ ax-13 .  (Revised
       by Gino Giotto, 10-Jan-2024.) $)
    cbvralvw $a |- ( A. x e. A ph <-> A. y e. A ps ) $.
    $( $j usage 'cbvralvw' avoids 'ax-10' 'ax-11' 'ax-12' 'ax-13'; $)
  $}

  ${
    $d x y $.  $d y A $.

    $d x B $.

    $( Commutation of restricted existential quantifiers.  (Contributed by NM,
       19-Nov-1995.)  (Revised by Mario Carneiro, 14-Oct-2016.)  (Proof
       shortened by BJ, 26-Aug-2023.)  (Proof shortened by Wolf Lammen,
       8-Dec-2024.) $)
    rexcom $a |- ( E. x e. A E. y e. B ph <-> E. y e. B E. x e. A ph ) $.
    $( $j usage 'rexcom' avoids 'ax-6' 'ax-7' 'ax-8' 'ax-9' 'ax-10' 'ax-12'
       'ax-13' 'ax-ext'; $)
  $}

  ${
    $d x A $.  $d x B $.  $d x ps $.
    ceqsralv.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Restricted quantifier version of ~ ceqsalv .  (Contributed by NM,
       21-Jun-2013.)  Avoid ~ ax-9 , ~ ax-12 , ~ ax-ext .  (Revised by SN,
       8-Sep-2024.) $)
    ceqsralv $a |- ( A e. B -> ( A. x e. B ( x = A -> ph ) <-> ps ) ) $.
    $( $j usage 'ceqsralv' avoids 'ax-9' 'ax-12' 'ax-ext'; $)
  $}

  ${
    $d x A $.  $d x B $.  $d x ps $.
    rspcv.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 26-May-1998.)  Drop ~ ax-10 , ~ ax-11 , ~ ax-12 .  (Revised by SN,
       12-Dec-2023.) $)
    rspcv $a |- ( A e. B -> ( A. x e. B ph -> ps ) ) $.
  $}

  $( Extend wff notation to include the general binary relation predicate.
     Note that the syntax is simply three class symbols in a row.  Since binary
     relations are the only possible wff expressions consisting of three class
     expressions in a row, the syntax is unambiguous.  (For an example of how
     syntax could become ambiguous if we are not careful, see the comment in
     ~ cneg .) $)
  wbr $a wff A R B $.

  $( Equality theorem for a binary relation.  (Contributed by NM,
     31-Dec-1993.) $)
  breq1 $a |- ( A = B -> ( A R C <-> B R C ) ) $.

  $( Equality theorem for a binary relation.  (Contributed by NM,
     31-Dec-1993.) $)
  breq2 $a |- ( A = B -> ( C R A <-> C R B ) ) $.

  $c ` $.  $( Left apostrophe or backtick, backquote (function value symbol) $)

  $( Extend the definition of a class to include the value of a function.
     Read:  "the value of ` F ` at ` A ` ", or " ` F ` of ` A ` ". $)
  cfv $a class ( F ` A ) $.

  $( Extend class notation to include the value of an operation ` F ` (such as
     ` + ` ) for two arguments ` A ` and ` B ` .  Note that the syntax is
     simply three class symbols in a row surrounded by parentheses.  Since
     operation values are the only possible class expressions consisting of
     three class expressions in a row surrounded by parentheses, the syntax is
     unambiguous.  (For an example of how syntax could become ambiguous if we
     are not careful, see the comment in ~ cneg .) $)
  co $a class ( A F B ) $.

  $( Equality theorem for operation value.  (Contributed by NM,
     28-Feb-1995.) $)
  oveq1 $a |- ( A = B -> ( A F C ) = ( B F C ) ) $.

  $( Equality theorem for operation value.  (Contributed by NM,
     28-Feb-1995.) $)
  oveq2 $a |- ( A = B -> ( C F A ) = ( C F B ) ) $.

  ${
    oveq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for operation value.  (Contributed by NM,
       13-Mar-1995.) $)
    oveq1d $a |- ( ph -> ( A F C ) = ( B F C ) ) $.

    $( Equality deduction for operation value.  (Contributed by NM,
       13-Mar-1995.) $)
    oveq2d $a |- ( ph -> ( C F A ) = ( C F B ) ) $.
  $}

  $c CC $. $( The set of complex numbers (blackboard bold C) $)
  $c RR $. $( The set of real numbers (blackboard bold R) $)
  $c 0 $. $( The real number 0. $)
  $c 1 $. $( The real number 1. $)
  $c + $. $( Plus (addition) symbol $)
  $c x. $. $( Multiplication symbol (center dot) $)

  $( Class of complex numbers. $)
  cc $a class CC $.
  $( Class of real numbers. $)
  cr $a class RR $.
  $( Extend class notation to include the complex number 0. $)
  cc0 $a class 0 $.
  $( Extend class notation to include the complex number 1. $)
  c1 $a class 1 $.

  $( Addition on complex numbers. $)
  caddc $a class + $.

  $( Multiplication on complex numbers.  The token ` x. ` is a center dot. $)
  cmul $a class x. $.

  $c <_ $. $( 'Less than or equal to' relation. $)
  $c < $. $( 'Less than' relation (over extended reals) $)

  $( 'Less than' predicate (extended to include the extended reals). $)
  clt $a class < $.
  $( Extend wff notation to include the 'less than or equal to' relation. $)
  cle $a class <_ $.

  $( 'Less than or equal to' expressed in terms of 'less than' or 'equals'.
     (Contributed by NM, 13-May-1999.) $)
  leloe $a |- ( ( A e. RR /\ B e. RR ) ->
               ( A <_ B <-> ( A < B \/ A = B ) ) ) $.

  $( Extend class notation to include division. $)
  cdiv $a class / $.

  ${
    div1d.1 $e |- ( ph -> A e. CC ) $.

    divcld.2 $e |- ( ph -> B e. CC ) $.
    ${
      divcld.3 $e |- ( ph -> B =/= 0 ) $.

      $( A cancellation law for division.  (Contributed by Mario Carneiro,
         27-May-2016.) $)
      divcan1d $a |- ( ph -> ( ( A / B ) x. B ) = A ) $.

      $( A cancellation law for division.  (Contributed by Mario Carneiro,
         27-May-2016.) $)
      divcan3d $a |- ( ph -> ( ( B x. A ) / B ) = A ) $.
    $}

    divmuld.3 $e |- ( ph -> C e. CC ) $.
    ${
      divmuld.4 $e |- ( ph -> B =/= 0 ) $.

      divdiv23d.5 $e |- ( ph -> C =/= 0 ) $.

      $( Cancel equal divisors in a division.  (Contributed by Mario Carneiro,
         27-May-2016.) $)
      divcan7d $a |- ( ph -> ( ( A / C ) / ( B / C ) ) = ( A / B ) ) $.

      $( Division into a fraction.  (Contributed by Mario Carneiro,
         27-May-2016.) $)
      divdiv1d $a |- ( ph -> ( ( A / B ) / C ) = ( A / ( B x. C ) ) ) $.
    $}
  $}

  ${
    ltp1d.1 $e |- ( ph -> A e. RR ) $.
    $( A number is less than itself plus 1.  (Contributed by Mario Carneiro,
       28-May-2016.) $)
    ltp1d $a |- ( ph -> A < ( A + 1 ) ) $.
  $}

  $c NN $. $( The set of positive integers (blackboard bold N). $)

  $( Extend class notation to include the class of positive integers. $)
  cn $a class NN $.

  $( A positive integer is a real number.  (Contributed by NM, 18-Aug-1999.) $)
  nnre $a |- ( A e. NN -> A e. RR ) $.

  $( A positive integer is a complex number.  (Contributed by NM,
     18-Aug-1999.) $)
  nncn $a |- ( A e. NN -> A e. CC ) $.

  ${
    $d x y z A $.

    $( Peano postulate: a successor of a positive integer is a positive
       integer.  (Contributed by NM, 11-Jan-1997.)  (Revised by Mario Carneiro,
       17-Nov-2014.) $)
    peano2nn $a |- ( A e. NN -> ( A + 1 ) e. NN ) $.
  $}

  ${
    nnred.1 $e |- ( ph -> A e. NN ) $.

    $( A positive integer is a complex number.  (Contributed by Mario Carneiro,
       27-May-2016.) $)
    nncnd $a |- ( ph -> A e. CC ) $.
  $}

  ${
    $d x y $.  $d x A $.  $d x ps $.  $d x ch $.  $d x th $.  $d x ta $.
    $d y ph $.
    $( Substitutions. $)
    nnind.1 $e |- ( x = 1 -> ( ph <-> ps ) ) $.
    nnind.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    nnind.3 $e |- ( x = ( y + 1 ) -> ( ph <-> th ) ) $.
    nnind.4 $e |- ( x = A -> ( ph <-> ta ) ) $.
    $( Basis. $)
    nnind.5 $e |- ps $.
    $( Induction step. $)
    nnind.6 $e |- ( y e. NN -> ( ch -> th ) ) $.
    $( Principle of Mathematical Induction (inference schema).  The first four
       hypotheses give us the substitution instances we need; the last two are
       the basis and the induction step.  See ~ nnaddcl for an example of its
       use.  See ~ nn0ind for induction on nonnegative integers and ~ uzind ,
       ~ uzind4 for induction on an arbitrary upper set of integers.  See
       ~ indstr for strong induction.  See also ~ nnindALT .  This is an
       alternative for Metamath 100 proof #74.  (Contributed by NM,
       10-Jan-1997.)  (Revised by Mario Carneiro, 16-Jun-2013.) $)
    nnind $a |- ( A e. NN -> ta ) $.
  $}

  $( A positive integer is not less than one.  (Contributed by NM,
     18-Jan-2004.)  (Revised by Mario Carneiro, 27-May-2016.) $)
  nnnlt1 $a |- ( A e. NN -> -. A < 1 ) $.

  ${
    $d x y A $.
    $( A positive integer is nonzero.  See ~ nnne0ALT for a shorter proof using
       ~ ax-pre-mulgt0 .  This proof avoids ~ 0lt1 , and thus ~ ax-pre-mulgt0 ,
       by splitting ~ ax-1ne0 into the two separate cases ` 0 < 1 ` and
       ` 1 < 0 ` .  (Contributed by NM, 27-Sep-1999.)  Remove dependency on
       ~ ax-pre-mulgt0 .  (Revised by Steven Nguyen, 30-Jan-2023.) $)
    nnne0 $a |- ( A e. NN -> A =/= 0 ) $.
  $}

  ${
    nnge1d.1 $e |- ( ph -> A e. NN ) $.

    $( A positive integer is nonzero.  (Contributed by Mario Carneiro,
       27-May-2016.) $)
    nnne0d $a |- ( ph -> A =/= 0 ) $.
  $}

  $c 2 $. $( The decimal number 2 $)

  $( Extend class notation to include the number 2. $)
  c2 $a class 2 $.

  $( The number 2 is a complex number, deduction form.  (Contributed by David
     A. Wheeler, 8-Dec-2018.) $)
  2cnd $a |- ( ph -> 2 e. CC ) $.

  $( The number 2 is nonzero.  (Contributed by NM, 9-Nov-2007.) $)
  2ne0 $a |- 2 =/= 0 $.

  $c ZZ $. $( The set of integers (blackboard bold Z). $)

  $( Extend class notation to include the class of integers. $)
  cz $a class ZZ $.

  $( An integer is a complex number.  (Contributed by NM, 9-May-2004.) $)
  zcn $a |- ( N e. ZZ -> N e. CC ) $.

  $( Positive integer property expressed in terms of integers.  (Contributed by
     NM, 8-Jan-2002.) $)
  elnnz $a |- ( N e. NN <-> ( N e. ZZ /\ 0 < N ) ) $.

  ${
    nnzd.1 $e |- ( ph -> A e. NN ) $.
    $( A positive integer is an integer.  (Contributed by Mario Carneiro,
       28-May-2016.) $)
    nnzd $a |- ( ph -> A e. ZZ ) $.
  $}

  $( Positive integer ordering relation.  (Contributed by NM, 13-Aug-2001.)
     (Proof shortened by Mario Carneiro, 16-May-2014.) $)
  nnleltp1 $a |- ( ( A e. NN /\ B e. NN ) ->
                ( A <_ B <-> A < ( B + 1 ) ) ) $.

  ${
    zred.1 $e |- ( ph -> A e. ZZ ) $.

    $( An integer is a complex number.  (Contributed by Mario Carneiro,
       28-May-2016.) $)
    zcnd $a |- ( ph -> A e. CC ) $.
  $}

  $c QQ $. $( The set of rational numbers (blackboard bold Q). $)

  $( Extend class notation to include the class of rationals. $)
  cq $a class QQ $.

  ${
    $d x y z A $.
    $( Membership in the set of rationals.  (Contributed by NM, 8-Jan-2002.)
       (Revised by Mario Carneiro, 28-Jan-2014.) $)
    elq $a |- ( A e. QQ <-> E. x e. ZZ E. y e. NN A = ( x / y ) ) $.
  $}

  $c RR+ $. $( The set of positive reals (blackboard bold R^+). $)

  $( Extend class notation to include the class of positive reals. $)
  crp $a class RR+ $.

  $( A positive integer is a positive real.  (Contributed by NM,
     28-Nov-2008.) $)
  nnrp $a |- ( A e. NN -> A e. RR+ ) $.

  $( Half of a positive real is less than the original number.  (Contributed by
     Mario Carneiro, 21-May-2014.) $)
  rphalflt $a |- ( A e. RR+ -> ( A / 2 ) < A ) $.

  ${
    nnrpd.1 $e |- ( ph -> A e. NN ) $.
    $( A positive integer is a positive real.  (Contributed by Mario Carneiro,
       28-May-2016.) $)
    nnrpd $a |- ( ph -> A e. RR+ ) $.
  $}

  ${
    rpred.1 $e |- ( ph -> A e. RR+ ) $.

    $( A positive real is greater than zero.  (Contributed by Mario Carneiro,
       28-May-2016.) $)
    rpgt0d $a |- ( ph -> 0 < A ) $.

    $( Closure law for half of a positive real.  (Contributed by Mario
       Carneiro, 28-May-2016.) $)
    rphalfcld $a |- ( ph -> ( A / 2 ) e. RR+ ) $.
  $}

  $c ^ $. $( Exponentiation. $)

  $( Extend class notation to include exponentiation of a complex number to an
     integer power. $)
  cexp $a class ^ $.

  $( Integers are closed under squaring.  (Contributed by Scott Fenton,
     18-Apr-2014.)  (Revised by Mario Carneiro, 19-Apr-2014.) $)
  zsqcl $a |- ( A e. ZZ -> ( A ^ 2 ) e. ZZ ) $.

  ${
    expcld.1 $e |- ( ph -> A e. CC ) $.

    $( Value of square.  Inference version.  (Contributed by Mario Carneiro,
       28-May-2016.) $)
    sqvald $a |- ( ph -> ( A ^ 2 ) = ( A x. A ) ) $.

    $( Closure of square.  (Contributed by Mario Carneiro, 28-May-2016.) $)
    sqcld $a |- ( ph -> ( A ^ 2 ) e. CC ) $.

    mulexpd.2 $e |- ( ph -> B e. CC ) $.

    ${
      sqdivd.3 $e |- ( ph -> B =/= 0 ) $.
      $( Distribution of squaring over division.  (Contributed by Mario
         Carneiro, 28-May-2016.) $)
      sqdivd $a |- ( ph -> ( ( A / B ) ^ 2 ) = ( ( A ^ 2 ) / ( B ^ 2 ) ) ) $.
    $}

  $}

  $( An integer is even iff its square is even.  (Contributed by Mario
     Carneiro, 12-Sep-2015.) $)
  zesq $a |- ( N e. ZZ ->
              ( ( N / 2 ) e. ZZ <-> ( ( N ^ 2 ) / 2 ) e. ZZ ) ) $.

  $( A positive integer is even iff its square is even.  (Contributed by NM,
     20-Aug-2001.)  (Revised by Mario Carneiro, 12-Sep-2015.) $)
  nnesq $a |- ( N e. NN ->
               ( ( N / 2 ) e. NN <-> ( ( N ^ 2 ) / 2 ) e. NN ) ) $.

  ${
    nnexpcld.1 $e |- ( ph -> A e. NN ) $.
    $( The naturals are closed under squaring.  (Contributed by Mario Carneiro,
       28-May-2016.) $)
    nnsqcld $a |- ( ph -> ( A ^ 2 ) e. NN ) $.
  $}

  $c sqrt $. $( Positive square root of a positive real number. $)

  $( Extend class notation to include square root of a complex number. $)
  csqrt $a class sqrt $.

  ${
    abscld.1 $e |- ( ph -> A e. CC ) $.
    $( Square root theorem.  Theorem I.35 of [Apostol] p. 29.  (Contributed by
       Mario Carneiro, 29-May-2016.) $)
    sqsqrtd $a |- ( ph -> ( ( sqrt ` A ) ^ 2 ) = A ) $.
  $}


  ${
    sqrt2irrlem.1 $e |- ( ph -> A e. ZZ ) $.
    sqrt2irrlem.2 $e |- ( ph -> B e. NN ) $.
    sqrt2irrlem.3 $e |- ( ph -> ( sqrt ` 2 ) = ( A / B ) ) $.
    $( Lemma for ~ sqrt2irr .  This is the core of the proof: if
       ` A / B = sqrt ( 2 ) ` , then ` A ` and ` B ` are even, so ` A / 2 ` and
       ` B / 2 ` are smaller representatives, which is absurd by the method of
       infinite descent (here implemented by strong induction).  This is
       Metamath 100 proof #1.  (Contributed by NM, 20-Aug-2001.)  (Revised by
       Mario Carneiro, 12-Sep-2015.)  (Proof shortened by JV, 4-Jan-2022.) $)
    sqrt2irrlem $p |- ( ph -> ( ( A / 2 ) e. ZZ /\ ( B / 2 ) e. NN ) ) $=
      ( c2 cdiv co cz wcel cn cexp cmul oveq1d eqtr3d nncnd nnne0d eqtrd syl wb
      csqrt cfv 2cnd sqsqrtd zcnd sqdivd nnsqcld divcan1d cc0 wne 2ne0 divcan3d
      sqcld a1i eqeltrd nnzd zesq mpbird clt wbr sqvald oveq2d divdiv1d 3eqtr4d
      zsqcl eqeltrrd nnrpd rphalfcld rpgt0d elnnz sylanbrc nnesq jca ) ABGHIZJK
      ZCGHILKZAVPBGMIZGHIZJKZAVSAVSCGMIZLAGWANIZGHIVSWAAWBVRGHAWBVRWAHIZWANIVRA
      GWCWANAGBCHIZGMIZWCAGUBUCZGMIGWEAGAUDZUEAWFWDGMFOPABCABDUFZACEQACERUGSOAV
      RWAABWHUNZAWAACEUHZQZAWAWJRUISOAWAGWKWGGUJUKAULUOZUMPZWJUPUQABJKVPVTUADBU
      RTUSZAVQWAGHIZLKZAWOJKUJWOUTVAWPAVOGMIZWOJAWQVSGHIZWOAVRGGMIZHIVRGGNIZHIW
      QWRAWSWTVRHAGWGVBVCABGWHWGWLUGAVRGGWIWGWGWLWLVDVEAVSWAGHWMOSAVPWQJKWNVOVF
      TVGAWOAWAAWAWJVHVIVJWOVKVLACLKVQWPUAECVMTUSVN $.
  $}

  ${
    $d n x y z $.
    $( The square root of 2 is irrational.  See ~ zsqrtelqelz for a
       generalization to all non-square integers.  The proof's core is proven
       in ~ sqrt2irrlem , which shows that if ` A / B = sqrt ( 2 ) ` , then
       ` A ` and ` B ` are even, so ` A / 2 ` and ` B / 2 ` are smaller
       representatives, which is absurd.  An older version of this proof was
       included in _The Seventeen Provers of the World_ compiled by Freek
       Wiedijk.  It is also the first of the "top 100" mathematical theorems
       whose formalization is tracked by Freek Wiedijk on his _Formalizing 100
       Theorems_ page at ~ http://www.cs.ru.nl/~~freek/100/ .  (Contributed by
       NM, 8-Jan-2002.)  (Proof shortened by Mario Carneiro, 12-Sep-2015.) $)
    sqrt2irr $p |- ( sqrt ` 2 ) e/ QQ $=
      ( vx vy vz c2 wcel cv cdiv co wceq cz wrex cn c1 clt wbr wne wral ralbidv
      wi wa vn csqrt cfv cq caddc peano2nn breq2 imbi1d nnnlt1 pm2.21d rgen crp
      wn nnrp rphalflt breq1 oveq2 neeq2d imbi12d rspcv com13 simpr cc ad2antlr
      syl zcn nncn ad2antrr 2cnd cc0 nnne0 2ne0 a1i divcan7d eqtr4d sqrt2irrlem
      simplr simpll simprd simpld oveq1 embantd necon2bd mpd necon2ad ralrimdva
      ex syld cbvralvw imbitrrdi ceqsralv sylibrd ancld wo wb cle nnleltp1 nnre
      leloe syl2an bitr3d ancoms jaob bitrdi ralbidva r19.26 nnind ltp1d ralnex
      cr df-ne mp2d nrex elq rexcom bitri mtbir nelir ) DUBUCZUDXSUDEZXSAFZBFZG
      HZIZAJKZBLKZYEBLYBLEZCFZYBMUEHZNOZXSYAYHGHZPZAJQZSZCLQZYBYINOZYEUMZYGYILE
      YOYBUFYHUAFZNOZYMSZCLQYHMNOZYMSZCLQYHYBNOZYMSZCLQZYOYOUABYIYRMIZYTUUBCLUU
      FYSUUAYMYRMYHNUGUHRYRYBIZYTUUDCLUUGYSUUCYMYRYBYHNUGUHRYRYIIZYTYNCLUUHYSYJ
      YMYRYIYHNUGUHRZUUIUUBCLYHLEZUUAYMYHUIUJUKYGUUEUUEYHYBIZYMSZCLQZTZYOYGUUEU
      UMYGUUEXSYCPZAJQZUUMYGUUEXSYHYBGHZPZCJQZUUPYGUUEYBDGHZLEZXSYAUUTGHZPZAJQZ
      SZUUSYGUUTYBNOZUUEUVESYGYBULEUVFYBUNYBUOVEUVAUUEUVFUVDUUDUVFUVDSCUUTLYHUU
      TIZUUCUVFYMUVDYHUUTYBNUPUVGYLUVCAJUVGYKUVBXSYHUUTYAGUQURRUSUTVAVEYGUVEUUR
      CJYGYHJEZTZUVEXSUUQUVIXSUUQIZUVEUMZUVIUVJTZXSYHDGHZUUTGHZIUVKUVLXSUUQUVNU
      VIUVJVBZUVLYHYBDUVHYHVCEYGUVJYHVFVDYGYBVCEUVHUVJYBVGVHUVLVIYGYBVJPUVHUVJY
      BVKVHDVJPUVLVLVMVNVOUVLUVEXSUVNUVLUVAUVDXSUVNPZUVLUVMJEZUVAUVLYHYBYGUVHUV
      JVQYGUVHUVJVRUVOVPZVSUVLUVQUVDUVPSUVLUVQUVAUVRVTUVCUVPAUVMJYAUVMIUVBUVNXS
      YAUVMUUTGWAURUTVEWBWCWDWGWEWFWHUUOUURACJYAYHIYCUUQXSYAYHYBGWAURWIWJYMUUPC
      YBLUUKYLUUOAJUUKYKYCXSYHYBYAGUQURZRWKWLWMYGYOUUDUULTZCLQUUNYGYNUVTCLYGUUJ
      TZYNUUCUUKWNZYMSUVTUWAYJUWBYMUUJYGYJUWBWOUUJYGTYHYBWPOZYJUWBYHYBWQUUJYHXJ
      EYBXJEUWCUWBWOYGYHWRYBWRZYHYBWSWTXAXBUHUUCYMUUKXCXDXEUUDUULCLXFXDWLXGVEYG
      YBUWDXHYNYPYQSCYBLUUKYJYPYMYQYHYBYINUPUUKYMYDUMZAJQYQUUKYLUWEAJUUKYLUUOUW
      EUVSXSYCXKXDRYDAJXIXDUSUTXLXMXTYDBLKAJKYFABXSXNYDABJLXOXPXQXR $.
  $}


$( End $[ set-numth.mm $] $)

$( Unused constants to satisfy the htmldef's in the $ t comment. $)
$c , T. F. F/ [ ] E* E! { | } F/_ _V [. ]. [_ ]_ \ u. i^i C_ C. (/) if ~P <.
  >. U. U_ |-> Tr _I _E Po Or Fr We X. `' dom ran |` " o. Rel Pred Ord On Lim
  suc iota : Fun Fn --> -1-1-> -onto-> -1-1-onto-> iota_ _om 1st 2nd frecs
  wrecs recs rec Er ~~ ~<_ ~< sup <RR _i +oo -oo RR* - -u 3 NN0 ZZ>= seq Re
  Im * abs & => if- -/\ \/_ -\/ hadd cadd CondEq /_\ |^| |^|_ Disj_ Se Isom
  oF oR [C.] supp tpos curry uncurry Undef Smo seqom 1o 2o 3o 4o +o .o ^o +no
  /. ^m ^pm X_ Fin finSupp fi inf OrdIso har ~<_* CNF t++ TC R1 rank |_| inl
  inr card aleph cf AC_ CHOICE Fin1a Fin2 Fin3 Fin4 Fin5 Fin6 Fin7 GCH InaccW
  Inacc WUni wUniCl Tarski Univ tarskiMap N. +N .N <N +pQ .pQ <pQ ~Q Q. 1Q /Q
  +Q .Q *Q <Q P. 1P +P. .P. <P ~R R. 0R 1R -1R +R .R <R 4 5 6 7 8 9 NN0* ; -e
  +e *e (,) (,] [,) [,] ... ..^ |_ |^ mod == ! _C # Word lastS ++ <" ">
  substr prefix splice reverse repeatS cyclShift t+ t* ^r t*rec shift sgn +-
  limsup ~~> ~~>r O(1) <_O(1) sum_ prod_ FallFac RiseFac BernPoly exp _e sin
  cos tan _pi _tau $.

