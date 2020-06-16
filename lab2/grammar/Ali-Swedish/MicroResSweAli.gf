resource MicroResSweAli = open Prelude in {

param
  Number = Sg | Pl ;
  Gender = Ut | Neu ;
  Defeniteness = Def | Indef ;
  Case = Nom | Acc ;

  VForm = Pres | Inf | Preteritum | Supinum  ;


oper



  Noun : Type = {s : Number => Defeniteness => Str ; g : Gender } ;


 regN : (sgIndef, sgDefi, plIndef, plDefi : Str ) ->  Noun
    =\sgIndef, sgDefi, plIndef, plDefi -> {s = table { Sg    => table { Indef => sgIndef ;
                                                                               Def  => sgDefi } ;

                                                           Pl    => table { Indef => plIndef ;
                                                                            Def  => plDefi }
                                         } ;
                                                                 g = taGender sgIndef }  ;
taGender : Str -> Gender
 = \sg -> case sg of {
      x + ("el"|"a"|"t"|"r"|"än"|"nd"|"ke"|"re"|"o") => Ut ; -- en
      x + ("v"|"in"|"en"|"öd"|"od"|"åk"|"g"|"ln"|"äd"|"le"|"rn") => Neu ; --ett
      _ => Neu

} ;

smartN : Str -> Noun
 = \sgIndef -> case sgIndef of {
  x + "el"  => regN sgIndef (x + "len") (x + "lar") (x + "larna") ; -- cyckel , fågel,
  x + ("e")       => regN sgIndef (x + "en") (x + "ar") (x + "arna")  ;
  x + ("t"|"k"|"il"|"d")    => regN sgIndef (sgIndef + "en") (sgIndef +"ar") (sgIndef + "arna")  ;
  x + ("r")       => regN sgIndef (sgIndef + "en") (sgIndef + "er") (sgIndef + "erna") ;
  x + "än"    => regN sgIndef (sgIndef + "en") (sgIndef + "ner") (sgIndef + "nerna") ;

  x +("a" |"o")   => regN sgIndef  (sgIndef + "n" ) (x + "or" ) (x + "orna") ; -- flicka , ko
  x + "v"    => regN sgIndef  (sgIndef + "et" ) sgIndef  (sgIndef + "en") ;
  x + "in"    => regN sgIndef  (sgIndef + "et" ) (sgIndef + "er")  (sgIndef + "enrna") ;
  x + "en"  => regN sgIndef  (x + "net" ) (x + "nen")  (x + "net") ;
  _  => regN sgIndef  (sgIndef + "net" ) (sgIndef + "nen")  (sgIndef + "net")
 } ;

irregN : (sgIndef, plindef : Str) ->  Noun
= \ sgIndef, plIndef -> case sgIndef of {
  x + ("ln"|"g"|"åk"|"äd")  => regN sgIndef (sgIndef + "et") plIndef (sgIndef + "en"); -- moln,träd, språk,tåg -- ett
  x + "e"  => regN sgIndef (sgIndef + "t") plIndef (sgIndef + "n");  -- äpple
    x + ("öd"|"n") => regN sgIndef (sgIndef + "et") plIndef sgIndef ; -- bröd

  x + ("lk"|"ik"|"an") =>   regN sgIndef (sgIndef + "en") plIndef (plIndef + "arna") ; -- mjölk , musik, män
  x + ("od") =>   regN sgIndef (sgIndef + "en") plIndef (plIndef + "arna") ; --blod
  x + ("ok"|"nd") => regN sgIndef (sgIndef + "en") plIndef (plIndef + "na") ; --bok,
  x + "l" => regN sgIndef (sgIndef + "en") plIndef sgIndef ;
  _ => regN sgIndef (sgIndef + "en") plIndef sgIndef

} ;

  Adjective : Type = {s : Number => Gender => Defeniteness => Str } ;


regA : (sgUtIndef,sgUtDef, sgNeuIndef, sgNeuDef, plUtDef, plUtIndef, plNeuDef, plNeuIndef : Str ) ->  Adjective
   =\ sgUtDef, sgUtIndef, sgNeuDef, sgNeuIndef, plUtDef, plUtIndef, plNeuDef, plNeuIndef -> {s = table

   { Sg => table { Neu => table { Def => sgUtDef ;
                                 Indef => sgUtIndef } ;

                  Ut  => table { Def =>  sgNeuDef ;
                                  Indef => sgNeuIndef} }  ;

    Pl => table { Neu => table { Def => plUtDef ;
                                Indef => plUtIndef} ;

                  Ut => table { Def => plNeuDef ;
                                 Indef => plNeuIndef} } } } ;

smartA : Str -> Adjective
  =\ sg -> case sg of {
  gamm + "al" => regA (gamm + "la") (gamm + "t") (gamm + "la") sg (gamm + "la") (gamm + "la") (gamm + "la") (gamm + "la");
  bl + ("å"|"a") => regA sg  (bl + "tt")  sg  sg sg  sg sg sg ;
  rö + "d" => regA sg  (rö + "tt")  (rö +"a")  (rö +"a") (rö +"a") (rö +"a")  (rö +"a") (rö +"a") ;
  _ =>  regA (sg + "a") (sg + "t") (sg + "a") sg (sg + "a") (sg + "a") (sg + "a") (sg + "a") } ;


Verb : Type = {s : VForm => Str} ;


  mkVerb : (inf,pres,preteritum,supinum : Str) -> Verb
    = \inf,pres,preteritum,supinum -> {
    s = table {
      Inf => inf ;
      Pres => pres ;
      Preteritum => preteritum ;
      Supinum => supinum
      }
    } ;

  regVerb : (inf : Str) -> Verb = \inf ->
    mkVerb inf inf  (inf + "de") (inf + "t") ;

  -- regular verbs with predictable variations
  smartVerb : Str -> Verb = \pres -> case pres of {
     x  +  "ar"  => mkVerb (x + "a") pres (x + "ade") (x + "at") ;
     x  +  "er" =>  mkVerb (x + "a") pres (x + "te") (x + "t");
     x + "t"  =>  mkVerb (pres + "a") pres (x + "te") (x + "t");
     x + "år"  =>  mkVerb (x + "å") pres (x + "te") (x + "t");
     _ => regVerb pres
     } ;

  -- normal irregular verbs e.g. drink,drank,drunk
  irregVerb : (pres,preteritum,supinum : Str) -> Verb =
    \pres,preteritum,supinum ->
      let verb = smartVerb pres
      in mkVerb (verb.s! Inf) pres preteritum supinum ;

  -- two-place verb with "case" as preposition; for transitive verbs, c=[]
  Verb2 : Type = Verb ** {c : Str} ;

  be_Verb : Verb = mkVerb "vara" "är" "var" "varit"  ; ---s to be generalized



}
