-- GrammYEP - a multilingual computational grammar for Nheengatu, English, and Portuguese
-- (c) 2020 Leonel Figueiredo de Alencar
-- Licensed under the terms of the GNU Lesser General Public License, version 2.1
-- See LICENSE or visit the URL
-- https://www.gnu.org/licenses/old-licenses/lgpl-2.1.en.html


resource Oper = open Prelude in {
flags coding=utf8 ;
param
	Person = P1 | P2 | P3 ;
    Number = Sg | Pl ;
    Gender = Masc | Fem ;
    Level = Ind | Stage ;

  oper
	EXPR : Type = {s : Str} ;
	ITEM : Type = {s : Str ; n : Number; p: Person} ;
	KIND : Type = {s : Number => Str} ;

    shuffle : Str -> Str -> Str = \a,b -> a ++ b | b ++ a ;

    noun : Str -> Str -> KIND =
      \man,men -> {s = table {Sg => man ; Pl => men}} ;


--TODO: mkRegVerb returns record, mkIrrVerb returns table; uniformize this
mkIrrVerb : (_,_,_,_,_,_ : Str) -> Number => Person => Str =
        \sum,es,est,sumus,estis,sunt ->
          table {
	  	Sg => table {
		   P1 => sum;
		   P2 => es;
		   P3 => est
		   } ;
	  	 Pl => table {
		    P1 => sumus;
		    P2 => estis;
		    P3 => sunt
		    }
		    } ;
}
