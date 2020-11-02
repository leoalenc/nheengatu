-- GrammYEP - a multilingual computational grammar for Nheengatu, English, and Portuguese
-- (c) 2020 Leonel Figueiredo de Alencar
-- Licensed under the terms of the GNU Lesser General Public License, version 2.1
-- See LICENSE or visit the URL
-- https://www.gnu.org/licenses/old-licenses/lgpl-2.1.en.html


resource OperEng = open Oper, Prelude in { 
flags coding=utf8 ;
param
	-- TODO: the distinction between the two features below relates to the licensing of "the"
	-- * the my canoo, * the John (change feature name accordingly)
    POS = CommonN | ProperN ;
    Polar = Pos | Neg ;
    Case = Nom | Obj ;

  oper
	
	ITEM_ENG : Type = {s : Case => Str ; n : Number; p: Person} ;
	NONVAR : Type = ITEM ;
	VAR : Type = ITEM_ENG ;
	POLARITY : Type = {s: Str ; pol: Polar};
	KIND_ENG : Type = KIND ** {pos: POS} ;
	STATE : Type = {s: Str ; l: Level } ;
	DEF_ITEM : Type = ITEM ;
	POSSPRO : Type = EXPR ;
	POSSKIND : Type = KIND_ENG ;
	DEF : Type = {s: POS => Str; n: Number} ;

    mkLocEng : Str -> ITEM_ENG -> EXPR = \prep,item -> {s= prep ++ item.s ! Obj};
    
    mkPropEng : EXPR -> EXPR = \qual -> {s= qual.s};
    chooseThe : POS => Str =  table {CommonN => "the" ; ProperN => ""} ; 
    
    det = overload {
    	det : Number -> DEF = \n -> {s= chooseThe ; n=n};
    	det : DEF -> KIND_ENG -> DEF_ITEM = \d,k -> {s= d.s ! k.pos ++ k.s ! d.n ; n= d.n ; p=P3};
    	det : Number -> KIND_ENG -> NONVAR = \num,noun -> let art: Str = chooseThe ! noun.pos in {s = art ++ noun.s ! num ; n = num; p = P3} ;
    	det : Number -> Str -> 
      	    KIND_ENG -> NONVAR = 
            	     \num,d,noun -> {	s = d ++ noun.s ! num ; 
		     		       	n = num; 
					p = P3} ;

	} ;
    
    properNameEng : Str -> KIND_ENG = \name -> regNounEng name ProperN ;
    
    mkItem = overload {
    	   mkItem : VAR -> ITEM_ENG = \var -> {
    	     	      	 	  s = table {
				      	    Nom => var.s ! Nom ; 
					    Obj => var.s ! Obj
				      	    }; 
    	     	      	 	  n = var.n; 
				  p= var.p
				 } ;
	mkItem : NONVAR -> ITEM_ENG = \nonvar -> {
	       	 	   	      s = \\cs => nonvar.s ; 
	       	 	   	      n = nonvar.n; 
				      p= nonvar.p } ;
		} ;

    mkKindEng : KIND_ENG -> KIND_ENG = \k -> {s = \\n => k.s ! n ; pos = k.pos} ;
    
    pron : Number -> Person -> Str -> Str -> VAR = 
        \num,pers,she,her -> { s = table {Nom => she; Obj => her} ; 
			       n = num; 
			       p = pers } ;

    nounEng : Str -> Str -> POS -> KIND_ENG = 
      \man,men,p -> {s = table {Sg => man ; Pl => men}; pos = p} ;
    
    regNounEng : Str -> POS -> KIND_ENG = 
      \car,pos -> nounEng car (car + "s") pos;
    adj : Str -> EXPR = 
      \cold -> {s = cold} ;
    
   
EngCopula : Number => Person => Polar => Str = table {
	  	      Sg => table {
		      	 P1 => table { Pos => "am"; Neg => "am not"} ;
		   	 P2 => table { Pos => "are"; Neg => "are not" | "aren't"};
		   	 P3 => table { Pos => "is"; Neg => "is not" | "isn't"}
		  	  } ; 
	  	 Pl => table {
		       _ => table { Pos => "are"; Neg => "are not" | "aren't"} 
		       } 
		       }; 



}