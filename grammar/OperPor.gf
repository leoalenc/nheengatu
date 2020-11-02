-- GrammYEP - a multilingual computational grammar for Nheengatu, English, and Portuguese
-- (c) 2020 Leonel Figueiredo de Alencar
-- Licensed under the terms of the GNU Lesser General Public License, version 2.1
-- See LICENSE or visit the URL
-- https://www.gnu.org/licenses/old-licenses/lgpl-2.1.en.html


resource OperPor = open Oper, Prelude in { 
flags coding=utf8 ;
param

    Case = Nom | Acc | Loc | Gen | Com ; 
    Form = Prep | Pron ;

  oper
	
	KIND_POR : Type = {s : Number => Str ; g: Gender } ;
	QUAL_POR : Type = {s : Number => Gender => Str } ;
	STATE_POR : Type = QUAL_POR ** {l: Level } ;
	DEF_ITEM_POR : Type = ITEM ** { g: Gender } ;
	ITEM_POR : Type = {s : Case => Str ; n : Number; p: Person ; g: Gender} ;
	POSSPRO : Type = QUAL_POR ** {f: Form} ;
    	DEF_POR : Type = {s: Gender => Str ; n: Number} ;
	
    possPronN : Str -> Str -> Form -> Str = \p,n,f -> table {Prep => n ++ p ; Pron => p ++ n} ! f ;
    mkPossPron = overload {
    	   mkPossPron : Str -> Str -> POSSPRO = \meu,minha -> let paradigm: QUAL_POR = adjPor (meu) (minha) (meu + "s") (minha + "s") in paradigm ** {f= Pron};
	   mkPossPron : Str -> POSSPRO =\nosso -> let paradigm: QUAL_POR = adjO nosso in paradigm ** {f= Pron};
	   mkPossPron : Str -> Form -> POSSPRO =\dele,f -> let paradigm: QUAL_POR = adjPor dele dele dele dele in paradigm ** {f= f};
	   mkPossPron : Form -> POSSPRO =\f -> let x: Str = "de" ++ "vocês"; paradigm: QUAL_POR = adjPor x x x x in paradigm ** {f= f};
    	} ;

    mkPropPor : QUAL_POR -> QUAL_POR = \qual -> {s= \\n,g => qual.s ! n ! g } ;
    mkPropLocPor : EXPR -> QUAL_POR = \loc -> {s= \\n,g => loc.s } ;

    mkLocPor = overload {

    	      mkLocPor : Case -> ITEM_POR -> EXPR = \c,i-> 
    	     {s=i.s ! c};
    	     mkLocPor : Case -> Str -> ITEM_POR -> EXPR = \c,f,i-> 
    	     {s=f ++ i.s ! c};

	     };

    --pform : Str -> Case => Str =\prep -> table {Loc => ""; _ => prep};

    detPor = overload {
    	   detPor : Number -> DEF_POR = \num -> {s= PossPrepArt ! num ; n= num};

    	   detPor : DEF_POR -> KIND_POR -> DEF_ITEM_POR = \df,noun -> let num: Number = df.n ; prepart : Str = df.s ! noun.g in {s = prepart ++ noun.s ! num ; n = num ; p = P3 ; g = noun.g} ;

	   detPor : Number -> Str -> Str -> KIND_POR -> ITEM_POR = \num,m,f,kind -> 
	   let base : Str = table {Masc => m; Fem => f}  ! kind.g ; 
	   noun : Str = kind.s ! num in {
    	   	s= table { Loc => ("n"+ base) ++ noun ; 
		   	   Gen => ("d"+ base) ++ noun ;
			   Com => ("com" ++ base) ++ noun ;
		   	   _ => base ++ noun } ;
    		n= num ; 
    		p = P3 ; 
    		g = kind.g  } ;
    } ;
    

    detForm : Str -> Str -> Gender => Str = \masc,fem -> table {Masc => masc; Fem => fem} ;

    
    mkItemPor : ITEM_POR -> ITEM_POR = \item -> {s = item.s ; n = item.n; p= item.p ; g = item.g} ;
    
    mkKindPor : KIND_POR -> KIND_POR = \k -> {s = \\n => k.s ! n ; g = k.g} ;
    
    mkPron : Number -> Person -> Gender -> Str -> Str -> Str -> Str -> Str -> ITEM_POR = 
        \num,pers,gend,nom,acc,loc,gen,com -> 
		{s = table {
		     	   Nom => nom | "";
			   Acc => acc ;
			   Loc => loc ;
			   Gen => gen ;
			   Com => com
			   }; 
		n = num; 
		p = pers ; 
		g = gend } ;
    
    pronPor = overload {
	pronPor : Number -> Person -> Gender -> Str -> Str -> ITEM_POR = 
        \num,pers,gend,nom,acc -> mkPron num pers gend nom acc ("n" + nom) ("d" + nom) ("com" ++ nom) ; 

		{- 
		   {s = table {
		     	   Nom => ele | "";
			   Acc => o ;
			   Loc => "n" + ele ;
			   Gen => "d" + ele ;
			   Com => "com" ++ ele
			   }; 
		n = num; 
		p = pers ; 
		g = gend } ; 
		-}

	

	pronPor : Number -> Person -> Str -> Str -> Str -> ITEM_POR = 
        \num,pers,nom,acc,com -> mkPron num pers (Masc|Fem) nom acc ("em" ++ nom) ("de" ++ nom) ("conosco") ; 

	pronPor : Number -> Person -> Str -> Str -> Str -> Str -> ITEM_POR = 
        \num,pers,eu,me,mim,comigo -> mkPron num pers (Masc|Fem) eu me ("em" ++ mim) ("de" ++ mim) comigo ;

	pronPor : Number -> Person -> Str -> ITEM_POR = 
        \num,pers,nom -> mkPron num pers (Masc|Fem) nom nom ("em" ++ nom) ("de" ++ nom) ("com" ++ nom) ; 

} ;
    regNounPor : Str -> Gender -> KIND_POR = 
      \n,g -> {s = (noun n (n + "s")).s ; g = g } ;
    nounPor : Str -> Str -> Gender -> KIND_POR = 
      \man,men,gen -> {s = (noun man men).s ; g = gen } ;
    adjPor : (bom,boa,bons,boas: Str) -> QUAL_POR = \bom,boa,bons,boas -> {
    	   s = table {
		Sg => table {Masc => bom ; Fem => boa}; 
		Pl => table {Masc => bons ; Fem => boas}
		}
	};
    adjO : Str -> QUAL_POR = \bonito -> let bonit : Str = init bonito 
    	 in 
    	 adjPor bonito (bonit +"a") (bonit +"os") (bonit +"as") ;
    adj2 : Str -> Str -> QUAL_POR = \feliz,felizes -> adjPor feliz feliz felizes felizes ;
    adjE : Str -> QUAL_POR = \forte -> adj2 forte (forte +"s") ;
    
    -- TODO: use adjO
   PossPrepArt : Number => Gender => Str = table { Sg => table { Masc => "do"; Fem => "da"} ; Pl => table { Masc => "dos"; Fem => "das" }};
   
PorCopula : Level -> Number -> Person -> Str = \l,n,p -> table {
Ind => IndLevelCopPor ! n ! p ;
Stage => StageLevelCopPor ! n ! p
} ! l;

IndLevelCopPor : Number => Person => Str =  mkIrrVerb "sou" "és" "é" "somos" "sois" "são" ;
StageLevelCopPor : Number => Person => Str =  mkIrrVerb "estou" "estás" "está" "estamos" "estais" "estão" ;


}