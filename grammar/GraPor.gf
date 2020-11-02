-- GrammYEP - a multilingual computational grammar for Nheengatu, English, and Portuguese
-- (c) 2020 Leonel Figueiredo de Alencar
-- Licensed under the terms of the GNU Lesser General Public License, version 2.1
-- See LICENSE or visit the URL
-- https://www.gnu.org/licenses/old-licenses/lgpl-2.1.en.html


concrete GraPor of Lex = open Oper, OperPor in {
	 flags coding=utf8 ;
  lincat
    Comment, Polarity = EXPR ;
    Quality = QUAL_POR ;
    Kind, SimpleKind, PossKind = KIND_POR ;
    Property = QUAL_POR ;
    Location = EXPR ;
    State = STATE_POR ;
    Item = ITEM_POR ; 
    Psor = DEF_ITEM_POR ;
    Deitic = ITEM_POR ;
    NonDeitic = ITEM_POR ;
    PossPro = POSSPRO ;
    Num = DEF_POR ;

  lin
    Pred pol item st = 
     -- {s= item.s ++ copula  item.n ++ quality.s} ;
     {s= item.s ! Nom ++ pol.s ++ PorCopula st.l item.n  item.p ++ st.s ! item.n ! item.g} ;
    StageLevelState quality = {s=\\n,g => quality.s ! n ! g ; l= Stage} ;
    IndLevelState quality = {s=\\n,g => quality.s ! n ! g ; l= Ind} ;
    mkItemDeitic var = mkItemPor var;
    mkItemNonDeitic nonvar =  mkItemPor nonvar ;
    mkKind k = mkKindPor k ;
    mkKind_ k = mkKindPor k ;
    mkPropLoc loc = mkPropLocPor loc ;
    mkPropQual qual = mkPropPor qual ;
    Yes = {s=""};
    No = {s= "não" } ;
    Here = {s= "aqui"};
    There = {s= "lá"};
    On = mkLocPor Loc ;
    In = mkLocPor Loc ;
    With = mkLocPor Com  ;
    Near = mkLocPor Gen "perto" ;
-- TODO: consider implementing plural possessors
    Poss psor psum = let x : Str = psor.s in  {s =\\c => psum.s ! c ++ x ; n = psum.n; p= P3 ; g = psum.g} ;
    Poss_ psor psum = let psumSg: Str = psum.s ! Sg ; psumPl: Str = psum.s ! Pl ; psorSing: Str =  psor.s ! Sg ! psum.g ; psorPl: Str = psor.s ! Pl ! psum.g in {s = table {Sg => possPronN psorSing psumSg psor.f ; Pl => possPronN psorPl psumPl psor.f } ; g = psum.g } ;
   -- The = det Sg "the" ;
    --TheSG kind = let f : Str = chooseThe kind.pos in det Sg f ;
    --TheSG kind = detTheSG kind ;
    -- TODO: consider implementing detThePL for proper names in plural
    mkPsor df sk = detPor df sk;
    mkPsor_ df pk = detPor df pk;
    SG = detPor Sg;
    PL = detPor Pl;
    TheSG = detPor Sg "o" "a" ; 
    ThePL = detPor Pl "os" "as" ;
    This  = detPor Sg ("este"|"esse") ("esta"|"essa") ;
    That  = detPor Sg "aquele" "aquela" ;
    These = detPor Pl "estes" "estas" ;
    Those = detPor Pl "aqueles" "aquelas" ;
    He =  pronPor Sg P3 Masc "ele" "o" ;
    She =  pronPor Sg P3 Fem "ela" "a" ;
    It =  pronPor Sg P3 Masc "ele" "o" ;
    They = pronPor Pl P3 Masc "eles" "os" ;
    We = pronPor Pl P1 "nós" "nos" "conosco";
    I = pronPor Sg P1 "eu" "me" "mim" "comigo";
    YouSG = pronPor Sg P3 "você" | pronPor Sg P2 "tu" "te" "ti" "contigo" ;
    YouPL = pronPor Pl P3 "vocês" ;
    My = mkPossPron "meu" "minha";
    Our = mkPossPron "nosso";
    YourSG = mkPossPron ("seu"|"teu") ("sua"|"tua");
    YourPL = mkPossPron Prep;
    His = mkPossPron "dele" Prep;
    Her = mkPossPron "dela" Prep;
    Its = mkPossPron "dele" Prep;
    Their = mkPossPron ("deles"|"delas");

{-
    Mod quality kind = let gend : Gender = kind.g ; 
    		       	   adj : Number => Gender => Str = quality.s  ; 
			   noun : Number => Str = kind.s in 
      {s = \\num => shuffle (adj ! num ! gend)  (noun ! num)  ; g = gend } ;
-}

    Mod qual kind = let g : Gender = kind.g in 
    	{s = \\n => shuffle (qual.s ! n ! g)  (kind.s ! n)  ; g = g } ;

	Very a = {s = \\n,g => "muito" ++ a.s ! n ! g } ;

     
Alive = adjO "duro";
Ant = regNounPor "formiga" Fem;
Antonio = regNounPor "Antônio" Masc;
Beak = regNounPor "bico" Masc;
Beautiful = adjO "bonito";
Bird = regNounPor "pássaro" Masc;
Blood = regNounPor "sangue" Masc;
Boy = regNounPor "menino" Masc;
Branch = regNounPor ("galho"|"ramo") Masc;
Brother_Of_Woman = regNounPor "irmão" Masc;
Canoe = regNounPor "canoa" Fem;
Cheap = adjO "barato";
Child = regNounPor "criança" Fem;
City = regNounPor "cidade" Fem;
Community = regNounPor "comunidade" Fem;
Delicious = adjO "delicioso";
Dirty = adjO "sujo";
Door = regNounPor "porta" Fem;
Dove = regNounPor "pomba" Fem | regNounPor "pombo" Masc;
Egg = regNounPor "ovo" Masc;
Expensive = adjO "caro";
Fish = regNounPor "peixe" Masc;
Food = regNounPor "comida" Fem;
Good = adjPor "bom" "bons" "boa" "boas";
Grandfather = regNounPor "avô" Masc;
Happy = adj2 "feliz" "felizes" | adj2 "alegre" "alegres";
Hard = adjO "duro";
Heavy = adjO "pesado";
Hog_Plum = regNounPor ("cajá"|"taperebá") Masc;
Hook = nounPor "anzol" "anzóis" Masc;
Hot = adjE "quente";
House = regNounPor "casa" Fem;
Husband = regNounPor "marido" Masc;
Joanna = regNounPor "Joana" Fem;
Knife = regNounPor "faca" Fem;
Language = regNounPor "língua" Fem;
Life = regNounPor "vida" Fem;
Man = nounPor "homem" "homens" Masc;
Maria = regNounPor "Maria" Fem;
Milk = regNounPor "leite" Masc;
Nest = regNounPor "ninho" Masc;
New = adjO "novo";
Path = regNounPor "caminho" Masc;
Pedro = regNounPor "Pedro" Masc;
Picture = regNounPor "fotografia" Fem | regNounPor "retrato" Masc;
Pit = regNounPor "caroço" Masc;
Pumpkin = regNounPor ("jerimum"|"abóbara") Masc;
Red = adjO "vermelho";
River = regNounPor "rio" Masc;
Round = adjO "redondo";
Seed = regNounPor "semente" Fem;
Son_Of_Woman = regNounPor "filho" Masc;
Son_Of_Man = regNounPor "filho" Masc;
Daughter_Of_Woman = regNounPor "filha" Fem;
Daughter_Of_Man = regNounPor "filha" Fem;
Stone = regNounPor "pedra" Fem;
Street = regNounPor "rua" Fem;
Strong = adjE "forte";
Tapioca_Cake = regNounPor "beiju" Masc;
Toucan = regNounPor "tucano" Masc;
Tree = regNounPor "árvore" Fem;
Water = regNounPor "água" Fem;
Wife = regNounPor ("esposa"|"mulher") Fem;
Woman = nounPor "mulher" "mulheres" Fem;
Word = regNounPor "palavra" Fem;

}
