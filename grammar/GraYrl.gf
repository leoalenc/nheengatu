-- GrammYEP - a multilingual computational grammar for Nheengatu, English, and Portuguese
-- (c) 2020 Leonel Figueiredo de Alencar
-- Licensed under the terms of the GNU Lesser General Public License, version 2.1
-- See LICENSE or visit the URL
-- https://www.gnu.org/licenses/old-licenses/lgpl-2.1.en.html

concrete GraYrl of Lex = open Oper, OperYrl in {
 flags coding=utf8 ;
  lincat
    Comment, Polarity = EXPR ;
    Kind = KIND_YRL ;
    SimpleKind = SIMPLEKIND ;
    Quality = QUAL_YRL ;
    Property = PROPERTY ;
    Location = LOCATION ;
    State = STATE_YRL ;
    Item = ITEM_YRL ; 
    Psor = DEF_ITEM_YRL ;
    Deitic = ITEM_YRL ;
    NonDeitic = NONVAR_YRL ;
    PossPro = POSSPRO ;
    PossKind = POSSKIND ;
    Num = DEF ;

  lin
    Pred pol item st = let f: FORM = item.s ! st.c ! st.l ;  pred: Str = YrlCopula item.n item.p st.l st.c (st.s ! item.n ! item.p) st.v st.nc pol.s in
     {s= f ! Nom ! NCI ++ pred } ;
    StageLevelState qual = {s= qual.s ; l= Stage; c=qual.c ; v=qual.v ; nc = qual.nc} ;
    IndLevelState qual = {s= qual.s; l= Ind; c=qual.c ; v=qual.v;  nc = qual.nc} ;
    mkItemDeitic var = mkItemYrl var;
    mkItemNonDeitic nonvar =  mkItemYrl nonvar ;
    mkKind sk = mkKindYrl sk ;
    mkKind_ pk = mkKindYrl_ pk ;
    mkPropLoc loc = mkPropYrl loc ;
    mkPropQual qual = mkPropYrl qual ;
    Here = mkAdvLoc "iké" ;
    There = mkAdvLoc "ape" ;
    On = mkLocYrl "upé" ;
    In = mkLocYrl ("upé"|"pupé"|"kuara upé") ;
    With = mkLocYrl "irũmu" ;
    Near = mkLocYrl "ruaki" NCS ;
    mkPsor df sk = detYrl df sk ;
    mkPsor_ df pk = detYrl df.s df.n pk ;
    Yes = {s=""};
    No = {s= "ti" | "niti" } ;
    SG = {s = "" ; n= Sg};
    PL = {s = "" ; n= Pl};
    TheSG = detYrl Sg "" ;
    ThePL = detYrl Pl "" ;
    This  = detYrl Sg "kuá" ;
    That  = detYrl Sg "nhaã" ;
    These = detYrl "kuá" ;
    Those = detYrl "nhaã" ;
    He =  pronYrl Sg P3 "aé" ;
    She =  pronYrl Sg P3 "aé" ;
    It =  pronYrl Sg P3 "aé" ;
    They = pronYrl Pl P3 "aintá" ;
    We = pronYrl Pl P1 "iandé" ;
    I = pronYrl Sg P1 "ixé" ;
    YouSG = pronYrl Sg P2 "indé" ;
    YouPL = pronYrl Pl P2 "penhẽ" ;
    My = mkPossPron Sg P1;
    Our = mkPossPron Pl P1;
    YourSG = mkPossPron Sg P2;
    YourPL = mkPossPron Pl P2;
    His = mkPossPron Sg P3;
    Her = mkPossPron Sg P3;
    Its = mkPossPron Sg P3;
    Their = mkPossPron Pl P3;

    Mod quality kind = let adjForm: Str = quality.s ! Sg ! P3 in 
      {s = \\n,nf => adjForm ++ kind.s ! n ! nf | kind.s ! n ! nf ++ adjForm } ;
  
	Poss psor psum = let psorForm : Str = psor.s in {s = \\c,l,cs,nc => (psum.s).dem ++  psorForm ++ (psum.s).head ! NRel psor.pf ; n = psum.n; p = P3 ; pos = Noun  } ;
    	Poss_ psor psum = let singForm: Str = psum.s ! Sg ! NRel psor.pf; plForm: Str = psum.s ! Pl ! NRel psor.pf; psorForm: Str = psor.s ! psum.nc in {s = table {Sg => psorForm ++ singForm; Pl => psorForm ++ plForm} ; pf = NSG3  } ;


-- TODO: adapt the following to new type system
    Very adj = {s = \\num,pers => adj.s ! num ! pers ++ "retana"; c=adj.c ; v = adj.v ; nc = adj.nc} ;

      
Alive = adjYrl "rikué" NCS;
Ant = regNounYrl "tukandira";
Antonio = properNameYrl "Antônio";
Beak = regNounYrl "tĩ";
Beautiful = adjYrl "puranga" C1;
Bird = regNounYrl "uirá";
Blood = RelPrefNoun "tuí" "tuí";
Boy = regNounYrl "kurumĩ";
Branch = RelPrefNoun "sakanga";
Brother_Of_Woman = regNounYrl "kiuíra";
Canoe = regNounYrl "igara";
Cheap = adjYrl "sepiasuíma" C1;
Child = regNounYrl "taína";
City = regNounYrl "taua";
Community = RelPrefNoun "tendaua";
Delicious = adjYrl "sé" C1;
Dirty = adjYrl "kiá" C2;
Door = RelPrefNoun "ukena";
Dove = regNounYrl "pikasu";
Egg = RelPrefNoun "supiá";
Expensive = adjYrl "sepiasu" C1;
Fish = regNounYrl "pirá";
Food = RelPrefNoun "timbiú" "ximbiú";
Good = adjYrl "katu" C2;
Grandfather = RelPrefNoun "samunha";
Happy = adjYrl "ruri" NCS;
Hard = adjYrl "santá" C1;
Heavy = adjYrl "pusé" C2;
Hog_Plum = regNounYrl "tapereiuá";
Hook = regNounYrl "pindá";
Hot = adjYrl "raku" NCS;
House = RelPrefNoun "uka";
Husband = regNounYrl "mena";
Joanna = properNameYrl "Joana";
Knife = regNounYrl "kisé";
Language = regNounYrl "nheenga";
Life = RelPrefNoun "sikué";
Man = regNounYrl "apigaua";
Maria = properNameYrl "Maria";
Milk = regNounYrl "kambi";
Nest = RelPrefNoun "taiti";
New = adjYrl "pisasu" C1;
Path = RelPrefNoun "pé";
Pedro = properNameYrl "Pedro";
Picture = RelPrefNoun "sangaua";
Pit = RelPrefNoun "tainha";
Pumpkin = regNounYrl "ierimũ";
Red = adjYrl "piranga" C1;
River = regNounYrl ("paranã"|"paraná");
Round = adjYrl "apuã" C2;
Seed = RelPrefNoun "tainha";
Son_Of_Woman = regNounYrl ("mimbira"|"mbira");
Son_Of_Man = RelPrefNoun "taíra" "taíra";
Daughter_Of_Woman = regNounYrl ("mimbira"|"mbira");
Daughter_Of_Man = RelPrefNoun "taiera" "taiera";
Stone = regNounYrl "itá";
Street = RelPrefNoun "pé";
Strong = adjYrl "kirimbaua" C1;
Tapioca_Cake = regNounYrl "meiú";
Toucan = regNounYrl "tukana";
Tree = regNounYrl "mirá";
Water = regNounYrl "ií";
Wife = RelPrefNoun "simiriku" ("simiriku"|"ximiriku");
Woman = regNounYrl "kunhã";
Word = regNounYrl "nheenga";

}
