-- GrammYEP - a multilingual computational grammar for Nheengatu, English, and Portuguese
-- (c) 2020 Leonel Figueiredo de Alencar
-- Licensed under the terms of the GNU Lesser General Public License, version 2.1
-- See LICENSE or visit the URL
-- https://www.gnu.org/licenses/old-licenses/lgpl-2.1.en.html


concrete GraEng of Lex = open Oper, OperEng, Prelude in {
  lincat
    Comment, Quality = EXPR ;
    Polarity = POLARITY ;
    Kind, SimpleKind, PossKind = KIND_ENG ;
    Property = EXPR ;
    Location = EXPR ;
    State = STATE ;
    Item = ITEM_ENG ;
    Psor = DEF_ITEM ;
    Deitic = VAR ;
    NonDeitic = NONVAR ;
    PossPro = POSSPRO ;
    Num = DEF ;

  lin
    Pred pol item st =
     {s= item.s ! Nom ++ EngCopula ! item.n ! item.p ! pol.pol ++ pol.s ++ st.s} ;
    StageLevelState quality = {s= quality.s ; l= Stage} ;
    IndLevelState quality = {s= quality.s; l= Ind} ;
    mkItemDeitic var = mkItem var;
    mkItemNonDeitic nonvar =  mkItem nonvar ;
    mkKind k = mkKindEng k ;
    mkKind_ k = mkKindEng k ;
    mkPropLoc loc = mkPropEng loc ;
    mkPropQual qual = mkPropEng qual ;
    On = mkLocEng "on" ;
    In = mkLocEng "in" ;
    With = mkLocEng "with" ;
    Near = mkLocEng "near" ;
    Here = {s= "here"};
    There = {s= "there"};

    Poss psor psum = let f : Str = psor.s in
    	      {s = \\cs => psum.s ++ "of" ++ f ;
	      n = psum.n;
	      p= P3} ;

-- TODO: 18/01/20 substitute ProperN for Definite and CommonN for NonDefinte
    Poss_ psor psum = let singForm: Str = psum.s ! Sg ; plForm: Str = psum.s ! Pl in {s= table {Sg => psor.s ++ singForm ; Pl => psor.s ++ plForm} ; pos = ProperN} ;


    mkPsor df sk= det df sk ;
    mkPsor_ df pk= det df pk ;
    SG = det Sg;
    PL = det Pl;
    Yes = {s="" ; pol = Pos} ;
    No = {s="" ; pol = Neg} ;
    ThePL k = det Pl k;
    TheSG k = det Sg k ;
    This  = det Sg "this" ;
    That  = det Sg "that" ;
    These = det Pl "these" ;
    Those = det Pl "those" ;
    He =  pron Sg P3 "he" "him ";
    She =  pron Sg P3 "she" "her" ;
    It =  pron Sg P3 "it" "it" ;
    They = pron Pl P3 "they" "them" ;
    We = pron Pl P1 "we" "us" ;
    I = pron Sg P1 "I" "me" ;
    YouSG = pron Sg P2 "you" "you" ;
    YouPL = pron Pl P2 "you" "you" ;
    My = ss "my";
    Our = ss "our";
    YourSG = ss "your";
    YourPL = ss "your";
    His = ss "his";
    Her = ss "her";
    Its = ss "its";
    Their = ss "their";
    Mod quality kind =
      {s = \\n => quality.s ++ kind.s ! n ; pos = kind.pos} ;

     Very a = {s = "very" ++ a.s} ;


Alive = adj "alive";
Ant = regNounEng "ant" CommonN;
Antonio = properNameEng "Antônio";
Beak = regNounEng "beak" CommonN;
Beautiful = adj "beautiful";
Bird = regNounEng "bird" CommonN;
Blood = regNounEng "blood" CommonN;
Boy = regNounEng "boy" CommonN;
Branch = regNounEng "branch" CommonN;
Brother_Of_Woman = regNounEng "brother" CommonN;
Canoe = regNounEng "canoe" CommonN;
Cow = regNounEng "cow" CommonN;
Cheap = adj "cheap";
Child = nounEng "child" "children" CommonN;
City = regNounEng "city" CommonN;
Community = regNounEng "community" CommonN;
Delicious = adj "delicious";
Dirty = adj "dirty";
Door = regNounEng "door" CommonN;
Dove = regNounEng "dove" CommonN;
Egg = regNounEng "egg" CommonN;
Expensive = adj "expensive";
Fish = nounEng "fish" "fish" CommonN;
Food = regNounEng "food" CommonN;
Good = adj "good";
Grandfather = regNounEng "grandfather" CommonN;
Happy = adj "happy";
Hard = adj "hard";
Heavy = adj "heavy";
Hog_Plum = regNounEng "hog plum" CommonN;
Hook = regNounEng "hook" CommonN;
Hot = adj "hot";
House = regNounEng "house" CommonN;
Husband = regNounEng "husband" CommonN;
Joanna = properNameEng "Joana";
Knife = regNounEng "knife" CommonN;
Language = regNounEng "language" CommonN;
Life = regNounEng "life" CommonN;
Man = nounEng "man" "men" CommonN;
Maria = properNameEng "Maria";
Milk = regNounEng "milk" CommonN;
Nest = regNounEng "nest" CommonN;
New = adj "new";
Path = regNounEng "path" CommonN;
Pedro = properNameEng "Pedro";
Picture = regNounEng "picture" CommonN;
Pit = regNounEng "pit" CommonN;
Pumpkin = regNounEng "pumpkin" CommonN;
Red = adj "red";
River = regNounEng "river" CommonN;
Round = adj "round";
Seed = regNounEng "seed" CommonN;
Son_Of_Woman = regNounEng "son" CommonN;
Son_Of_Man = regNounEng "son" CommonN;
Daughter_Of_Woman = regNounEng "daughter" CommonN;
Daughter_Of_Man = regNounEng "daughter" CommonN;
Stone = regNounEng "stone" CommonN;
Street = regNounEng "street" CommonN;
Strong = adj "strong";
Tapioca_Cake = regNounEng "tapioca cake" CommonN;
Toucan = regNounEng "toucan" CommonN;
Tree = regNounEng "tree" CommonN;
Water = regNounEng "water" CommonN;
Wife = regNounEng "wife" CommonN;
Woman = nounEng "woman" "women" CommonN;
Word = regNounEng "word" CommonN;

}
