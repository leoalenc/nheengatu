-- GrammYEP - a multilingual computational grammar for Nheengatu, English, and Portuguese
-- (c) 2020 Leonel Figueiredo de Alencar
-- Licensed under the terms of the GNU Lesser General Public License, version 2.1
-- See LICENSE or visit the URL
-- https://www.gnu.org/licenses/old-licenses/lgpl-2.1.en.html


abstract Gra = {
  flags startcat = Comment ;
  cat
    Comment ; Item ; Psor ; Kind ; SimpleKind ; State ; Quality ; Property ; Location ; Deitic ; NonDeitic ; Polarity ; PossPro ; PossKind ; Num ; 
  fun
    Pred:Polarity->Item->State->Comment;
    StageLevelState : Property -> State ;
    IndLevelState : Property -> State ;
    Mod : Quality -> Kind -> Kind ;
    Poss : Psor -> NonDeitic -> Item ;
    Poss_ : PossPro -> SimpleKind -> PossKind ;
    mkPsor : Num -> SimpleKind ->  Psor ;
    mkPsor_ : Num -> PossKind -> Psor ;
    mkKind : SimpleKind -> Kind ;
    mkKind_ : PossKind -> Kind ;
    mkItemDeitic : Deitic -> Item ;
    mkItemNonDeitic : NonDeitic -> Item ;
    mkPropLoc : Location -> Property ;
    mkPropQual : Quality -> Property ;
    
}
