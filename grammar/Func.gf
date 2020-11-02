-- GrammYEP - a multilingual computational grammar for Nheengatu, English, and Portuguese
-- (c) 2020 Leonel Figueiredo de Alencar
-- Licensed under the terms of the GNU Lesser General Public License, version 2.1
-- See LICENSE or visit the URL
-- https://www.gnu.org/licenses/old-licenses/lgpl-2.1.en.html


abstract Func = Gra** {
fun

	Very : Quality -> Quality ;
    TheSG, ThePL, This, That, These, Those : Kind -> NonDeitic ;
    He, She, It, They, I, YouSG, YouPL, We : Deitic;
    His, Her, Its, Their, My, YourSG, YourPL, Our : PossPro;
    On, With, In, Near : Item -> Location ;
    Here, There : Location ;
    Yes, No : Polarity ;
    PL, SG : Num ;

}
