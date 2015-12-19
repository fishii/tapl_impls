import Test.HUnit
import System.IO
import Data.Bifunctor
import Text.ParserCombinators.Parsec
import Text.Parsec.Error
import Text.Parsec.Pos
import Syntax
import Parser

tv_X = Tv "X"
ty_X = TyVar tv_X
tv_Y = Tv "Y"
ty_Y = TyVar tv_Y
tv_Z = Tv "Z"
ty_Z = TyVar tv_Z
vr_x = Vr "x"
tm_x = TmVar vr_x
vr_y = Vr "y"
tm_y = TmVar vr_y
vr_z = Vr "z"
tm_z = TmVar vr_z
id_x = TmAbs vr_x ty_X tm_x

parseType' = parse typeExpr ""

-- パースに失敗したとき返されるParseErrorは複雑で、
-- テストの期待値を作るのが面倒なので、
-- 失敗した位置だけを返すようにする。
parseType :: String -> Either SourcePos Type
parseType s = first errorPos (parseType' s)

typeTests = TestList
    [
      " Bool " ~: parseType " Bool " ~?= Right TyBool
    , " Nat " ~: parseType " Nat " ~?= Right TyNat
    , " B " ~: parseType " B " ~?= Right (TyVar (Tv "B"))
    , " N " ~: parseType " N " ~?= Right (TyVar (Tv "N"))
    , " X " ~: parseType " X " ~?= Right ty_X
    , " X -> Y " ~: parseType " X -> Y " ~?= Right (TyArr ty_X ty_Y)
    , " ( X ) " ~: parseType " ( X ) " ~?= Right ty_X
    , " ( ( X ) ) " ~: parseType " ( ( X ) ) " ~?= Right ty_X
    , " ( ( X ) -> ( Y ) ) " ~: parseType " ( ( X ) -> ( Y ) ) " ~?= Right (TyArr ty_X ty_Y)
    , " ( ( Bool ) -> ( Nat ) ) " ~: parseType " ( ( Bool ) -> ( Nat ) ) " ~?= Right (TyArr TyBool TyNat)
    , " X -> Y -> Z " ~: parseType " X -> Y -> Z " ~?= Right (TyArr ty_X (TyArr ty_Y ty_Z))
    , " ( X -> Y ) -> Z " ~: parseType " ( X -> Y ) -> Z " ~?= Right (TyArr (TyArr ty_X ty_Y) ty_Z)
    , "XY" ~: parseType "XY" ~?= Left (newPos "" 1 2)
    ]

parseTerm' = parse termExpr ""

-- パースに失敗したとき返されるParseErrorは複雑で、
-- テストの期待値を作るのが面倒なので、
-- 失敗した位置だけを返すようにする。
parseTerm :: String -> Either SourcePos Term
parseTerm s = first errorPos (parseTerm' s)

termTests = TestList
    [
      " x " ~: parseTerm " x " ~?= Right tm_x
    , " ( x ) " ~: parseTerm " ( x ) " ~?= Right tm_x
    , " ( ( x ) ) " ~: parseTerm " ( ( x ) ) " ~?= Right tm_x
    , "\\x:X.x" ~: parseTerm "\\x:X.x" ~?= Right id_x
    , " \\ x : X . x " ~: parseTerm " \\ x : X . x " ~?= Right id_x
    , "(\\x:X.x)" ~: parseTerm "\\x:X.x" ~?= Right id_x
    , " ( \\ x : X . x ) " ~: parseTerm " ( \\ x : X . x ) " ~?= Right id_x
    , "x y" ~: parseTerm "x y" ~?= Right (TmApp tm_x tm_y)
    , " x y " ~: parseTerm " x y " ~?= Right (TmApp tm_x tm_y)
    , "x (y)" ~: parseTerm "x (y)" ~?= Right (TmApp tm_x tm_y)
    , " x ( y ) " ~: parseTerm " x ( y ) " ~?= Right (TmApp tm_x tm_y)
    , "x \\x:X.x" ~: parseTerm "x \\x:X.x" ~?= Right (TmApp tm_x id_x)
    , "x (\\x:X.x)" ~: parseTerm "x (\\x:X.x)" ~?= Right (TmApp tm_x id_x)
    , "(\\x:X.x) x" ~: parseTerm "(\\x:X.x) x" ~?= Right (TmApp id_x tm_x)
    , " x ( y z ) " ~: parseTerm " x ( y z ) " ~?= Right (TmApp tm_x (TmApp tm_y tm_z))
    , " ( x y ) z " ~: parseTerm " ( x y ) z " ~?= Right (TmApp (TmApp tm_x tm_y) tm_z)
    , "\\x:X.x x" ~: parseTerm "\\x:X.x x" ~?= Left (newPos "" 1 8)
    , " x y z " ~: parseTerm " x y z " ~?= Left (newPos "" 1 6)
    , " xy " ~: parseTerm " xy " ~?= Left (newPos "" 1 3)
    , " true " ~: parseTerm " true " ~?= Right TmTrue
    , " false " ~: parseTerm " false " ~?= Right TmFalse
    , " if x then true else false " ~:
      parseTerm " if x then true else false " ~?= Right (TmIf tm_x TmTrue TmFalse)
    ]

main = do
    runTestText (putTextToHandle stderr False) typeTests
    runTestText (putTextToHandle stderr False) termTests
