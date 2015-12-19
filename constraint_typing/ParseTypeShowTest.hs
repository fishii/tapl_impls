import Test.HUnit
import System.IO
import Data.Bifunctor
import Syntax
import Parser
import ConstraintTyping

parseTypeShow :: String -> String
parseTypeShow s = case (parseTerm s) of
                  Left err -> "ParseError: " ++ (show err)
                  Right t -> case typeof [] f t of
                             Left s -> s
                             Right (ty, vars, unifier) -> show ty

parseTypeShowTests = TestList
    [
      "true : Bool" ~: parseTypeShow " true " ~?= "Bool"
    , "false : Bool" ~: parseTypeShow " false " ~?= "Bool"
    , "if true then true else false : Bool" ~:
      parseTypeShow " if true then true else false " ~?= "Bool"
    , "0 : Nat" ~: parseTypeShow " 0 " ~?= "Nat"
    , "succ 0 : Nat" ~: parseTypeShow " succ 0 " ~?= "Nat"
    , "pred 0 : Nat" ~: parseTypeShow " pred 0 " ~?= "Nat"
    , "iszero 0 : Nat" ~: parseTypeShow " iszero 0 " ~?= "Nat"
    , " \\x:X. x : X -> X" ~: parseTypeShow " \\x:X. x " ~?= "(X -> X)"
    , " \\z:Z. \\y:Y. z (y true) : (?X0 -> ?X1) -> (Bool -> ?X0) -> ?X1" ~:
      parseTypeShow " \\z:Z. \\y:Y. (z (y true)) " ~?= "((?X0 -> ?X1) -> ((Bool -> ?X0) -> ?X1))"
    ]

main = do
    runTestText (putTextToHandle stderr False) parseTypeShowTests
