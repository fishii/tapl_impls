module Parser where
import Text.ParserCombinators.Parsec
import Syntax

spaces1 = many1 space

symbol :: String -> Parser String
symbol s = try (string s)

-- 型の構文規則。
-- V ::= "A" | ... | "Z"
-- T ::= Bool | Nat | V | T -> T | (T)
-- 左再帰を除去する。
-- 結果的に矢印型が右結合になる。
-- T ::= T_head T_tail
-- T_head ::= Bool | Nat | V | (T)
-- T_tail ::= e | -> T
-- 字句を明示する。
-- E ::= spaces T spaces eof
-- T ::= T_head T_tail
-- T_head ::= "Bool" | "Nat" | V | "(" spaces T spaces ")" spaces T''
-- T_tail ::= e | "->" spaces T

typeExpr :: Parser Type
typeExpr = do spaces
              ty <- _type
              spaces
              eof
              return ty

_type :: Parser Type
_type = arr typeHead typeTail

arr :: Parser Type -> Parser (Type -> Type) -> Parser Type
arr p1 p2 = do head <- p1
               spaces
               tail <- p2
               return (tail head)

typeHead :: Parser Type
typeHead = typeBool
        <|> typeNat
        <|> typeVar
        <|> enclosedType

typeBool :: Parser Type
typeBool = do symbol "Bool"
              return TyBool

typeNat :: Parser Type
typeNat = do symbol "Nat"
             return TyNat

typeVar :: Parser Type
typeVar = do x <- letter
             return (TyVar (Tv [x]))

enclosedType :: Parser Type
enclosedType = do symbol "("
                  spaces
                  ty <- _type
                  spaces
                  symbol ")"
                  return ty

typeTail :: Parser (Type -> Type)
typeTail = arrowTypeTail
        <|> emptyTypeTail

arrowTypeTail :: Parser (Type -> Type)
arrowTypeTail = do symbol "->"
                   spaces
                   ty2 <- _type
                   return (\ty1 -> (TyArr ty1 ty2))

emptyTypeTail :: Parser (Type -> Type)
emptyTypeTail = return id

parseType = parse typeExpr ""

-- 項の構文規則。
-- 結合の優先順位を示すためfun、argという記号を導入する。
-- funは関数適用の第1項になり得る項。
-- argは関数適用の第2項およびラムダ抽象の本体になり得る項。
-- var ::= "a" | ... | "z"
-- abs ::= \ v : T . arg
-- fun ::= true | false | 0 | var | (t)
-- arg ::= fun | abs
-- t ::= if fun then fun else fun | succ arg | pred arg | iszero arg | arg | fun " " arg
-- 間接左再帰を除去する。
-- t ::= if fun then fun else fun | succ arg | pred arg | iszero arg | abs | fun t_tail
-- t_tail ::= e | " " arg
-- 字句を明示する。
-- abs ::= "\" spaces v spaces ":" spaces T spaces "." spaces abs_body
-- fun ::= true | false | 0 | var | enclosed_t
-- arg ::= fun | abs
-- expr ::= spaces t spaces eof
-- t ::= ... | abs | fun t_tail
-- t_tail ::= e | spaces1 arg
-- enclosed_t ::= "(" spaces t spaces ")"

termExpr :: Parser Term
termExpr = do spaces
              t <- term
              spaces
              eof
              return t

term :: Parser Term
term = _if
    <|> _succ
    <|> _pred
    <|> iszero
    <|> _abs
    <|> app fun arg

app :: Parser Term -> Parser Term -> Parser Term
app f a = do t1 <- f
             t2 <- (try (do spaces1
                            t2 <- a
                            return (\t1 -> TmApp t1 t2)))
                   <|> return id
             return (t2 t1)

fun :: Parser Term
fun = true <|> false <|> zero <|> var <|> enclosedTerm

arg :: Parser Term
arg = fun <|> _abs

true :: Parser Term
true = do symbol "true"
          return TmTrue

false :: Parser Term
false = do symbol "false"
           return TmFalse

_if :: Parser Term
_if = do symbol "if"
         spaces1
         t1 <- fun
         spaces1
         symbol "then"
         spaces1
         t2 <- fun
         spaces1
         symbol "else"
         spaces1
         t3 <- fun
         return (TmIf t1 t2 t3)

zero :: Parser Term
zero = do symbol "0"
          return TmZero

_succ :: Parser Term
_succ = do symbol "succ"
           spaces1
           t <- arg
           return (TmSucc t)

_pred :: Parser Term
_pred = do symbol "pred"
           spaces1
           t <- arg
           return (TmPred t)

iszero :: Parser Term
iszero = do symbol "iszero"
            spaces1
            t <- arg
            return (TmIsZero t)

var :: Parser Term
var = do v <- letter
         return (TmVar (Vr [v]))

_abs :: Parser Term
_abs = do symbol "\\"
          spaces
          TmVar v <- var
          spaces
          symbol ":"
          spaces
          ty <- _type
          spaces
          symbol "."
          spaces
          t <- arg
          return (TmAbs v ty t)

enclosedTerm :: Parser Term
enclosedTerm = do symbol "("
                  spaces
                  t <- term
                  spaces
                  symbol ")"
                  return t

parseTerm :: String -> Either ParseError Term
parseTerm = parse termExpr ""
