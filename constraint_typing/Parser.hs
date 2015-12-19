module Parser where
import Text.ParserCombinators.Parsec
import Syntax

withSpaces :: Parser a -> Parser a
withSpaces p = do t <- p
                  spaces
                  return t

symbol :: String -> Parser String
symbol s = try (string s)

-- 型の構文規則。
-- V ::= "A" | ... | "Z"
-- T ::= Bool | Nat | V | T -> T | (T)
-- 左再帰を除去する。
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

-- 項の構文規則。
-- 抽象または適用の項を別の項に適用するときは括弧で括るよう強制するため、fという記号を導入する。
-- v ::= "a" | ... | "z"
-- abs_body ::= v | abs | (t)
-- abs ::= \v:T.abs_body
-- fun ::= v | (t)
-- arg ::= v | abs | (t)
-- t ::= v | abs | fun " " arg | (t)
-- 間接左再帰を除去する。
-- t  ::= v t' | abs | (t) t'
-- t' ::= e | " " v | " " abs | " " (t)
-- 空白等を明示する。
-- abs_body ::= v | abs | enclosed_t
-- abs ::= "\" spaces v spaces ":" spaces T spaces "." spaces abs_body
-- fun ::= v | enclosed_t
-- arg ::= v | abs | (t)
-- expr ::= spaces t spaces eof
-- t ::= v t' | abs | enclosed_t t'
-- t' ::= e | space spaces v | space spaces abs | space spaces enclosed_t
-- enclosed_t ::= "(" spaces t spaces ")"

termExpr :: Parser Term
termExpr = do spaces
              t <- term
              spaces
              eof
              return t

term :: Parser Term
term = _abs
       <|> withTermTail (var
                         <|> enclosedTerm)

var :: Parser Term
var = do v <- letter
         return (TmVar (Vr [v]))

absBody :: Parser Term
absBody = var <|> _abs <|> enclosedTerm

_abs :: Parser Term
_abs = do withSpaces (symbol "\\")
          TmVar v <- var
          spaces
          withSpaces (symbol ":")
          ty <- _type
          spaces
          withSpaces (symbol ".")
          t <- absBody
          return (TmAbs v ty t)

enclosedTerm :: Parser Term
enclosedTerm = do withSpaces (symbol "(")
                  t <- term
                  spaces
                  symbol ")"
                  return t

withTermTail :: Parser Term -> Parser Term
withTermTail p = do t <- p
                    tail <- termTail
                    return (tail t)

termTail :: Parser (Term -> Term)
termTail = try (do space
                   spaces
                   t2 <- var <|> _abs <|> enclosedTerm
                   return (\t1 -> TmApp t1 t2))
           <|> emptyTermTail

emptyTermTail :: Parser (Term -> Term)
emptyTermTail = return id
