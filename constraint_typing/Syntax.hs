{-|
Module      : Syntax
Description : 制約型付けを行う。

制約型付けを行う。第22章の実装。
-}
module Syntax where

-- | 項の上を動く変数。
-- ラムダ抽象の束縛変数の位置に変数しか指定できないことを表現するため、
-- 変数と変数のみからなる項を異なる型で表す。
data Variable = -- | 変数名を引数に取る。
                Vr String
                deriving(Show, Eq)

-- | 項。
data Term = -- | 変数のみからなる項。
            TmVar Variable
            -- | ラムダ抽象。束縛変数、型注釈、本体を引数に取る。
          | TmAbs Variable Type Term
          | TmApp Term Term
          | TmZero
          | TmSucc Term
          | TmPred Term
          | TmIsZero Term
          | TmTrue
          | TmFalse
          | TmIf Term Term Term
            deriving(Show, Eq)

-- | 型変数。
-- 型代入の左辺に型変数しか指定できないことを表現するため、
-- 型変数と型変数のみからなる型を異なる型で表す。
data TypeVariable = -- | 変数名を引数に取る。
                    Tv String
                    deriving(Eq)

-- | デバッグ時の分かりやすさのため、変数名のみを表示する。
instance Show TypeVariable where
    show (Tv id) = id

-- | 型。
data Type = TyBool
          | TyNat
          | TyArr Type Type
            -- | 型変数のみからなる型。
          | TyVar TypeVariable
            deriving(Eq)

-- | デバッグ時の分かりやすさのため、矢印等を使って型を表示する。
instance Show Type where
    show TyBool = "Bool"
    show TyNat = "Nat"
    show (TyArr ty1 ty2) = "(" ++ (show ty1) ++ " -> " ++ (show ty2) ++ ")"
    show (TyVar (Tv id)) = id
