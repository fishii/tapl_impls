{-|
Module      : ConstraintTyping
Description : 制約型付けを行う。

制約型付けを行う。第22章の実装。
-}
module ConstraintTyping where

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

-- | 二つの型の間の等式制約を表す。
type Constraint = (Type, Type)

-- | 型付け文脈。
type Context = [(Variable, Type)]

-- | 型付け文脈の定義域を返す。
dom :: Context -> [Variable]
dom ctx = map fst ctx

-- | 制約を生成する。
-- 演習22.3.10の解答。
recon :: Context -> [TypeVariable] -> Term -> Maybe (Type, [TypeVariable], [Constraint])
recon ctx f (TmVar x) = do ty <- lookup x ctx
                           Just (ty, f, [])
recon ctx f (TmAbs x ty1 t2) | notElem x (dom ctx)
                               = do (ty2, f', c) <- recon (ctx ++ [(x, ty1)]) f t2
                                    Just (TyArr ty1 ty2, f', c)
                             | otherwise = Nothing
recon ctx f (TmApp t1 t2) = do (ty1, f', c1) <- recon ctx f t1
                               (ty2, f'', c2) <- recon ctx f' t2
                               (let x = head f'' in
                                let f''' = tail f'' in
                                Just ((TyVar x), f''', c1 ++ c2 ++ [(ty1, TyArr ty2 (TyVar x))]))
recon ctx f TmZero = Just (TyNat, f, [])
recon ctx f (TmSucc t1) = do (ty, f', c) <- recon ctx f t1
                             Just (TyNat, f, c ++ [(ty, TyNat)])
recon ctx f (TmPred t1) = do (ty, f', c) <- recon ctx f t1
                             Just (TyNat, f, c ++ [(ty, TyNat)])
recon ctx f (TmIsZero t1) = do (ty, f', c) <- recon ctx f t1
                               Just (TyBool, f, c ++ [(ty, TyNat)])
recon ctx f TmTrue = Just (TyBool, f, [])
recon ctx f TmFalse = Just (TyBool, f, [])
recon ctx f (TmIf t1 t2 t3) = do (ty1, f', c1) <- recon ctx f t1
                                 (ty2, f'', c2) <- recon ctx f' t2
                                 (ty3, f''', c3) <- recon ctx f'' t3
                                 Just (ty2, f''', c1 ++ c2 ++ c3 ++ [(ty1, TyBool), (ty2, ty3)])

-- | 型代入。
type TypeSubstitution = [(TypeVariable, Type)]

-- | 型式に型代入を適用する。
applySubst :: TypeSubstitution -> Type -> Type
applySubst [] t = t
applySubst _ TyBool = TyBool
applySubst _ TyNat = TyNat
applySubst sub (TyArr t1 t2) = TyArr (applySubst sub t1)
                                     (applySubst sub t2)
applySubst ((x, s):sub') t@(TyVar y) = if x == y then s else applySubst sub' t

-- | 型代入を合成する。
comp :: TypeSubstitution -> TypeSubstitution -> TypeSubstitution
comp sub1 sub2 = (map (\(x, s) -> (x, applySubst sub1 s)) sub2) ++ sub1

-- | 制約集合に型代入を適用する。
applySubstToConstrains :: TypeSubstitution -> [Constraint] -> [Constraint]
applySubstToConstrains sub constrs = map (\(s, t) -> (applySubst sub s, applySubst sub t)) constrs

-- | 型に含まれる自由な型変数を返す。
fv :: Type -> [TypeVariable]
fv TyBool = []
fv TyNat = []
fv (TyArr ty1 ty2) = (fv ty1) ++ (fv ty2)
fv (TyVar x) = [x]

-- | 制約集合を単一化する型代入を返す。
-- 演習22.4.6の解答。
unify :: [Constraint] -> Maybe TypeSubstitution
unify [] = Just []
unify ((s, t):constrains)
    | s == t = unify constrains
    | TyVar x <- s, notElem x (fv t) = do sub <- unify (applySubstToConstrains [(x, t)] constrains)
                                          Just (comp sub [(x, t)])
    | TyVar x <- t, notElem x (fv s) = do sub <- unify (applySubstToConstrains [(x, s)] constrains)
                                          Just (comp sub [(x, s)])
    | TyArr s1 s2 <- s, TyArr t1 t2 <- t = unify (constrains ++ [(s1, t1), (s2, t2)])
unify _ = Nothing

-- | フレッシュな型変数の列。
-- 無限列にしたいところだが、そうすると列が等しいか否かの比較(テストで必要になる)が停止しないので、有限列にする。
f = map (\i -> Tv ("?X" ++ (show i))) [0..9]

-- | 空の型付け文脈Γと項tとの組(Γ,t)の主要解を返す。
principalSolution :: Term -> Maybe (TypeSubstitution, Type)
principalSolution t = do (ty, f', c) <- recon [] f t
                         principalUnifier <- unify c
                         Just (principalUnifier, ty)

-- | 空の型付け文脈における項の主要型を返す。
-- 演習22.5.5の解答。
principalTypeof :: Term -> Maybe Type
principalTypeof t = do (principalUnifier, ty) <- principalSolution t
                       Just (applySubst principalUnifier ty)
