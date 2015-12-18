{-|
Module      : ConstraintTyping
Description : 制約型付けを行う。

制約型付けを行う。第22章の実装。
-}
module ConstraintTyping where
import Data.Bifunctor
import Syntax

-- | 二つの型の間の等式制約を表す。
type Constraint = (Type, Type)

-- | 型付け文脈。
type Context = [(Variable, Type)]

-- | 型付け文脈の定義域を返す。
dom :: Context -> [Variable]
dom ctx = map fst ctx

-- | 制約を生成する。
-- 演習22.3.10の解答。
recon :: Context -> [TypeVariable] -> Term -> Either String (Type, [TypeVariable], [Constraint])
recon ctx f (TmVar x) = do ty <- case lookup x ctx of
                                   Just ty -> Right ty
                                   Nothing -> Left "error"
                           Right (ty, f, [])
recon ctx f (TmAbs x ty1 t2) | notElem x (dom ctx)
                               = do (ty2, f', c) <- recon (ctx ++ [(x, ty1)]) f t2
                                    Right (TyArr ty1 ty2, f', c)
                             | otherwise = Left "error"
recon ctx f (TmApp t1 t2) = do (ty1, f', c1) <- recon ctx f t1
                               (ty2, f'', c2) <- recon ctx f' t2
                               (let x = head f'' in
                                let f''' = tail f'' in
                                Right ((TyVar x), f''', c1 ++ c2 ++ [(ty1, TyArr ty2 (TyVar x))]))
recon ctx f TmZero = Right (TyNat, f, [])
recon ctx f (TmSucc t1) = do (ty, f', c) <- recon ctx f t1
                             Right (TyNat, f, c ++ [(ty, TyNat)])
recon ctx f (TmPred t1) = do (ty, f', c) <- recon ctx f t1
                             Right (TyNat, f, c ++ [(ty, TyNat)])
recon ctx f (TmIsZero t1) = do (ty, f', c) <- recon ctx f t1
                               Right (TyBool, f, c ++ [(ty, TyNat)])
recon ctx f TmTrue = Right (TyBool, f, [])
recon ctx f TmFalse = Right (TyBool, f, [])
recon ctx f (TmIf t1 t2 t3) = do (ty1, f', c1) <- recon ctx f t1
                                 (ty2, f'', c2) <- recon ctx f' t2
                                 (ty3, f''', c3) <- recon ctx f'' t3
                                 Right (ty2, f''', c1 ++ c2 ++ c3 ++ [(ty1, TyBool), (ty2, ty3)])

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
unify :: [Constraint] -> Either String TypeSubstitution
unify [] = Right []
unify ((s, t):constrains)
    | s == t = unify constrains
    | TyVar x <- s, notElem x (fv t) = do sub <- unify (applySubstToConstrains [(x, t)] constrains)
                                          Right (comp sub [(x, t)])
    | TyVar x <- t, notElem x (fv s) = do sub <- unify (applySubstToConstrains [(x, s)] constrains)
                                          Right (comp sub [(x, s)])
    | TyArr s1 s2 <- s, TyArr t1 t2 <- t = unify (constrains ++ [(s1, t1), (s2, t2)])
    | otherwise = Left "Unsolvable constraints"

-- | フレッシュな型変数の列。
-- 無限列にしたいところだが、そうすると列が等しいか否かの比較(テストで必要になる)が停止しないので、有限列にする。
f = map (\i -> Tv ("?X" ++ (show i))) [0..9]

-- | 空の型付け文脈Γと項tとの組(Γ,t)の主要解を返す。
principalSolution :: Term -> Either String (TypeSubstitution, Type)
principalSolution t = do (ty, f', c) <- recon [] f t
                         principalUnifier <- unify c
                         Right (principalUnifier, ty)

-- | 空の型付け文脈における項の主要型を返す。
-- 演習22.5.5の解答。
typeof1 :: Term -> Either String Type
typeof1 t = do (principalUnifier, ty) <- principalSolution t
               Right (applySubst principalUnifier ty)

-- | 空の型付け文脈における項の主要型を段階的に計算して返す。
-- 演習22.5.6の解答。
typeof :: Context -> [TypeVariable] -> Term -> Either String (Type, [TypeVariable], TypeSubstitution)
typeof ctx f (TmVar x) = do ty <- case lookup x ctx of
                                  Just ty -> Right ty
                                  Nothing -> Left "error"
                            Right (ty, f, [])
typeof ctx f (TmAbs x ty1 t2) | notElem x (dom ctx)
                              = do (ty2, f', unifier) <- typeof (ctx ++ [(x, ty1)]) f t2
                                   Right ((applySubst unifier (TyArr ty1 ty2)), f', unifier)
                              | otherwise = Left "error"
typeof ctx f (TmApp t1 t2) = do (ty1, f', unifier1) <- typeof ctx f t1
                                (ty2, f'', unifier2) <- typeof ctx f' t2
                                tyX <- Right (TyVar (head f''))
                                unifier3 <- unify [(ty1, TyArr ty2 tyX)]
                                unifier <- Right (foldr1 comp [unifier3, unifier2, unifier1])
                                Right ((applySubst unifier tyX), tail f'', unifier)
typeof ctx f TmZero = Right (TyNat, f, [])
typeof ctx f (TmSucc t1) = do (ty, f', unifier1) <- typeof ctx f t1
                              unifier <- first (\err -> "argument of succ is not a number")
                                               (unify [(ty, TyNat)])
                              Right (TyNat, f', unifier)
typeof ctx f (TmPred t1) = do (ty, f', unifier1) <- typeof ctx f t1
                              unifier <- first (\err -> "argument of pred is not a number")
                                               (unify [(ty, TyNat)])
                              Right (TyNat, f', unifier)
typeof ctx f (TmIsZero t1) = do (ty, f', unifier1) <- typeof ctx f t1
                                unifier <- first (\err -> "argument of iszero is not a number")
                                                 (unify [(ty, TyNat)])
                                Right (TyNat, f', unifier)
typeof ctx f TmTrue = Right (TyBool, f, [])
typeof ctx f TmFalse = Right (TyBool, f, [])
typeof ctx f (TmIf t1 t2 t3) = do (ty1, f', unifier1) <- typeof ctx f t1
                                  (ty2, f'', unifier2) <- typeof ctx f' t2
                                  (ty3, f''', unifier3) <- typeof ctx f'' t3
                                  unifier4 <- unify [(ty1, TyBool), (ty2, ty3)]
                                  unifier <- Right (foldr1 comp [unifier4, unifier3, unifier2, unifier1])
                                  Right ((applySubst unifier ty2), f''', unifier)
