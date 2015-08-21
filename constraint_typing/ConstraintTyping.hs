module ConstraintTyping where

-- 変数。
-- 変数と変数のみからなる項を異なる型で表す。
-- ラムダ抽象の束縛変数の位置に変数しか指定できないことを表現するため。
data Variable = Vr String
                deriving(Show, Eq)

data Term = TmVar Variable -- 変数のみからなる項。
          | TmAbs Variable Type Term -- 変数、型注釈、本体。
          | TmApp Term Term
          | TmZero
          | TmSucc Term
          | TmPred Term
          | TmIsZero Term
          | TmTrue
          | TmFalse
          | TmIf Term Term Term
            deriving(Show, Eq)

-- 型変数。
-- 型変数と型変数のみからなる型を異なる型で表す。
-- 型代入の左辺に型変数しか指定できないことを表現するため。
data TypeVariable = Tv String
                    deriving(Eq)

instance Show TypeVariable where
    show (Tv id) = id

data Type = TyBool
          | TyNat
          | TyArr Type Type
          | TyVar TypeVariable -- 型変数のみからなる型。
            deriving(Eq)

instance Show Type where
    show TyBool = "Bool"
    show TyNat = "Nat"
    show (TyArr ty1 ty2) = "(" ++ (show ty1) ++ " -> " ++ (show ty2) ++ ")"
    show (TyVar (Tv id)) = id

type Constraint = (Type, Type)

type Context = [(Variable, Type)]

dom :: Context -> [Variable]
dom ctx = map fst ctx

recon :: Context -> [TypeVariable] -> Term -> Maybe (Type, [TypeVariable], [Constraint])
recon ctx f t@(TmVar x) = do ty <- lookup x ctx
                             Just (ty, f, [])
recon ctx f t@(TmAbs x ty1 t2) | not (elem x (dom ctx))
                               = do (ty2, f', c) <- recon (ctx ++ [(x, ty1)]) f t2
                                    Just (TyArr ty1 ty2, f', c)
                               | otherwise = Nothing
recon ctx f t@(TmApp t1 t2) = do (ty1, f', c1) <- recon ctx f t1
                                 (ty2, f'', c2) <- recon ctx f' t2
                                 (let x = head f'' in
                                  let f''' = tail f'' in
                                  Just ((TyVar x), f''', c1 ++ c2 ++ [(ty1, TyArr ty2 (TyVar x))]))
recon ctx f t@TmZero = Just (TyNat, f, [])
recon ctx f t@(TmSucc t1) = do (ty, f', c) <- recon ctx f t1
                               Just (TyNat, f, c ++ [(ty, TyNat)])
recon ctx f t@(TmPred t1) = do (ty, f', c) <- recon ctx f t1
                               Just (TyNat, f, c ++ [(ty, TyNat)])
recon ctx f t@(TmIsZero t1) = do (ty, f', c) <- recon ctx f t1
                                 Just (TyBool, f, c ++ [(ty, TyNat)])
recon ctx f t@TmTrue = Just (TyBool, f, [])
recon ctx f t@TmFalse = Just (TyBool, f, [])
recon ctx f t@(TmIf t1 t2 t3) = do (ty1, f', c1) <- recon ctx f t1
                                   (ty2, f'', c2) <- recon ctx f' t2
                                   (ty3, f''', c3) <- recon ctx f'' t3
                                   Just (ty2, f''', c1 ++ c2 ++ c3 ++ [(ty1, TyBool), (ty2, ty3)])

type TypeSubstitution = [(TypeVariable, Type)]

applySubst :: TypeSubstitution -> Type -> Type
applySubst [] t = t
applySubst _ TyBool = TyBool
applySubst _ TyNat = TyNat
applySubst sub (TyArr t1 t2) = TyArr (applySubst sub t1)
                                     (applySubst sub t2)
applySubst ((x, s):sub') t@(TyVar y) = if x == y then s else applySubst sub' t

comp :: TypeSubstitution -> TypeSubstitution -> TypeSubstitution
comp sub1 sub2 = (map (\(x, s) -> (x, applySubst sub1 s)) sub2) ++ sub1

applySubstToConstrains :: TypeSubstitution -> [Constraint] -> [Constraint]
applySubstToConstrains sub constrs = map (\(s, t) -> (applySubst sub s, applySubst sub t)) constrs

fv :: Type -> [TypeVariable]
fv TyBool = []
fv TyNat = []
fv (TyArr ty1 ty2) = (fv ty1) ++ (fv ty2)
fv (TyVar x) = [x]

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

-- フレッシュな型変数の列。
-- 無限列にしたいところだが、そうすると列が等しいか否かの比較(テストで必要になる)が終らないので、有限列にする。
f = map (\i -> Tv ("?X" ++ (show i))) [0..9]

principalTypeof :: Term -> Maybe Type
principalTypeof t = do (ty, f', c) <- recon [] f t
                       principalUnifiers <- unify c
                       Just (applySubst principalUnifiers ty)

principalSolution :: Term -> Maybe (TypeSubstitution, Type)
principalSolution t = do (ty, f', c) <- recon [] f t
                         principalUnifiers <- unify c
                         Just (principalUnifiers, ty)
