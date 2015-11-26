module Step where
import ConstraintTyping

-- | 空の型付け文脈における項の主要型を段階的に計算して返す。
-- 演習22.5.6の解答。
step :: Context -> [TypeVariable] -> Term -> Maybe (Type, [TypeVariable], TypeSubstitution)
step ctx f (TmVar x) = do ty <- lookup x ctx
                          Just (ty, f, [])
step ctx f (TmAbs x ty1 t2) | notElem x (dom ctx)
                              = do (ty2, f', unifier) <- step (ctx ++ [(x, ty1)]) f t2
                                   Just ((applySubst unifier (TyArr ty1 ty2)), f', unifier)
                            | otherwise = Nothing
step ctx f (TmApp t1 t2) = do (ty1, f', unifier1) <- step ctx f t1
                              (ty2, f'', unifier2) <- step ctx f' t2
                              tyX <- Just (TyVar (head f''))
                              unifier3 <- unify [(ty1, TyArr ty2 tyX)]
                              unifier <- Just (foldr1 comp [unifier3, unifier2, unifier1])
                              Just ((applySubst unifier tyX), tail f'', unifier)
step ctx f TmZero = Just (TyNat, f, [])
step ctx f (TmSucc t1) = do (ty, f', unifier1) <- step ctx f t1
                            unifier <- unify [(ty, TyNat)]
                            Just (TyNat, f', unifier)
step ctx f (TmPred t1) = step ctx f (TmSucc t1)
step ctx f (TmIsZero t1) = step ctx f (TmSucc t1)
step ctx f TmTrue = Just (TyBool, f, [])
step ctx f TmFalse = Just (TyBool, f, [])
step ctx f (TmIf t1 t2 t3) = do (ty1, f', unifier1) <- step ctx f t1
                                (ty2, f'', unifier2) <- step ctx f' t2
                                (ty3, f''', unifier3) <- step ctx f'' t3
                                unifier4 <- unify [(ty1, TyBool), (ty2, ty3)]
                                unifier <- Just (foldr1 comp [unifier4, unifier3, unifier2, unifier1])
                                Just ((applySubst unifier ty2), f''', unifier)
