module Step where
import ConstraintTyping

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
                                unifier3 <- case unify [(ty1, TyArr ty2 tyX)] of
                                              Just unifier -> Right unifier
                                              Nothing -> Left "error"
                                unifier <- Right (foldr1 comp [unifier3, unifier2, unifier1])
                                Right ((applySubst unifier tyX), tail f'', unifier)
typeof ctx f TmZero = Right (TyNat, f, [])
typeof ctx f (TmSucc t1) = do (ty, f', unifier1) <- typeof ctx f t1
                              unifier <- case unify [(ty, TyNat)] of
                                           Just unifier -> Right unifier
                                           Nothing -> Left "error"
                              Right (TyNat, f', unifier)
typeof ctx f (TmPred t1) = typeof ctx f (TmSucc t1)
typeof ctx f (TmIsZero t1) = typeof ctx f (TmSucc t1)
typeof ctx f TmTrue = Right (TyBool, f, [])
typeof ctx f TmFalse = Right (TyBool, f, [])
typeof ctx f (TmIf t1 t2 t3) = do (ty1, f', unifier1) <- typeof ctx f t1
                                  (ty2, f'', unifier2) <- typeof ctx f' t2
                                  (ty3, f''', unifier3) <- typeof ctx f'' t3
                                  unifier4 <- case unify [(ty1, TyBool), (ty2, ty3)] of
                                                Just unifier -> Right unifier
                                                Nothing -> Left "error"
                                  unifier <- Right (foldr1 comp [unifier4, unifier3, unifier2, unifier1])
                                  Right ((applySubst unifier ty2), f''', unifier)
