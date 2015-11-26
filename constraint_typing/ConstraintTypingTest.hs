import Test.HUnit
import System.IO
import ConstraintTyping

v_x = Vr "x"
t_x = TmVar v_x
v_y = Vr "y"
t_y = TmVar v_y
v_z = Vr "z"
t_z = TmVar v_z

tv_X = Tv "X"
ty_X = TyVar tv_X
tv_Y = Tv "Y"
ty_Y = TyVar tv_Y
tv_Z = Tv "Z"
ty_Z = TyVar tv_Z

tv_X0 = Tv "?X0"
ty_X0 = TyVar tv_X0
tv_X1 = Tv "?X1"
ty_X1 = TyVar tv_X1

reconTests = TestList
    [
      "項が変数の場合。変数が文脈に含まれない場合、制約型付けが失敗する。" ~:
      recon [] f t_x ~?= Nothing

    , "項が変数の場合。変数が文脈に含まれる場合、制約型付けが成功する。" ~:
      recon [(v_x, TyBool)] f t_x ~?= Just (TyBool, f, [])

    , "項がラムダ抽象の場合。束縛変数が文脈に含まれる場合、制約型付けが失敗する。" ~:
      recon [(v_x, TyNat)] f (TmAbs v_x (TyBool) t_x) ~?= Nothing

    , "項がラムダ抽象の場合。束縛変数が文脈に含まれない場合、制約型付けが成功する。" ~:
      recon [] f (TmAbs v_x (TyBool) t_x) ~?= Just ((TyArr TyBool TyBool), f, [])

    , "項がラムダ抽象の場合。型注釈が型変数の場合。" ++
      "lambda x.X x => X -> X where {}" ~:
      recon [] f (TmAbs v_x ty_X t_x)
      ~?= Just ((TyArr ty_X ty_X), f, [])

    , "項が関数適用の場合。" ++
      "y:Bool|-(lambda x:Bool. x) y => Bool where {Bool -> Bool = Bool -> ?X0}" ~:
      recon [(v_y, TyBool)] f (TmApp (TmAbs v_x (TyBool) t_x) t_y)
      ~?= Just (ty_X0, tail f, [(TyArr TyBool TyBool, TyArr TyBool ty_X0)])

    , "項が関数適用の場合。" ++
      "y:Bool|-(lambda x:Bool. 0) y => Nat where {Bool -> Nat = Bool -> ?X0}" ~:
      recon [(v_y, TyBool)] f (TmApp (TmAbs v_x TyBool TmZero) t_y)
      ~?= Just (ty_X0, tail f, [(TyArr TyBool TyNat, TyArr TyBool ty_X0)])

    , "項が関数適用の場合。関数の型注釈が型変数の場合。" ++
      "(lambda x.X x) true => Bool where {X -> X = Bool -> ?X0}" ~:
      recon [] f (TmApp (TmAbs v_x ty_X t_x) TmTrue)
      ~?= Just (ty_X0, tail f, [(TyArr ty_X ty_X, TyArr TyBool ty_X0)])

    , "項が定数ゼロの場合。" ~:
      recon [] f TmZero ~?= Just (TyNat, f, [])

    , "項が後者値の場合。" ~:
      recon [] f (TmSucc TmZero) ~?= Just (TyNat, f, [(TyNat, TyNat)])

    , "項が前者値の場合。" ~:
      recon [] f (TmPred TmZero) ~?= Just (TyNat, f, [(TyNat, TyNat)])

    , "項がゼロ判定の場合。" ~:
      recon [] f (TmIsZero TmZero) ~?= Just (TyBool, f, [(TyNat, TyNat)])

    , "項が定数真の場合。" ~:
      recon [] f TmTrue ~?= Just (TyBool, f, [])

    , "項が定数偽の場合。" ~:
      recon [] f TmFalse ~?= Just (TyBool, f, [])

    , "項が条件式の場合。" ~:
      recon [] f (TmIf TmTrue (TmSucc TmZero) TmZero)
      ~?= Just (TyNat, f, [(TyNat, TyNat), (TyBool, TyBool), (TyNat, TyNat)])

    , "(lambda x:Bool. x) true" ++
      "=> ?X0 where {Bool -> Bool = Bool -> ?X0}" ~:
      recon [] f (TmApp (TmAbs v_x TyBool t_x) TmTrue)
      ~?= Just (ty_X0, tail f,
                [(TyArr TyBool TyBool, TyArr TyBool ty_X0)])

    , "(lambda x:X. x) true" ++
      "=> ?X0 where {X -> X = Bool -> ?X0}" ~:
      recon [] f (TmApp (TmAbs v_x ty_X t_x) TmTrue)
      ~?= Just (ty_X0, tail f,
                [(TyArr ty_X ty_X, TyArr TyBool ty_X0)])

    , "lambda y:Y. y true" ++
      "=> Y -> ?X0 where {(?X0 -> ?X1) -> ((Bool -> ?X0) -> ?X1)}" ~:
      recon [] f (TmAbs v_y ty_Y (TmApp t_y TmTrue))
      ~?= Just (TyArr ty_Y ty_X0,
                tail f,
                [(ty_Y, TyArr TyBool ty_X0)])

    , "lambda z:Z. lambda y:Y. z (y true)" ++
      "=> ?X0 where {(?X0 -> ?X1) -> ((Bool -> ?X0) -> ?X1)}" ~:
      recon [] f (TmAbs v_z ty_Z
                        (TmAbs v_y ty_Y
                               (TmApp t_z (TmApp t_y TmTrue))))
      ~?= Just (TyArr ty_Z (TyArr ty_Y ty_X1),
                tail (tail f),
                [(ty_Y, TyArr TyBool ty_X0), (ty_Z, TyArr ty_X0 ty_X1)])

    , "lambda x:X. if true then false else (x false)" ++
      "=> {X = Bool -> ?X0, Bool = Bool, Bool = ?X0}, X -> Bool" ~:
      recon [] f (TmAbs v_x ty_X (TmIf TmTrue TmFalse (TmApp t_x TmFalse)))
      ~?= Just (TyArr ty_X TyBool, tail f,
                [(ty_X, TyArr TyBool ty_X0), (TyBool, TyBool), (TyBool, ty_X0)])
    ]

compTests = TestList
    [
      "" ~: comp [] [] ~?= []
    , "" ~: comp [(tv_X, TyBool)] [] ~?= [(tv_X, TyBool)]
    ]

unifyTests = TestList
    [
      "C = emptyset" ~:
      unify [] ~?= Just []

    , "S = T" ~:
      unify [(TyBool, TyBool), (TyArr TyNat ty_X, TyArr TyNat ty_X)] ~?= Just []

    , "S = X and X not in FV(T)" ~:
      unify [(ty_X, TyBool)] ~?= Just [(tv_X, TyBool)]

    , "S = X and X in FV(T)" ~:
      unify [(ty_X, TyArr ty_X TyBool)] ~?= Nothing

    , "T = X and X not in FV(S)" ~:
      unify [(TyBool, ty_X)] ~?= Just [(tv_X, TyBool)]

    , "T = X and X in FV(S)" ~:
      unify [(TyArr ty_X TyBool, ty_X)] ~?= Nothing

    , "S = S_1 -> S_2 and T = T_1 -> T_2" ~:
      unify [(TyArr ty_X TyBool, TyArr TyNat TyBool)] ~?= Just [(tv_X, TyNat)]

    , "{Bool -> Bool = Bool -> ?X0} => [?X0 mapsto Bool]" ~:
      unify [(TyArr TyBool TyBool, TyArr TyBool ty_X0)] ~?= Just [(tv_X0, TyBool)]

    , "{X -> Y = Bool -> Nat} => [Y mapsto Nat, X mapsto Bool]" ~:
      unify [(TyArr ty_X ty_Y, TyArr TyBool TyNat)]
      ~?= Just [(tv_X, TyBool), (tv_Y, TyNat)]

    , "{X -> X = Bool -> ?X0} => [?X0 mapsto Bool, X mapsto Bool]" ~:
      unify [(TyArr ty_X ty_X, TyArr TyBool ty_X0)]
      ~?= Just [(tv_X, TyBool), (tv_X0, TyBool)]

    , "[X = Bool -> ?X0, Bool = Bool, Bool = ?X0]" ++
      "=> [X mapsto Bool -> ?X0, ?X0 mapsto Bool]" ~:
      unify [(ty_X, TyArr TyBool ty_X0), (TyBool, TyBool), (TyBool, ty_X0)]
      ~?= Just [(tv_X, TyArr TyBool TyBool), (tv_X0, TyBool)]
    ]

applySubstTests = TestList
    [
      "[X mapsto Y, Y mapsto Z] X => Y" ~:
      applySubst [(tv_X, ty_Y), (tv_Y, ty_Z)] ty_X
      ~?= ty_Y

    , "[?X0 mapsto Bool] ?X0 => Bool" ~:
      applySubst [(tv_X0, TyBool)] ty_X0 ~?= TyBool
    ]

principalSolutionTests = TestList
    [
      "(lambda x:X. x) true => [X mapsto Bool, ?X0 mapsto Bool], ?X0" ~:
      principalSolution (TmApp (TmAbs v_x ty_X t_x) TmTrue)
      ~?= Just ([(tv_X, TyBool), (tv_X0, TyBool)], ty_X0)

    , "lambda x:X. if true then false else (x false)" ++
      "=> [X mapsto Bool -> Bool], X -> Bool" ~:
      principalSolution (TmAbs v_x ty_X (TmIf TmTrue TmFalse (TmApp t_x TmFalse)))
      ~?= Just ([(tv_X, TyArr TyBool TyBool), (tv_X0, TyBool)], TyArr ty_X TyBool)
    ]

typeof1Tests = TestList
    [
      "lambda x:X. x => X -> X" ~:
      typeof1 (TmAbs v_x ty_X t_x)
      ~?= Just (TyArr ty_X ty_X)

    , "true => Bool" ~:
      typeof1 TmTrue
      ~?= Just TyBool

    , "(lambda x:Bool. x) true => Bool" ~:
      typeof1 (TmApp (TmAbs v_x TyBool t_x) TmTrue)
      ~?= Just TyBool

    , "(lambda x:X. x) true => Bool" ~:
      typeof1 (TmApp (TmAbs v_x ty_X t_x) TmTrue)
      ~?= Just TyBool

    , "lambda z:Z. lambda y:Y. z (y true) => (?X0 -> ?X1) -> ((Bool -> ?X0) -> ?X1)" ~:
      typeof1 (TmAbs v_z ty_Z
                     (TmAbs v_y ty_Y
                            (TmApp t_z (TmApp t_y TmTrue))))
      ~?= Just (TyArr (TyArr ty_X0 ty_X1)
                      (TyArr (TyArr TyBool ty_X0)
                             ty_X1))

    , "lambda x:X. if true then false else x false => (Bool -> Bool) -> Bool" ~:
      typeof1 (TmAbs v_x ty_X (TmIf TmTrue TmFalse (TmApp t_x TmFalse)))
      ~?= Just (TyArr (TyArr TyBool TyBool)
                      TyBool)
    ]

main = do
    runTestText (putTextToHandle stderr False) reconTests
    runTestText (putTextToHandle stderr False) compTests
    runTestText (putTextToHandle stderr False) unifyTests
    runTestText (putTextToHandle stderr False) applySubstTests
    runTestText (putTextToHandle stderr False) principalSolutionTests
    runTestText (putTextToHandle stderr False) typeof1Tests
