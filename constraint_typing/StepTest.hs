import Test.HUnit
import System.IO
import ConstraintTyping
import Step

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

stepTests = TestList
    [
      "項が変数のみからなり、その変数が型付け文脈に含まれる場合、その項は型付け文脈で対応付けられた型に型付けされる。" ~:
      step [(v_x, ty_X)] f t_x ~?= Just (ty_X, f, [])
    , "項が変数のみからなり、その変数が型付け文脈に含まれない場合、型付けが失敗する。" ~:
      step [] f t_x ~?= Nothing

    , "項がzeroの場合、Nat型に型付けされる。" ~:
      step [] f TmZero ~?= Just (TyNat, f, [])

    , "項がsucc zeroの場合、Nat型に型付けされる。" ~:
      step [] f (TmSucc TmZero) ~?= Just (TyNat, f, [])
    , "項がsucc succ zeroの場合、Nat型に型付けされる。" ~:
      step [] f (TmSucc (TmSucc TmZero)) ~?= Just (TyNat, f, [])
    , "項がsucc trueの場合、型付けが失敗する。" ~:
      step [] f (TmSucc TmTrue) ~?= Nothing
    , "項がsucc xで、xが型付け文脈でNatに型付けされている場合、Natに型付けされる。" ~:
      step [(v_x, TyNat)] f (TmSucc t_x) ~?= Just (TyNat, f, [])
    , "項がsucc xで、xが型付け文脈でBoolに型付けされている場合、型付けが失敗する。" ~:
      step [(v_x, TyBool)] f (TmSucc t_x) ~?= Nothing
    , "項がsucc xで、xが型付け文脈に現れない場合、型付けが失敗する。" ~:
      step [(v_x, TyBool)] f (TmSucc t_x) ~?= Nothing

    , "項がpred zeroの場合、Nat型に型付けされる。" ~:
      step [] f (TmPred TmZero) ~?= Just (TyNat, f, [])
    , "項がpred trueの場合、型付けが失敗する。" ~:
      step [] f (TmPred TmTrue) ~?= Nothing

    , "項がiszero succ zeroの場合、型付けが失敗する。" ~:
      step [] f (TmIsZero (TmSucc TmZero)) ~?= Just (TyNat, f, [])
    , "項がiszero trueの場合、型付けが失敗する。" ~:
      step [] f (TmIsZero TmTrue) ~?= Nothing

    , "項がtrueの場合、Bool型に型付けされる。" ~:
      step [] f TmTrue ~?= Just (TyBool, f, [])

    , "項がfalseの場合、Bool型に型付けされる。" ~:
      step [] f TmFalse ~?= Just (TyBool, f, [])

    , "lambda x:X. x => X -> X" ~:
      step [] f (TmAbs v_x ty_X t_x)
      ~?= Just (TyArr ty_X ty_X, f, [])

    , "lambda x:Bool. x => Bool -> Bool" ~:
      step [] f (TmAbs v_x TyBool t_x)
      ~?= Just (TyArr TyBool TyBool, f, [])

    , "lambda x:X. true => X -> Bool" ~:
      step [] f (TmAbs v_x ty_X TmTrue)
      ~?= Just (TyArr ty_X TyBool, f, [])

    , "(lambda x:Bool. x) true => Bool" ~:
      step [] f (TmApp (TmAbs v_x TyBool t_x) TmTrue)
      ~?= Just (TyBool, tail f, [(tv_X0, TyBool)])

    , "(lambda x:X. x) true => Bool" ~:
      step [] f (TmApp (TmAbs v_x ty_X t_x) TmTrue)
      ~?= Just (TyBool, tail f, [(tv_X, TyBool), (tv_X0, TyBool)])

    , "step lambda y:Y. y true => (Bool -> ?X0) -> ?X0" ~:
      step [] f (TmAbs v_y ty_Y (TmApp t_y TmTrue))
      ~?= Just (TyArr (TyArr TyBool ty_X0) ty_X0, tail f, [(tv_Y, TyArr TyBool ty_X0)])

    , "lambda z:Z. lambda y:Y. z (y true) => (?X0 -> ?X1) -> ((Bool -> ?X0) -> ?X1)" ~:
      step [] f (TmAbs v_z ty_Z
                       (TmAbs v_y ty_Y
                              (TmApp t_z (TmApp t_y TmTrue))))
      ~?= Just (TyArr (TyArr ty_X0 ty_X1)
                      (TyArr (TyArr TyBool ty_X0)
                             ty_X1),
                drop 2 f, [(tv_Y, TyArr TyBool ty_X0), (tv_Z, TyArr ty_X0 ty_X1)])

    , "lambda x:X. if true then false else x false => (Bool -> Bool) -> Bool" ~:
      step [] f (TmAbs v_x ty_X (TmIf TmTrue TmFalse (TmApp t_x TmFalse)))
      ~?= Just (TyArr (TyArr TyBool TyBool) TyBool, tail f,
                [(tv_X, TyArr TyBool TyBool), (tv_X0, TyBool)])
    ]

main = do
    runTestText (putTextToHandle stderr False) stepTests
