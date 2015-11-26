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

typeofTests = TestList
    [
      "項が変数のみからなり、その変数が型付け文脈に含まれる場合、その項は型付け文脈で対応付けられた型に型付けされる。" ~:
      typeof [(v_x, ty_X)] f t_x ~?= Right (ty_X, f, [])
    , "項が変数のみからなり、その変数が型付け文脈に含まれない場合、型付けが失敗する。" ~:
      typeof [] f t_x ~?= Left "error"

    , "項がzeroの場合、Nat型に型付けされる。" ~:
      typeof [] f TmZero ~?= Right (TyNat, f, [])

    , "項がsucc zeroの場合、Nat型に型付けされる。" ~:
      typeof [] f (TmSucc TmZero) ~?= Right (TyNat, f, [])
    , "項がsucc succ zeroの場合、Nat型に型付けされる。" ~:
      typeof [] f (TmSucc (TmSucc TmZero)) ~?= Right (TyNat, f, [])
    , "項がsucc trueの場合、型付けが失敗する。" ~:
      typeof [] f (TmSucc TmTrue) ~?= Left "error"
    , "項がsucc xで、xが型付け文脈でNatに型付けされている場合、Natに型付けされる。" ~:
      typeof [(v_x, TyNat)] f (TmSucc t_x) ~?= Right (TyNat, f, [])
    , "項がsucc xで、xが型付け文脈でBoolに型付けされている場合、型付けが失敗する。" ~:
      typeof [(v_x, TyBool)] f (TmSucc t_x) ~?= Left "error"
    , "項がsucc xで、xが型付け文脈に現れない場合、型付けが失敗する。" ~:
      typeof [(v_x, TyBool)] f (TmSucc t_x) ~?= Left "error"

    , "項がpred zeroの場合、Nat型に型付けされる。" ~:
      typeof [] f (TmPred TmZero) ~?= Right (TyNat, f, [])
    , "項がpred trueの場合、型付けが失敗する。" ~:
      typeof [] f (TmPred TmTrue) ~?= Left "error"

    , "項がiszero succ zeroの場合、型付けが失敗する。" ~:
      typeof [] f (TmIsZero (TmSucc TmZero)) ~?= Right (TyNat, f, [])
    , "項がiszero trueの場合、型付けが失敗する。" ~:
      typeof [] f (TmIsZero TmTrue) ~?= Left "error"

    , "項がtrueの場合、Bool型に型付けされる。" ~:
      typeof [] f TmTrue ~?= Right (TyBool, f, [])

    , "項がfalseの場合、Bool型に型付けされる。" ~:
      typeof [] f TmFalse ~?= Right (TyBool, f, [])

    , "lambda x:X. x => X -> X" ~:
      typeof [] f (TmAbs v_x ty_X t_x)
      ~?= Right (TyArr ty_X ty_X, f, [])

    , "lambda x:Bool. x => Bool -> Bool" ~:
      typeof [] f (TmAbs v_x TyBool t_x)
      ~?= Right (TyArr TyBool TyBool, f, [])

    , "lambda x:X. true => X -> Bool" ~:
      typeof [] f (TmAbs v_x ty_X TmTrue)
      ~?= Right (TyArr ty_X TyBool, f, [])

    , "(lambda x:Bool. x) true => Bool" ~:
      typeof [] f (TmApp (TmAbs v_x TyBool t_x) TmTrue)
      ~?= Right (TyBool, tail f, [(tv_X0, TyBool)])

    , "(lambda x:X. x) true => Bool" ~:
      typeof [] f (TmApp (TmAbs v_x ty_X t_x) TmTrue)
      ~?= Right (TyBool, tail f, [(tv_X, TyBool), (tv_X0, TyBool)])

    , "typeof lambda y:Y. y true => (Bool -> ?X0) -> ?X0" ~:
      typeof [] f (TmAbs v_y ty_Y (TmApp t_y TmTrue))
      ~?= Right (TyArr (TyArr TyBool ty_X0) ty_X0, tail f, [(tv_Y, TyArr TyBool ty_X0)])

    , "lambda z:Z. lambda y:Y. z (y true) => (?X0 -> ?X1) -> ((Bool -> ?X0) -> ?X1)" ~:
      typeof [] f (TmAbs v_z ty_Z
                         (TmAbs v_y ty_Y
                                (TmApp t_z (TmApp t_y TmTrue))))
      ~?= Right (TyArr (TyArr ty_X0 ty_X1)
                       (TyArr (TyArr TyBool ty_X0)
                              ty_X1),
                drop 2 f, [(tv_Y, TyArr TyBool ty_X0), (tv_Z, TyArr ty_X0 ty_X1)])

    , "lambda x:X. if true then false else x false => (Bool -> Bool) -> Bool" ~:
      typeof [] f (TmAbs v_x ty_X (TmIf TmTrue TmFalse (TmApp t_x TmFalse)))
      ~?= Right (TyArr (TyArr TyBool TyBool) TyBool, tail f,
                [(tv_X, TyArr TyBool TyBool), (tv_X0, TyBool)])
    ]

main = do
    runTestText (putTextToHandle stderr False) typeofTests
