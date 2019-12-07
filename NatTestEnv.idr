module NatTestEnv

import public EnvCtxUtil
import public NatTestCPStmt

%default total
%access public export

testEnv : Env NatTestSyntax.testVs
testEnv =
  let nums' = [There Here]
      idxs' = [Here]
      arys' = [ (Here, (1 ** MkNotZero))
              , (Here, (3 ** MkNotZero))
              , (There Here, (5 ** MkNotZero))]
  in MkEnv nums' idxs' arys' []

testEmptyEnv : Env NatTestSyntax.testVs
testEmptyEnv = MkEnv [] [] [] []

testIdxCtx : IdxCtx NatTestSyntax.testVs NatTestEnv.testEnv
testIdxCtx = MkIdxCtx [4]

testEmptyIdxCtx : IdxCtx NatTestSyntax.testVs NatTestEnv.testEmptyEnv
testEmptyIdxCtx = MkIdxCtx []

testAVals : Vect 3 (l : Nat ** Vect l Nat)
testAVals = [(1 ** [1]),(3 ** [2,3,4]),(5 ** [5,6,7,8,9])]

testAValsStructSame : StructSame {as=[AryVar, AryVar]} [(Here, (1 ** MkNotZero)), (Here, (3 ** MkNotZero)), (There Here, (5 ** MkNotZero))] NatTestEnv.testAVals
testAValsStructSame = Cons Refl $ Cons Refl $ Cons Refl $ Nil

testCtx : Ctx Nat NatTestEnv.testEnv
testCtx = MkCtx [5] testAVals testAValsStructSame

testEmptyCtx : Ctx Nat NatTestEnv.testEmptyEnv
testEmptyCtx = MkCtx [] [] Nil
