module NatTestVerifCert

import public VerifCert
import public NatTestSemantics

%default total
%access public export

-- certVCRStmtNatSgp : Maybe (s_r : RStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                           ** s_wf : WFRStmt s_r NatTestEnv.testEmptyEnv
--                           ** s_s : SRStmt NatTestSyntax.sgpNat s_r NatTestEnv.testEmptyEnv s_wf NatTestEnv.testEmptyCtx
--                           ** VCRStmt NatTestSyntax.sgpNat s_r NatTestEnv.testEmptyEnv s_wf NatTestEnv.testEmptyCtx s_s)
-- certVCRStmtNatSgp with (certWFRStmt)
--   | Nothing = Nothing
--   | Just (s_r ** No s_nwf) = Nothing
--   | Just (s_r ** Yes s_wf) =
--     let s_s = srstmt sgpNat s_r testEmptyEnv s_wf testEmptyCtx
--     in Just (s_r ** s_wf ** s_s ** vcrstmt sgpNat s_r testEmptyEnv s_wf testEmptyCtx s_s)

-- ordVCRStmtNatSgp : Maybe (s_r : RStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
--                           ** s_wf : WFRStmt s_r NatTestEnv.testEmptyEnv
--                           ** s_s : SRStmt NatTestSyntax.ordNat s_r NatTestEnv.testEmptyEnv s_wf NatTestEnv.testEmptyCtx
--                           ** VCRStmt NatTestSyntax.ordNat s_r NatTestEnv.testEmptyEnv s_wf NatTestEnv.testEmptyCtx s_s)
-- ordVCRStmtNatSgp with (ordWFRStmt)
--   | Nothing = Nothing
--   | Just (s_r ** No s_nwf) = Nothing
--   | Just (s_r ** Yes s_wf) =
--     let s_s = srstmt ordNat s_r testEmptyEnv s_wf testEmptyCtx
--     in Just (s_r ** s_wf ** s_s ** vcrstmt ordNat s_r testEmptyEnv s_wf testEmptyCtx s_s)

{-
  Assume that we are given a list in the environment/context.

  x_1 := 0;
  x_3 := 7; -- memory (a count of all array cells, and numeric and index variables); from cap. ann
  for x_2 in a^5 do
    x_1 := x_2 + x_1

  csl_assert (x_1 = 15)
  csl_assert (x_3 < 10)
-}

-- wait, the way we only add things to the environment means that x_2 will still be declared and 
-- assigned to the final value of a^5.... eh, it's a feature

testListEnv : Env NatTestSyntax.testVs
testListEnv = MkEnv [] [] [(Here,(5 ** MkNotZero))] []

testListIdxCtx : IdxCtx NatTestSyntax.testVs NatTestVerifCert.testListEnv
testListIdxCtx = MkIdxCtx []

testListCtx : Ctx Nat NatTestVerifCert.testListEnv
testListCtx = MkCtx [] [(5 ** [1,2,3,4,5])] (Cons Refl Nil)

loopBody : Stmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
loopBody = Assn Here (Add (Var Here) (Var (There Here)))

sumListNatOSg : Stmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
sumListNatOSg = 
  Comp (Assn Here (Val 0)) $
  Comp (Assn (There (There Here)) (Val 7)) $
  Comp (Iter (There Here) Here Here 5 MkNotZero loopBody) $
  Comp (Cert (Eq (Var Here) (Val 15))) $
  Cert (LTE (Var (There (There Here))) (Val 10) OrdSemigroup)

-- sumListVCRStmtNatOSg : Maybe (s_r : RStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
--                               ** s_wf : WFRStmt s_r NatTestVerifCert.testListEnv
--                               ** s_s : SRStmt NatTestSyntax.ordNat s_r NatTestVerifCert.testListEnv s_wf NatTestVerifCert.testListCtx
--                               ** VCRStmt NatTestSyntax.ordNat s_r NatTestVerifCert.testListEnv s_wf NatTestVerifCert.testListCtx s_s)
-- sumListVCRStmtNatOSg with (unrollCPStmt (fst (relStmtCPS sumListNatOSg)) testListEnv)
--   | Nothing = Nothing
--   | Just (s_lu ** env_z ** sLU) with (reifyIdxStmt testVs s_lu testListEnv testListIdxCtx)
--     | Nothing = Nothing
--     | Just (s_r ** sRI) with (isWFRStmt s_r testListEnv)
--       | No s_nwf = Nothing
--       | Yes s_wf =
--         let s_s = srstmt ordNat s_r testListEnv s_wf testListCtx
--         in Just (s_r ** s_wf ** s_s ** vcrstmt ordNat s_r testListEnv s_wf testListCtx s_s)

sumListCPStmtNatOSg : (s_cps : CPStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
                       ** RelStmtCPS NatTestVerifCert.sumListNatOSg s_cps)
sumListCPStmtNatOSg = relStmtCPS sumListNatOSg

sumListLUStmtNatOSg : Maybe (s_lu : LUStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
                            ** env_z : Env NatTestSyntax.testVs
                            ** UnrollCPStmt (fst NatTestVerifCert.sumListCPStmtNatOSg)
                                            NatTestVerifCert.testListEnv
                                            s_lu
                                            env_z)
sumListLUStmtNatOSg = unrollCPStmt (fst sumListCPStmtNatOSg) testListEnv

sumListReifyNatOSg : Maybe (s_lu : LUStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
                         ** s_r : RStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
                         ** ReifyIdxStmt s_lu NatTestVerifCert.testListEnv NatTestVerifCert.testListIdxCtx s_r)
sumListReifyNatOSg with (sumListLUStmtNatOSg)
  | Nothing = Nothing
  | Just (s_lu ** env_z ** sLU) with (reifyIdxStmt testVs s_lu testListEnv testListIdxCtx)
    | Nothing = Nothing
    | Just (s_r ** sRI) = Just (s_lu ** s_r ** sRI)

sumListWFRStmtNatOSg : Maybe (s_r : RStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
    ** Dec (WFRStmt s_r NatTestVerifCert.testListEnv))
sumListWFRStmtNatOSg with (sumListReifyNatOSg)
  | Nothing = Nothing
  | Just (s_lu ** s_r ** prf) = Just (s_r ** isWFRStmt s_r testListEnv)

sumListSRStmtNatOSg : Maybe (s_r : RStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
                          ** s_wf : WFRStmt s_r NatTestVerifCert.testListEnv
                          ** s_s : SRStmt NatTestSyntax.ordNat s_r NatTestVerifCert.testListEnv s_wf NatTestVerifCert.testListCtx
                          ** env_fin : Env NatTestSyntax.testVs
                          ** Ctx Nat env_fin)
sumListSRStmtNatOSg with (sumListWFRStmtNatOSg)
  | Nothing = Nothing
  | Just (s_r ** No s_nwf) = Nothing
  | Just (s_r ** Yes s_wf) =
    let s_s = srstmt ordNat s_r testListEnv s_wf testListCtx
    in Just (s_r ** s_wf ** s_s ** getFinalState s_s)

sumListVCRStmtNatOSg : Maybe (s_r : RStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
                              ** s_wf : WFRStmt s_r NatTestVerifCert.testListEnv
                              ** s_s : SRStmt NatTestSyntax.ordNat s_r NatTestVerifCert.testListEnv s_wf NatTestVerifCert.testListCtx
                              ** VCRStmt NatTestSyntax.ordNat s_r NatTestVerifCert.testListEnv s_wf NatTestVerifCert.testListCtx s_s)
sumListVCRStmtNatOSg with (sumListWFRStmtNatOSg)
  | Nothing = Nothing
  | Just (s_r ** No s_nwf) = Nothing
  | Just (s_r ** Yes s_wf) =
    let s_s = srstmt ordNat s_r testListEnv s_wf testListCtx
    in Just (s_r ** s_wf ** s_s ** vcrstmt ordNat s_r testListEnv s_wf testListCtx s_s)
