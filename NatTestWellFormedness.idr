module NatTestWellFormednesss

import public WellFormedness
import public NatTestReification

%default total
%access public export

-- aWFRAExp : (a : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs)
--         -> Dec (WFRAExp a NatTestEnv.testEnv)
-- aWFRAExp a = isWFRAExp a testEnv

-- valWFRAExp : Maybe (a_r : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                     ** (ReifyIdxAExp NatTestSyntax.valAExpNatSgp NatTestEnv.testEnv NatTestEnv.testIdxCtx a_r,
--                         Dec (WFRAExp a_r NatTestEnv.testEnv)))
-- valWFRAExp with (valReifyNatSgp)
--   | No contra = Nothing
--   | Yes (a_r ** prf) = Just (a_r ** (prf,aWFRAExp a_r))

-- varWFRAExp : Maybe (a_r : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                     ** (ReifyIdxAExp NatTestSyntax.varAExpNatSgp NatTestEnv.testEnv NatTestEnv.testIdxCtx a_r,
--                         Dec (WFRAExp a_r NatTestEnv.testEnv)))
-- varWFRAExp with (varReifyNatSgp)
--   | No contra = Nothing
--   | Yes (a_r ** prf) = Just (a_r ** (prf,aWFRAExp a_r))

-- accWFRAExp : Maybe (a_r : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                     ** (ReifyIdxAExp NatTestSyntax.accAExpNatSgp NatTestEnv.testEnv NatTestEnv.testIdxCtx a_r,
--                         Dec (WFRAExp a_r NatTestEnv.testEnv)))
-- accWFRAExp with (accReifyNatSgp)
--   | No contra = Nothing
--   | Yes (a_r ** prf) = Just (a_r ** (prf,aWFRAExp a_r))

-- addWFRAExp : Maybe (a_r : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                     ** (ReifyIdxAExp NatTestSyntax.addAExpNatSgp NatTestEnv.testEnv NatTestEnv.testIdxCtx a_r,
--                         Dec (WFRAExp a_r NatTestEnv.testEnv)))
-- addWFRAExp with (addReifyNatSgp)
--   | No contra = Nothing
--   | Yes (a_r ** prf) = Just (a_r ** (prf,aWFRAExp a_r))


-- stmtWFRStmt : Maybe (s_r : RStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                      ** Dec (WFRStmt s_r NatTestEnv.testEmptyEnv))
-- stmtWFRStmt with (stmtReifyNatSgp)
--   | Nothing = Nothing
--   | Just (s_lu ** s_r ** prf) = Just (s_r ** isWFRStmt s_r testEmptyEnv)

-- certWFRStmt : Maybe (s_r : RStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                      ** Dec (WFRStmt s_r NatTestEnv.testEmptyEnv))
-- certWFRStmt with (certReifyNatSgp)
--   | Nothing = Nothing
--   | Just (s_lu ** s_r ** prf) = Just (s_r ** isWFRStmt s_r testEmptyEnv)

-- ordWFRStmt : Maybe (s_r : RStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
--                      ** Dec (WFRStmt s_r NatTestEnv.testEmptyEnv))
-- ordWFRStmt with (ordReifyNatSgp)
--   | Nothing = Nothing
--   | Just (s_lu ** s_r ** prf) = Just (s_r ** isWFRStmt s_r testEmptyEnv)
