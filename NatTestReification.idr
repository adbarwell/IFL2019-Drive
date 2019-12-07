module NatTestReification

import public Reification
import public NatTestLoopUnrolling

%default total
%access public export

-- valReifyNatSgp : Dec (a_r : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                       ** ReifyIdxAExp NatTestSyntax.valAExpNatSgp NatTestEnv.testEnv NatTestEnv.testIdxCtx a_r)
-- valReifyNatSgp = reifyIdxAExp valAExpNatSgp testEnv testIdxCtx
-- varReifyNatSgp : Dec (a_r : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                       ** ReifyIdxAExp NatTestSyntax.varAExpNatSgp NatTestEnv.testEnv NatTestEnv.testIdxCtx a_r)
-- varReifyNatSgp = reifyIdxAExp varAExpNatSgp testEnv testIdxCtx
-- accReifyNatSgp : Dec (a_r : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                       ** ReifyIdxAExp NatTestSyntax.accAExpNatSgp NatTestEnv.testEnv NatTestEnv.testIdxCtx a_r)
-- accReifyNatSgp = reifyIdxAExp accAExpNatSgp testEnv testIdxCtx
-- addReifyNatSgp : Dec (a_r : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                       ** ReifyIdxAExp NatTestSyntax.addAExpNatSgp NatTestEnv.testEnv NatTestEnv.testIdxCtx a_r)
-- addReifyNatSgp = reifyIdxAExp addAExpNatSgp testEnv testIdxCtx

-- stmtReifyNatSgp : Maybe (s_lu : LUStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                          ** s_r : RStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                          ** ReifyIdxStmt s_lu NatTestEnv.testEmptyEnv NatTestEnv.testEmptyIdxCtx s_r)
-- stmtReifyNatSgp with (stmtLUStmtNatSgp)
--   | Nothing = Nothing
--   | Just (s_lu ** env_z ** sLU) with (reifyIdxStmt testVs s_lu testEmptyEnv testEmptyIdxCtx)
--     | Nothing = Nothing
--     | Just (s_r ** sRI) = Just (s_lu ** s_r ** sRI)

-- ifstmtReifyNatSgp : Maybe (s_lu : LUStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                             ** s_r : RStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                             ** ReifyIdxStmt s_lu NatTestEnv.testEmptyEnv NatTestEnv.testEmptyIdxCtx s_r)
-- ifstmtReifyNatSgp with (ifstmtLUStmtNatSgp)
--   | Nothing = Nothing
--   | Just (s_lu ** env_z ** sLU) with (reifyIdxStmt testVs s_lu testEmptyEnv testEmptyIdxCtx)
--     | Nothing = Nothing
--     | Just (s_r ** sRI) = Just (s_lu ** s_r ** sRI)

-- certReifyNatSgp : Maybe (s_lu : LUStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                          ** s_r : RStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                          ** ReifyIdxStmt s_lu NatTestEnv.testEmptyEnv NatTestEnv.testEmptyIdxCtx s_r)
-- certReifyNatSgp with (certLUStmtNatSgp)
--   | Nothing = Nothing
--   | Just (s_lu ** env_z ** sLU) with (reifyIdxStmt testVs s_lu testEmptyEnv testEmptyIdxCtx)
--     | Nothing = Nothing
--     | Just (s_r ** sRI) = Just (s_lu ** s_r ** sRI)

-- ordReifyNatSgp : Maybe (s_lu : LUStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
--                          ** s_r : RStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
--                          ** ReifyIdxStmt s_lu NatTestEnv.testEmptyEnv NatTestEnv.testEmptyIdxCtx s_r)
-- ordReifyNatSgp with (ordLUStmtNatSgp)
--   | Nothing = Nothing
--   | Just (s_lu ** env_z ** sLU) with (reifyIdxStmt testVs s_lu testEmptyEnv testEmptyIdxCtx)
--     | Nothing = Nothing
--     | Just (s_r ** sRI) = Just (s_lu ** s_r ** sRI)

loopReifyNatSgp : Maybe (s_lu : LUStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
                         ** s_r : RStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
                         ** ReifyIdxStmt s_lu NatTestEnv.testEmptyEnv NatTestEnv.testEmptyIdxCtx s_r)
loopReifyNatSgp with (loopLUStmtNatSgp)
  | Nothing = Nothing
  | Just (s_lu ** env_z ** sLU) with (reifyIdxStmt testVs s_lu testEmptyEnv testEmptyIdxCtx)
    | Nothing = Nothing
    | Just (s_r ** sRI) = Just (s_lu ** s_r ** sRI)

