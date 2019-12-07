module NatTestLoopUnrolling

import public LoopUnrolling
import public NatTestEnv

%default total
%access public export

-- stmtLUStmtNatSgp : Maybe (s_lu : LUStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                           ** env_z : Env NatTestSyntax.testVs
--                           ** UnrollCPStmt (fst NatTestCPStmt.stmtCPStmt)
--                                           NatTestEnv.testEmptyEnv
--                                           s_lu
--                                           env_z)
-- stmtLUStmtNatSgp = unrollCPStmt (fst stmtCPStmt) testEmptyEnv

-- ifstmtLUStmtNatSgp : Maybe (s_lu : LUStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                             ** env_z : Env NatTestSyntax.testVs
--                             ** UnrollCPStmt (fst NatTestCPStmt.ifstmtCPStmtNatSgp)
--                                             NatTestEnv.testEmptyEnv
--                                             s_lu
--                                             env_z)
-- ifstmtLUStmtNatSgp = unrollCPStmt (fst ifstmtCPStmtNatSgp) testEmptyEnv

-- assnLUStmtNatSgp : Maybe (s_lu : LUStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                             ** env_z : Env NatTestSyntax.testVs
--                             ** UnrollCPStmt (fst NatTestCPStmt.assnCPStmtNatSgp)
--                                             NatTestEnv.testEmptyEnv
--                                             s_lu
--                                             env_z)
-- assnLUStmtNatSgp = unrollCPStmt (fst assnCPStmtNatSgp) testEmptyEnv

-- certLUStmtNatSgp : Maybe (s_lu : LUStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                             ** env_z : Env NatTestSyntax.testVs
--                             ** UnrollCPStmt (fst NatTestCPStmt.certCPStmtNatSgp)
--                                             NatTestEnv.testEmptyEnv
--                                             s_lu
--                                             env_z)
-- certLUStmtNatSgp = unrollCPStmt (fst certCPStmtNatSgp) testEmptyEnv

-- ordLUStmtNatSgp : Maybe (s_lu : LUStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
--                             ** env_z : Env NatTestSyntax.testVs
--                             ** UnrollCPStmt (fst NatTestCPStmt.ordCPStmtNatSgp)
--                                             NatTestEnv.testEmptyEnv
--                                             s_lu
--                                             env_z)
-- ordLUStmtNatSgp = unrollCPStmt (fst ordCPStmtNatSgp) testEmptyEnv

loopNatSgp : Stmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
loopNatSgp =
  Comp (Aryd Here 2 MkNotZero) $
  Iter Here Here Here 2 MkNotZero (Assn (There Here) (Val 5))

loopLUStmtNatSgp : Maybe (s_lu : LUStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
                          ** env_z : Env NatTestSyntax.testVs
                          ** UnrollCPStmt (fst (relStmtCPS NatTestLoopUnrolling.loopNatSgp))
                                          NatTestEnv.testEmptyEnv
                                          s_lu
                                          env_z)
loopLUStmtNatSgp = unrollCPStmt (fst (relStmtCPS NatTestLoopUnrolling.loopNatSgp)) testEmptyEnv

