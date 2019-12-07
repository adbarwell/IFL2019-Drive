module NatTestCPStmt

import public CPStmt
import public NatTestSyntax

%default total
%access public export

-- stmtCPStmt : (s_cps : CPStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--               ** RelStmtCPS NatTestSyntax.stmtNatSgp s_cps)
-- stmtCPStmt = relStmtCPS stmtNatSgp

-- ifstmtCPStmtNatSgp : (s_cps : CPStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                       ** RelStmtCPS NatTestSyntax.ifstmtNatSgp s_cps)
-- ifstmtCPStmtNatSgp = relStmtCPS ifstmtNatSgp

-- assnCPStmtNatSgp : (s_cps : CPStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                     ** RelStmtCPS NatTestSyntax.assnNatSgp s_cps)
-- assnCPStmtNatSgp = relStmtCPS assnNatSgp

-- certCPStmtNatSgp : (s_cps : CPStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                     ** RelStmtCPS NatTestSyntax.certNatSgp s_cps)
-- certCPStmtNatSgp = relStmtCPS certNatSgp

-- ordCPStmtNatSgp : (s_cps : CPStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
--                     ** RelStmtCPS NatTestSyntax.ordNatSgp s_cps)
-- ordCPStmtNatSgp = relStmtCPS ordNatSgp
