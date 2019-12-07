module NatTestSemantics

import public Semantics
import public NatTestWellFormedness

%default total
%access public export

-- aSRAExp : (a : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs)
--        -> (a_wf : WFRAExp a NatTestEnv.testEnv)
--        -> (val ** SRAExp NatTestSyntax.sgpNat a NatTestEnv.testEnv a_wf NatTestEnv.testCtx val)
-- aSRAExp a a_wf = sraexp sgpNat a testEnv a_wf testCtx

-- valSRAExp : Maybe (a_r : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                    ** a_wf : WFRAExp a_r NatTestEnv.testEnv
--                    ** val : Nat
--                    ** SRAExp NatTestSyntax.sgpNat a_r NatTestEnv.testEnv a_wf NatTestEnv.testCtx val)
-- valSRAExp with (valWFRAExp)
--   | Nothing = Nothing
--   | Just (a_r ** (a_rfy, No a_nwf)) = Nothing
--   | Just (a_r ** (a_rfy, Yes a_wf)) = Just (a_r ** a_wf ** aSRAExp a_r a_wf)

-- varSRAExp : Maybe (a_r : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                    ** a_wf : WFRAExp a_r NatTestEnv.testEnv
--                    ** nf : Nat
--                    ** SRAExp NatTestSyntax.sgpNat a_r NatTestEnv.testEnv a_wf NatTestEnv.testCtx nf)
-- varSRAExp with (varWFRAExp)
--   | Nothing = Nothing
--   | Just (a_r ** (a_rfy, No a_nwf)) = Nothing
--   | Just (a_r ** (a_rfy, Yes a_wf)) = Just (a_r ** a_wf ** aSRAExp a_r a_wf)

-- accSRAExp : Maybe (a_r : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                    ** a_wf : WFRAExp a_r NatTestEnv.testEnv
--                    ** nf : Nat
--                    ** SRAExp NatTestSyntax.sgpNat a_r NatTestEnv.testEnv a_wf NatTestEnv.testCtx nf)
-- accSRAExp with (accWFRAExp)
--   | Nothing = Nothing
--   | Just (a_r ** (a_rfy, No a_nwf)) = Nothing
--   | Just (a_r ** (a_rfy, Yes a_wf)) = Just (a_r ** a_wf ** aSRAExp a_r a_wf)

-- addSRAExp : Maybe (a_r : RAExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                    ** a_wf : WFRAExp a_r NatTestEnv.testEnv
--                    ** nf : Nat
--                    ** SRAExp NatTestSyntax.sgpNat a_r NatTestEnv.testEnv a_wf NatTestEnv.testCtx nf)
-- addSRAExp with (addWFRAExp)
--   | Nothing = Nothing
--   | Just (a_r ** (a_rfy, No a_nwf)) = Nothing
--   | Just (a_r ** (a_rfy, Yes a_wf)) = Just (a_r ** a_wf ** aSRAExp a_r a_wf)

-- stmtSRStmtNatSgp : Maybe (s_r : RStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                           ** s_wf : WFRStmt s_r NatTestEnv.testEmptyEnv
--                           ** s_s : SRStmt NatTestSyntax.sgpNat s_r NatTestEnv.testEmptyEnv s_wf NatTestEnv.testEmptyCtx
--                           ** env_fin : Env NatTestSyntax.testVs
--                           ** Ctx Nat env_fin)
-- stmtSRStmtNatSgp with (stmtWFRStmt)
--   | Nothing = Nothing
--   | Just (s_r ** No s_nwf) = Nothing
--   | Just (s_r ** Yes s_wf) =
--     let s_s = srstmt sgpNat s_r testEmptyEnv s_wf testEmptyCtx
--     in Just (s_r ** s_wf ** s_s ** getFinalState s_s)

-- certSRStmtNatSgp : Maybe (s_r : RStmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
--                           ** s_wf : WFRStmt s_r NatTestEnv.testEmptyEnv
--                           ** s_s : SRStmt NatTestSyntax.sgpNat s_r NatTestEnv.testEmptyEnv s_wf NatTestEnv.testEmptyCtx
--                           ** env_fin : Env NatTestSyntax.testVs
--                           ** Ctx Nat env_fin)
-- certSRStmtNatSgp with (certWFRStmt)
--   | Nothing = Nothing
--   | Just (s_r ** No s_nwf) = Nothing
--   | Just (s_r ** Yes s_wf) =
--     let s_s = srstmt sgpNat s_r testEmptyEnv s_wf testEmptyCtx
--     in Just (s_r ** s_wf ** s_s ** getFinalState s_s)

-- ordSRStmtNatSgp : Maybe (s_r : RStmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
--                           ** s_wf : WFRStmt s_r NatTestEnv.testEmptyEnv
--                           ** s_s : SRStmt NatTestSyntax.ordNat s_r NatTestEnv.testEmptyEnv s_wf NatTestEnv.testEmptyCtx
--                           ** env_fin : Env NatTestSyntax.testVs
--                           ** Ctx Nat env_fin)
-- ordSRStmtNatSgp with (ordWFRStmt)
--   | Nothing = Nothing
--   | Just (s_r ** No s_nwf) = Nothing
--   | Just (s_r ** Yes s_wf) =
--     let s_s = srstmt ordNat s_r testEmptyEnv s_wf testEmptyCtx
--     in Just (s_r ** s_wf ** s_s ** getFinalState s_s)
