module CPStmt

import public Syntax

%default total
%access public export

data CPStmt : (c : Type) -> (cnst : Struct c set kind) -> (vs : VarSet ns is as fs) -> Type where
  Assn : (var : Elem NumVar ns)
      -> (a : AExp c cnst (MkVarSet ns is as fs))
      -> (s_k : CPStmt c cnst (MkVarSet ns is as fs))
      -> CPStmt c cnst (MkVarSet ns is as fs)
  Idxd : (var : Elem IdxVar is)
      -> (s_k : CPStmt c cnst (MkVarSet ns is as fs))
      -> CPStmt c cnst (MkVarSet ns is as fs)
  Idxi : (var : Elem IdxVar is)
      -> (s_k : CPStmt c cnst (MkVarSet ns is as fs))
      -> CPStmt c cnst (MkVarSet ns is as fs)
  Aryd : (var : Elem AryVar as)
      -> (len : Nat)
      -> (lenNZ : NotZero len)
      -> (s_k : CPStmt c cnst (MkVarSet ns is as fs))
      -> CPStmt c cnst (MkVarSet ns is as fs)
  Aryu : (var : Elem AryVar as)
      -> (len : Nat)
      -> (lenNZ : NotZero len)
      -> (idx : Elem IdxVar is)
      -> (a : AExp c cnst (MkVarSet ns is as fs))
      -> (s_k : CPStmt c cnst (MkVarSet ns is as fs))
      -> CPStmt c cnst (MkVarSet ns is as fs)
  Iftt : (b : BExp c cnst vs)
      -> (k_tt : CPStmt c cnst vs)
      -> (k_ff : CPStmt c cnst vs)
      -> CPStmt c cnst vs
  Iter : (var : Elem NumVar ns)
      -> (idx : Elem IdxVar is)
      -> (ary : Elem AryVar as)
      -> (len : Nat)
      -> (lenNZ : NotZero len)
      -> (s : CPStmt c cnst (MkVarSet ns is as fs))
      -> (s_k : CPStmt c cnst (MkVarSet ns is as fs))
      -> CPStmt c cnst (MkVarSet ns is as fs)
  Stop : CPStmt c cnst vs

  Cert : (b : BExp c cnst vs) -> (s_k : CPStmt c cnst vs) -> CPStmt c cnst vs

(++) : (s1 : CPStmt c cnst vs) -> (s2 : CPStmt c cnst vs) -> CPStmt c cnst vs
(++) (Assn var a s_k) s2 = Assn var a (s_k ++ s2)
(++) (Idxd var s_k) s2 = Idxd var (s_k ++ s2)
(++) (Idxi var s_k) s2 = Idxi var (s_k ++ s2)
(++) (Aryd var len lenNZ s_k) s2 = Aryd var len lenNZ (s_k ++ s2)
(++) (Aryu var len lenNZ idx a s_k) s2 = Aryu var len lenNZ idx a (s_k ++ s2)
(++) (Iftt b k_tt k_ff) s2 = Iftt b (k_tt ++ s2) (k_ff ++ s2)
(++) (Iter var idx ary len lenNZ s s_k) s2 = Iter var idx ary len lenNZ s (s_k ++ s2)
(++) Stop s2 = s2

(++) (Cert b s_k) s2 = Cert b (s_k ++ s2)

-- Assoc proof; s1 ++ Stop = s1; Stop ++ s2 = s2

namespace CPSRel
  data RelStmtCPS : (s : Stmt c cnst vs) -> (s_cps : CPStmt c cnst vs) -> Type where
    Assn : RelStmtCPS (Assn var a) (Assn var a Stop)
    Idxd : RelStmtCPS (Idxd var) (Idxd var Stop)
    Idxi : RelStmtCPS (Idxi var) (Idxi var Stop)
    Aryd : RelStmtCPS (Aryd var len lenNZ) (Aryd var len lenNZ Stop)
    Aryu : RelStmtCPS (Aryu var len lenNZ idx a) (Aryu var len lenNZ idx a Stop)
    Iftt : (tCPS : RelStmtCPS s_tt tt_cps)
        -> RelStmtCPS (Iftt b s_tt) (Iftt b tt_cps Stop)
    Iter : (sCPS : RelStmtCPS s s_cps)
        -> RelStmtCPS (Iter var idx ary len lenNZ s) (Iter var idx ary len lenNZ s_cps Stop)
    Comp : (s1CPS : RelStmtCPS s1 s1_cps)
        -> (s2CPS : RelStmtCPS s2 s2_cps)
        -> RelStmtCPS (Comp s1 s2) (s1_cps ++ s2_cps)

    Cert : RelStmtCPS (Cert b) (Cert b Stop)

relStmtCPS : (s : Stmt c cnst vs) -> (s_cps : CPStmt c cnst vs ** RelStmtCPS s s_cps)
relStmtCPS (Assn var a) = (Assn var a Stop ** Assn)
relStmtCPS (Idxd var) = (Idxd var Stop ** Idxd)
relStmtCPS (Idxi var) = (Idxi var Stop ** Idxi)
relStmtCPS (Aryd var len lenNZ) = (Aryd var len lenNZ Stop ** Aryd)
relStmtCPS (Aryu var len lenNZ idx a) = (Aryu var len lenNZ idx a Stop ** Aryu)
relStmtCPS (Iftt b s_tt) with (relStmtCPS s_tt)
  | (tt_cps ** ttCPS) = (Iftt b tt_cps Stop ** Iftt ttCPS)
relStmtCPS (Iter var idx ary len lenNZ s) with (relStmtCPS s)
  | (s_cps ** sCPS) = (Iter var idx ary len lenNZ s_cps Stop ** Iter sCPS)
relStmtCPS (Comp s1 s2) with (relStmtCPS s1, relStmtCPS s2)
  | ((s1_cps ** s1CPS), (s2_cps ** s2CPS)) = (s1_cps ++ s2_cps ** Comp s1CPS s2CPS)
-- relStmtCPS s = ?holeRelStmtCPS

relStmtCPS (Cert b) = (Cert b Stop ** Cert)