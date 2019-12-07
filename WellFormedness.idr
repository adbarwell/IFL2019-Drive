module WellFormedness

import public Reification

%default total
%access public export

-- [Algebraic Expressions] ------------------------------------------------------------------------

||| Proof that all occurring variables in a have been declared (bound in the ground case),
||| and that all array accesses are not out-of-bounds.
data WFRAExp : (a : RAExp c cnst vs) -> (env : Env vs) -> Type where
  Val : WFRAExp (Val n) env
  Var : (varinenv : Elem var nums) -> WFRAExp (Var var) (MkEnv nums idxs arys funs)
  Acc : (lenNZ : NotZero len)
      -> (varinenv : Elem (var, (len ** lenNZ)) arys)
      -> (ubLTlen : LT ub len)
      -> WFRAExp (Acc var len ub) (MkEnv nums idxs arys funs)
  Neg : (a_wf : WFRAExp a env) -> WFRAExp (Neg a p) env
  Add : (a1_wf : WFRAExp a1 env) -> (a2_wf : WFRAExp a2 env) -> WFRAExp (Add a1 a2) env
  Mul : (a1_wf : WFRAExp a1 env) -> (a2_wf : WFRAExp a2 env) -> WFRAExp (Mul a1 a2 p) env

isWFRAExp : (a : RAExp c cnst vs) -> (env : Env vs) -> Dec (WFRAExp a env)
isWFRAExp (Val n) env = Yes Val
isWFRAExp (Var var) (MkEnv nums idxs arys funs) with (isElem var nums)
  | No varNInEnv = No (\(Var varinenv) => varNInEnv varinenv)
  | Yes varInEnv = Yes (Var varInEnv)
isWFRAExp (Acc var Z ub) env = No (\(Acc lenNZ varinenv ubLTlen) => absurd lenNZ)
isWFRAExp (Acc var (S l) ub) (MkEnv nums idxs arys funs)
  with (isElem (var, (S l ** MkNotZero)) arys)
    | No varNInEnv = No (\(Acc MkNotZero varinenv ubLTlen) => varNInEnv varinenv)
    | Yes varInEnv with (isLTE (S ub) (S l))
      | No ubGTElen = No (\(Acc MkNotZero varinenv ubLTlen) => ubGTElen ubLTlen)
      | Yes ubLTlen = Yes (Acc MkNotZero varInEnv ubLTlen)
isWFRAExp (Neg a p) env with (isWFRAExp a env)
  | No aNWF = No (\(Neg a_wf) => aNWF a_wf)
  | Yes aWF = Yes (Neg aWF)
isWFRAExp (Add a1 a2) env with (isWFRAExp a1 env)
  | No a1NWF = No (\(Add a1_wf a2_wf) => a1NWF a1_wf)
  | Yes a1WF with (isWFRAExp a2 env)
    | No a2NWF = No (\(Add a1_wf a2_wf) => a2NWF a2_wf)
    | Yes a2WF = Yes (Add a1WF a2WF)
isWFRAExp (Mul a1 a2 p) env with (isWFRAExp a1 env)
  | No a1NWF = No (\(Mul a1_wf a2_wf) => a1NWF a1_wf)
  | Yes a1WF with (isWFRAExp a2 env)
    | No a2NWF = No (\(Mul a1_wf a2_wf) => a2NWF a2_wf)
    | Yes a2WF = Yes (Mul a1WF a2WF)

-- [Boolean Expressions] --------------------------------------------------------------------------

||| Proof that all arithmetic subexpressions are well-formed.
data WFRBExp : (b : RBExp c cnst vs) -> (env : Env vs) -> Type where
  Eq : (a1_wf : WFRAExp a1 env) -> (a2_wf : WFRAExp a2 env) -> WFRBExp (Eq a1 a2) env
  LTE : (a1_wf : WFRAExp a1 env) -> (a2_wf : WFRAExp a2 env) -> WFRBExp (LTE a1 a2 ok) env

isWFRBExp : (b : RBExp c cnst vs) -> (env : Env vs) -> Dec (WFRBExp b env)
isWFRBExp (Eq a1 a2) env with (isWFRAExp a1 env)
  | No a1_nwf = No (\(Eq a1_wf a2_wf) => a1_nwf a1_wf)
  | Yes a1_wf with (isWFRAExp a2 env)
    | No a2_nwf = No (\(Eq a1_wf a2_wf) => a2_nwf a2_wf)
    | Yes a2_wf = Yes (Eq a1_wf a2_wf)
isWFRBExp (LTE a1 a2 ok) env with (isWFRAExp a1 env)
  | No a1_nwf = No (\(LTE a1_wf a2_wf) => a1_nwf a1_wf)
  | Yes a1_wf with (isWFRAExp a2 env)
    | No a2_nwf = No (\(LTE a1_wf a2_wf) => a2_nwf a2_wf)
    | Yes a2_wf = Yes (LTE a1_wf a2_wf)

-- [Statements] -----------------------------------------------------------------------------------

data WFRStmt : (s : RStmt c cnst vs) -> (env : Env vs) -> Type where
  Assn : (a_wf : WFRAExp a (MkEnv nums idxs arys funs))
      -> (k_wf : WFRStmt s_k (MkEnv (var :: nums) idxs arys funs))
      -> WFRStmt (Assn var a s_k) (MkEnv nums idxs arys funs)
  Idxd : (k_wf : WFRStmt s_k env) -> WFRStmt (Idxd s_k) env
  Idxi : (k_wf : WFRStmt s_k env) -> WFRStmt (Idxi s_k) env
  Aryd : (k_wf : WFRStmt s_k (MkEnv nums idxs ((var, (len ** lenNZ)) :: arys) funs))
      -> WFRStmt (Aryd var len lenNZ s_k) (MkEnv nums idxs arys funs)
  Aryu : (varinarys : Elem (var,(len ** lenNZ)) arys)
      -> (ubLTlen : LT ub len)
      -> (a_wf : WFRAExp a (MkEnv nums idxs arys funs))
      -> (k_wf : WFRStmt s_k (MkEnv nums idxs arys funs))
      -> WFRStmt (Aryu var len lenNZ ub a s_k) (MkEnv nums idxs arys funs)
  -- Iftt : WFRStmt (Iftt b s_tt k kNL) (MkEnv nums idxs arys funs)
  Stop : WFRStmt Stop env

  Cert : (b_wf : WFRBExp b env) -> (k_wf : WFRStmt s_k env) -> WFRStmt (Cert b s_k) env

isWFRStmt : (s : RStmt c cnst vs) -> (env : Env vs) -> Dec (WFRStmt s env)
isWFRStmt (Assn var a s_k) (MkEnv nums idxs arys funs) with (isWFRAExp a (MkEnv nums idxs arys funs))
  | No a_nwf = No (\(Assn a_wf k_wf) => a_nwf a_wf)
  | Yes a_wf with (isWFRStmt s_k (MkEnv (var :: nums) idxs arys funs))
    | No k_nwf = No (\(Assn a_wf k_wf) => k_nwf k_wf)
    | Yes k_wf = Yes (Assn a_wf k_wf)
isWFRStmt (Idxd s_k) env with (isWFRStmt s_k env)
  | No k_nwf = No (\(Idxd k_wf) => k_nwf k_wf)
  | Yes k_wf = Yes (Idxd k_wf)
isWFRStmt (Idxi s_k) env with (isWFRStmt s_k env)
  | No k_nwf = No (\(Idxi k_wf) => k_nwf k_wf)
  | Yes k_wf = Yes (Idxi k_wf)
isWFRStmt (Aryd var len lenNZ s_k) (MkEnv nums idxs arys funs)
  with (isWFRStmt s_k (MkEnv nums idxs ((var,(len ** lenNZ)) :: arys) funs))
    | No k_nwf = No (\(Aryd k_wf) => k_nwf k_wf)
    | Yes k_wf = Yes (Aryd k_wf)
isWFRStmt (Aryu var len lenNZ idx a s_k) (MkEnv nums idxs arys funs) 
  with (isWFRStmt s_k (MkEnv nums idxs arys funs))
    | No k_nwf = No (\(Aryu varinarys idxLTlen a_wf k_wf) => k_nwf k_wf)
    | Yes k_wf with (isWFRAExp a (MkEnv nums idxs arys funs))
      | No a_nwf = No (\(Aryu varinarys idxLTlen a_wf k_wf) => a_nwf a_wf)
      | Yes a_wf with (isLTE (S idx) len)
        | No idxGTElen = No (\(Aryu varinarys idxLTlen a_wf k_wf) => idxGTElen idxLTlen)
        | Yes idxLTlen with (isElem (var,(len ** lenNZ)) arys)
          | No varninarys = No (\(Aryu varinarys idxLTlen a_wf k_wf) => varninarys varinarys)
          | Yes varinarys = Yes (Aryu varinarys idxLTlen a_wf k_wf)
-- isWFRStmt s env = ?holeWFRStmt
isWFRStmt Stop env = Yes Stop

isWFRStmt (Cert b s_k) env with (isWFRStmt s_k env)
  | No k_nwf = No (\(Cert b_wf k_wf) => k_nwf k_wf)
  | Yes k_wf with (isWFRBExp b env)
    | No b_nwf = No (\(Cert b_wf k_wf) => b_nwf b_wf)
    | Yes b_wf = Yes (Cert b_wf k_wf)

{-
-- [Array Access Indices Are Not Out-of-Bounds] ---------------------------------------------------

namespace IB
  ||| Proof that all array accesses are within the bounds of the array that they are accessing,
  ||| given some context for index variable symbols.
  data IBAExp : (a : AExp c cnst vs)
             -> (env : Env vs)
             -> (bv : BVAExp a env)
             -> (idxCtx : IdxCtx env)
             -> Type where
    Var : IBAExp (Var var) (MkEnv nums' idxs' arys') (Var varinenv) ctx
    ||| .
    ||| @varinenv .
    ||| @idxinenv .
    Acc : (arridxlbub : ArrIdxBounds idxs' idxbounds idxinenv (lb,ub))
       -> (ubltlen : LT ub (S l))
       -> IBAExp (Acc var (S l) idx) (MkEnv nums' idxs' arys') (Acc varinenv idxinenv) (MkIdxCtx idxbounds)

  ubGTELen : (lbubArr : ArrIdxBounds idxs' lbubs idxinenv (lb, ub))
          -> (ubGTElen : Not (LT ub (S l)))
          -> IBAExp (Acc var (S l) idx) (MkEnv nums' idxs' arys') (Acc varinenv idxinenv) (MkIdxCtx lbubs) -> Void
  ubGTELen lbubArr ubGTElen (Acc arridxlbub ubltlen)
    with (lemma_same_lbub_two_ArrIdxBounds lbubArr arridxlbub)
      ubGTELen arridxlbub ubGTElen (Acc arridxlbub ubltlen) | Refl = ubGTElen ubltlen

  isIBAExp : (a : AExp c cnst vs)
          -> (env : Env vs)
          -> (bv : BVAExp a env)
          -> (idxCtx : IdxCtx env)
          -> Dec (IBAExp a env bv idxCtx)
  isIBAExp (Var var) (MkEnv nums' idxs' arys') (Var varinenv) idxCtx = Yes Var
  isIBAExp (Acc var (S l) idx) (MkEnv nums' idxs' arys') (Acc varinenv idxinenv) (MkIdxCtx lbubs)
    with (arrIdxBounds idxs' lbubs idxinenv)
      | ((lb,ub) ** lbubArr) =
        case (isLTE (S ub) (S l)) of
          Yes ubLTlen => Yes (Acc lbubArr ubLTlen)
          No ubGTElen => No (ubGTELen lbubArr ubGTElen)

-- [Well-Formedness] ------------------------------------------------------------------------------

||| Proof of well-formedness for arithmetic expressions,
||| given some environment and index variable symbol context.
data WFAExp : (a : AExp c cnst vs) -> (env : Env vs) -> (idxCtx : IdxCtx env) -> Type where
  MkWFAExp : (bv : BVAExp a env) -> (ib : IBAExp a env bv idxCtx) -> WFAExp a env idxCtx

lemma_same_a_env_two_BVAExp : (bv1 : BVAExp a env)
                           -> (bv2 : BVAExp a env)
                           -> (bv1 = bv2)
lemma_same_a_env_two_BVAExp (Var varinenv) (Var varinenv) = Refl
lemma_same_a_env_two_BVAExp (Acc varinenv idxinenv) (Acc varinenv' idxinenv') = ?holeAcc

isWFAExp : (a : AExp c cnst vs)
        -> (env : Env vs)
        -> (idxCtx : IdxCtx env)
        -> Dec (WFAExp a env idxCtx)
isWFAExp a env idxCtx with (isBVAExp a env)
  | No nbv = No (\(MkWFAExp bv ib) => nbv bv)
  | Yes bv with (isIBAExp a env bv idxCtx)
    | No nib = No ?holeNo
    | Yes ib = Yes (MkWFAExp bv ib)
-}

