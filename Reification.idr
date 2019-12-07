module Reification

import public LoopUnrolling

%default total
%access public export

-- [Reification – Syntax] -------------------------------------------------------------------------

||| Only differs from AExp in the Acc case.
|||
||| Literals allow us to avoid the proof obligation of (bv = bv1) in the case
||| `isWFAExp a env ctx | Yes bv | No nib = No (contra bv nib)`, where
||| `lemma_same_a_env_two_BVAExp (Acc varinenv idxinenv) (Acc varinenv' idxinenv')` s.t.
|||  both `(varinenv = varinenv')` and `(idxinenv = idxinenv')` do not necessarily hold.
||| I.e. we are back to our old problem that two proofs of vector inclusion (Elem) for the same 
||| indices does *not* imply that those two proofs are the same.
data RAExp : (c : Type) -> (cnst : Struct c set kind)
          -> (vs : VarSet ns is as fs) -> Type where
  Val : (n : c) -> RAExp c cnst vs
  Var : {vs : VarSet ns is as fs}
     -> (var : Elem NumVar ns) -> RAExp c cnst vs
  Acc : {vs : VarSet ns is as fs}
     -> (var : Elem AryVar as) -> (len : Nat) -> (idx : Nat) -> RAExp c cnst vs
  Neg : {cnst : Struct c set kind}
     -> (a : RAExp c cnst vs) -> (ok : GT kind Monoid) -> RAExp c cnst vs
  Add : (a1 : RAExp c cnst vs) -> (a2 : RAExp c cnst vs) -> RAExp c cnst vs
  Mul : {cnst : Struct c set kind}
     -> (a1 : RAExp c cnst vs) -> (a2 : RAExp c cnst vs) -> (ok : GT kind AbelianGroup)
     -> RAExp c cnst vs

||| Only differs from BExp in that the arguments to `Eq` are themselves reified.
data RBExp : (c : Type) -> (cnst : Struct c set kind)
          -> (vs : VarSet ns is as fs) -> Type where
  Eq : (a1 : RAExp c cnst vs) -> (a2 : RAExp c cnst vs) -> RBExp c cnst vs
  LTE : {cnst : Struct c set kind}
     -> (a1 : RAExp c cnst vs)
     -> (a2 : RAExp c cnst vs)
     -> (ok : HasOrdering kind)
     -> RBExp c cnst vs

mutual
  data RStmt : (c : Type) -> (cnst : Struct c set kind) -> (vs : VarSet ns is as fs) -> Type where
    Assn : (var : Elem NumVar ns)
        -> (a : RAExp c cnst (MkVarSet ns is as fs))
        -> (s_k : RStmt c cnst (MkVarSet ns is as fs))
        -> RStmt c cnst (MkVarSet ns is as fs)
    Idxd : (s_k : RStmt c cnst (MkVarSet ns is as fs))
        -> RStmt c cnst (MkVarSet ns is as fs)
    Idxi : (s_k : RStmt c cnst (MkVarSet ns is as fs))
        -> RStmt c cnst (MkVarSet ns is as fs)
    Aryd : (var : Elem AryVar as)
        -> (len : Nat)
        -> (lenNZ : NotZero len)
        -> (s_k : RStmt c cnst (MkVarSet ns is as fs))
        -> RStmt c cnst (MkVarSet ns is as fs)
    Aryu : (var : Elem AryVar as)
        -> (len : Nat)
        -> (lenNZ : NotZero len)
        -> (idx : Nat)
        -> (a : RAExp c cnst (MkVarSet ns is as fs))
        -> (s_k : RStmt c cnst (MkVarSet ns is as fs))
        -> RStmt c cnst (MkVarSet ns is as fs)
    -- Iftt : (b : RBExp c cnst vs)
    --     -> (s_tt : RStmt c cnst vs)
    --     -> (k : KTree c cnst vs)
    --     -> (kNL : NotLeaf k)
    --     -> RStmt c cnst vs
    Stop : RStmt c cnst vs

    Cert : (b : RBExp c cnst vs) -> (s_k : RStmt c cnst vs) -> RStmt c cnst vs
  
-- [Reification – Relations] ----------------------------------------------------------------------

namespace RRel
  ||| Relates an arithmetic expression provided by the programmer
  ||| with an equivalent reified arithmetic expression, given a context.
  data ReifyIdxAExp : (a : AExp c cnst vs)
                   -> (env : Env vs)
                   -> (idxCtx : IdxCtx vs env)
                   -> (a_r : RAExp c cnst vs)
                   -> Type where
    Val : ReifyIdxAExp (Val n) env idxCtx (Val n)
    Var : ReifyIdxAExp (Var var) env idxCtx (Var var)
    Acc : (idxisdecld : Elem idx idxs)
       -> (arridxub : ArrIdxBounds idxs ubs idxisdecld ub)
       -> ReifyIdxAExp (Acc var len idx) (MkEnv nums idxs arys funs) (MkIdxCtx ubs) (Acc var len ub)
    Neg : (aRI : ReifyIdxAExp a env idxCtx a_r) -> ReifyIdxAExp (Neg a p) env idxCtx (Neg a_r p)
    Add : (a1RI : ReifyIdxAExp a1 env idxCtx a1_r)
       -> (a2RI : ReifyIdxAExp a2 env idxCtx a2_r)
       -> ReifyIdxAExp (Add a1 a2) env idxCtx (Add a1_r a2_r)
    Mul : (a1RI : ReifyIdxAExp a1 env idxCtx a1_r)
       -> (a2RI : ReifyIdxAExp a2 env idxCtx a2_r)
       -> ReifyIdxAExp (Mul a1 a2 p) env idxCtx (Mul a1_r a2_r p)
  
  data ReifyIdxBExp : (b : BExp c cnst vs)
                   -> (env : Env vs)
                   -> (idxCtx : IdxCtx vs env)
                   -> (b_r : RBExp c cnst vs)
                   -> Type where
    Eq : (a1RI : ReifyIdxAExp a1 env idxCtx a1_r)
      -> (a2RI : ReifyIdxAExp a2 env idxCtx a2_r)
      -> ReifyIdxBExp (Eq a1 a2) env idxCtx (Eq a1_r a2_r)
    LTE : (a1RI : ReifyIdxAExp a1 env idxCtx a1_r)
       -> (a2RI : ReifyIdxAExp a2 env idxCtx a2_r)
       -> ReifyIdxBExp (LTE a1 a2 ok) env idxCtx (LTE a1_r a2_r ok)

  data EnvCtxTree : (vs : VarSet ns is as fs) -> Type where
    Leaf : (env : Env vs) -> (idxCtx : IdxCtx vs env) -> EnvCtxTree vs
    Node : (l : EnvCtxTree vs) -> (r : EnvCtxTree vs) -> EnvCtxTree vs

  ||| Relates a loop-unrolled statement with its equivalent index-reified statement.
  |||
  data ReifyIdxStmt : {vs : VarSet ns is as fs}
                   -> (s : LUStmt c cnst vs)
                   -> (env_0 : Env vs)
                   -> (idxCtx_0 : IdxCtx vs env_0)
                   -> (s_r : RStmt c cnst vs)
                  --  -> (envCtx_z : EnvCtxTree vs)
                   -> Type where
    Assn : (aRI : ReifyIdxAExp a env_0 idxCtx_0 a_r)
        -> (kRI : ReifyIdxStmt s_k env_0 idxCtx_0 k_r)
        -> ReifyIdxStmt (Assn var a s_k) env_0 idxCtx_0 (Assn var a_r k_r)
    ||| We don't need to worry about checking for an old instance of idx,
    ||| b/c isElem finds the new one first.
    |||
    ||| Proof of this?
    Idxd : (kRI : ReifyIdxStmt s_k (MkEnv nums (idx :: idxs) arys funs) (MkIdxCtx (Z :: ubs)) k_r)
        -> ReifyIdxStmt (Idxd idx s_k) (MkEnv nums idxs arys funs) (MkIdxCtx ubs) (Idxd k_r)
    ||| We don't bother to update the ub in idxCtx_0 b/c isElem will find the new one first.
    ||| Note that updates within for loops will be handled by at the loop level.
    |||
    ||| Proof of this?
    Idxi : (idxinenv : Elem idx idxs)
        -> (arr : ArrIdxBounds idxs ubs idxinenv ub)
        -> (kRI : ReifyIdxStmt s_k (MkEnv nums (idx :: idxs) arys funs) (MkIdxCtx (S ub :: ubs)) k_r)
        -> ReifyIdxStmt (Idxi idx s_k) (MkEnv nums idxs arys funs) (MkIdxCtx ubs) (Idxi k_r)
    Aryd : (kRI : ReifyIdxStmt s_k (MkEnv nums idxs arys funs) (MkIdxCtx ubs) k_r)
        -> ReifyIdxStmt (Aryd var len lenNZ s_k) (MkEnv nums idxs arys funs) (MkIdxCtx ubs) (Aryd var len lenNZ k_r)
    Aryu : (aRI : ReifyIdxAExp a (MkEnv nums idxs arys funs) (MkIdxCtx ubs) a_r)
        -> (idxinenv : Elem idx idxs)
        -> (arr : ArrIdxBounds idxs ubs idxinenv ub)
        -> (kRI : ReifyIdxStmt s_k (MkEnv nums idxs arys funs) (MkIdxCtx ubs) k_r)
        -> ReifyIdxStmt (Aryu var len lenNZ idx a s_k) (MkEnv nums idxs arys funs) (MkIdxCtx ubs) (Aryu var len lenNZ ub a_r k_r)
    -- Iftt : (bRI : ReifyIdxBExp b env_0 idxCtx_0 b_r)
    --     -> (ttRI : ReifyIdxStmt s_tt env_0 idxCtx_0 t_r (Leaf env_ttz idxCtx_ttz))
    --     -> (kttRI : ReifyIdxStmt s_k env_tz idxCtx_tz k_tt envCtx_kttz)
    --     -> (kffRI : ReifyIdxStmt s_k env_0 idxCtx_0 k_ff envCtx_kffz)
    --     -> ReifyIdxStmt (Iftt b s_tt s_k) env_0 idxCtx_0
    --                     (Iftt b_r t_r (Node (Leaf k_tt) (Leaf k_ff)) MkNotLeaf)
    --                     (Node envCtx_kttz envCtx_kffz)
    Stop : ReifyIdxStmt Stop env_0 idxCtx_0 Stop

    Cert : (bRI : ReifyIdxBExp b env_0 idxCtx_0 b_r)
        -> (kRI : ReifyIdxStmt s_k env_0 idxCtx_0 k_r)
        -> ReifyIdxStmt (Cert b s_k) env_0 idxCtx_0 (Cert b_r k_r)

reifyIdxAExp : (a : AExp c cnst vs)
            -> (env : Env vs)
            -> (idxCtx : IdxCtx vs env)
            -> Dec (a_r : RAExp c cnst vs ** ReifyIdxAExp a env idxCtx a_r)
reifyIdxAExp (Val n) env idxCtx = Yes (Val n ** Val)
reifyIdxAExp (Var var) env idxCtx = Yes (Var var ** Var)
reifyIdxAExp (Acc var len idx) (MkEnv nums idxs arys funs) (MkIdxCtx ubs) with (isElem idx idxs)
  | No idxisndecld =
    No (\((Acc v l b) ** (Acc idxIsDecld arridxub)) => idxisndecld idxIsDecld)
  | Yes idxisdecld with (arrIdxBounds idxs ubs idxisdecld)
    | (idx_bounds ** arridxub) = Yes (Acc var len idx_bounds ** Acc idxisdecld arridxub)
reifyIdxAExp (Neg a p) env idxCtx with (reifyIdxAExp a env idxCtx)
  | No aNRI = No (\(Neg a_r p ** Neg aRI) => aNRI (a_r ** aRI))
  | Yes (a_r ** aRI) = Yes (Neg a_r p ** Neg aRI)
reifyIdxAExp (Add a1 a2) env idxCtx with (reifyIdxAExp a1 env idxCtx)
  | No a1NRI = No (\(Add a1_r a2_r ** Add a1RI a2RI) => a1NRI (a1_r ** a1RI))
  | Yes (a1_r ** a1RI) with (reifyIdxAExp a2 env idxCtx)
    | No a2NRI = No (\(Add a1_r a2_r ** Add a1RI a2RI) => a2NRI (a2_r ** a2RI))
    | Yes (a2_r ** a2RI) = Yes (Add a1_r a2_r ** Add a1RI a2RI)
reifyIdxAExp (Mul a1 a2 p) env idxCtx with (reifyIdxAExp a1 env idxCtx)
  | No a1NRI = No (\(Mul a1_r a2_r p ** Mul a1RI a2RI) => a1NRI (a1_r ** a1RI))
  | Yes (a1_r ** a1RI) with (reifyIdxAExp a2 env idxCtx)
    | No a2NRI = No (\(Mul a1_r a2_r p ** Mul a1RI a2RI) => a2NRI (a2_r ** a2RI))
    | Yes (a2_r ** a2RI) = Yes (Mul a1_r a2_r p ** Mul a1RI a2RI)

reifyIdxBExp : (b : BExp c cnst vs)
            -> (env : Env vs)
            -> (idxCtx : IdxCtx vs env)
            -> Dec (b_r : RBExp c cnst vs ** ReifyIdxBExp b env idxCtx b_r)
reifyIdxBExp (Eq a1 a2) env idxCtx
  with (reifyIdxAExp a1 env idxCtx)
    | No a1NRI = No (\(Eq a1_r a2_r ** Eq a1RI a2RI) => a1NRI (a1_r ** a1RI))
    | Yes (a1_r ** a1RI) with (reifyIdxAExp a2 env idxCtx)
      | No a2NRI = No (\(Eq a1_r a2_r ** Eq a1RI a2RI) => a2NRI (a2_r ** a2RI))
      | Yes (a2_r ** a2RI) = Yes (Eq a1_r a2_r ** Eq a1RI a2RI)
reifyIdxBExp (LTE a1 a2 ok) env idxCtx
  with (reifyIdxAExp a1 env idxCtx)
    | No a1NRI = No (\(LTE a1_r a2_r ok ** LTE a1RI a2RI) => a1NRI (a1_r ** a1RI))
    | Yes (a1_r ** a1RI) with (reifyIdxAExp a2 env idxCtx)
      | No a2NRI = No (\(LTE a1_r a2_r ok ** LTE a1RI a2RI) => a2NRI (a2_r ** a2RI))
      | Yes (a2_r ** a2RI) = Yes (LTE a1_r a2_r ok ** LTE a1RI a2RI)

{-
idxiKNRI : (idxinenv : Elem idx idxs) 
        -> (ub : Nat)
        -> (arr : ArrIdxBounds idxs ubs idxinenv ub)
        -> (kNRI : Not (s_r : RStmt c cnst (MkVarSet ns is as)
                        ** ReifyIdxStmt s_k (MkEnv nums (idx :: idxs) arys) (MkIdxCtx (S ub :: ubs)) s_r))
        -> (s_r : RStmt c cnst (MkVarSet ns is as)
            ** ReifyIdxStmt (Idxi idx s_k) (MkEnv nums idxs arys) (MkIdxCtx ubs) s_r)
        -> Void
idxiKNRI idxinenv ub arr kNRI (Idxi k_r ** Idxi idxinenv' arr' kRI) = ?holeLemma
-}

||| Changed to Maybe and move on b/c at this point we don't really care *why* s isn't well-formed. 
||| Rather, we are only interested in well-formed programs.
|||
||| An alternative approach would be to define a system where it *doesn't* work and Either it.
|||
||| I think we really need to drop these Vectors and use proper sets to do it properly.
||| For uniqueness: have a type that folds over the list, but instead of saying ((Not) x = x_i) 
||| which can lead to annoyances, state that Either (LT x x_i) (GT x x_i).
reifyIdxStmt : {ns : Vect x1 (Var Numerical)}
            -> {is : Vect x2 (Var Index)}
            -> {as : Vect x3 (Var Array)}
            -> {fs : Vect x4 (Var Function)}
            -> (vs : VarSet ns is as fs)
            -> (s : LUStmt c cnst vs)
            -> (env : Env vs)
            -> (idxCtx : IdxCtx vs env)
            -> Maybe (s_r : RStmt c cnst vs
                      -- ** envCtx_z : EnvCtxTree vs
                      ** ReifyIdxStmt s env idxCtx s_r)
reifyIdxStmt (MkVarSet ns is as fs) (Assn var a s_k) (MkEnv nums idxs arys funs) (MkIdxCtx ubs)
  with (reifyIdxAExp a (MkEnv nums idxs arys funs) (MkIdxCtx ubs))
    | No aNRI = Nothing -- No (\(Assn var a_r k_r ** Assn aRI kRI) => aNRI (a_r ** aRI))
    | Yes (a_r ** aRI) with (reifyIdxStmt (MkVarSet ns is as fs) s_k (MkEnv nums idxs arys funs) (MkIdxCtx ubs))
      -- | No kNRI = No (\(Assn var a_r k_r ** Assn aRI kRI) => kNRI (k_r ** kRI))
      | Nothing = Nothing
      | Just (k_r ** kRI) = Just (Assn var a_r k_r ** Assn aRI kRI)
reifyIdxStmt (MkVarSet ns is as fs) (Idxd var s_k) (MkEnv nums idxs arys funs) (MkIdxCtx ubs)
  with (reifyIdxStmt (MkVarSet ns is as fs) s_k (MkEnv nums (var :: idxs) arys funs) (MkIdxCtx (Z :: ubs)))
    -- | No kNRI = No (\(Idxd k_r ** Idxd kRI) => kNRI (k_r ** kRI))
    | Nothing = Nothing
    | Just (k_r ** kRI) = Just (Idxd k_r ** Idxd kRI)
reifyIdxStmt (MkVarSet ns is as fs) (Idxi idx s_k) (MkEnv nums idxs arys funs) (MkIdxCtx ubs)
  with (isElem idx idxs)
    | No idxninenv = Nothing -- No (\(Idxi k_r ** Idxi idxinenv arr kRI) => idxninenv idxinenv)
    | Yes idxinenv with (arrIdxBounds idxs ubs idxinenv)
      | (ub ** arr)
        with (reifyIdxStmt (MkVarSet ns is as fs) s_k (MkEnv nums (idx :: idxs) arys funs) (MkIdxCtx (S ub :: ubs)))
          -- | No kNRI = No (idxiKNRI idxinenv ub arr kNRI)
          | Nothing = Nothing
          | Just (k_r ** kRI) = Just (Idxi k_r ** Idxi idxinenv arr kRI)
reifyIdxStmt (MkVarSet ns is as fs) (Aryd var len lenNZ s_k) (MkEnv nums idxs arys funs) (MkIdxCtx ubs)
  with (reifyIdxStmt (MkVarSet ns is as fs) s_k (MkEnv nums idxs arys funs) (MkIdxCtx ubs))
    | Nothing = Nothing
    | Just (k_r ** kRI) = Just (Aryd var len lenNZ k_r ** Aryd kRI)
reifyIdxStmt (MkVarSet ns is as fs) (Aryu var len lenNZ idx a s_k) (MkEnv nums idxs arys funs) (MkIdxCtx ubs)
  with (reifyIdxStmt (MkVarSet ns is as fs) s_k (MkEnv nums idxs arys funs) (MkIdxCtx ubs))
    | Nothing = Nothing
    | Just (k_r ** kRI) with (reifyIdxAExp a (MkEnv nums idxs arys funs) (MkIdxCtx ubs))
      | No aNRI = Nothing
      | Yes (a_r ** aRI) with (isElem idx idxs)
        | No idxninenv = Nothing
        | Yes idxinenv with (arrIdxBounds idxs ubs idxinenv)
          | (ub ** arr) = Just (Aryu var len lenNZ ub a_r k_r
                                ** Aryu aRI idxinenv arr kRI)
-- reifyIdxStmt (MkVarSet ns is as fs) (Iftt b s_tt s_k) (MkEnv nums idxs arys funs) (MkIdxCtx ubs)
--   with (reifyIdxStmt (MkVarSet ns is as fs) s_tt (MkEnv nums idxs arys funs) (MkIdxCtx ubs))
--     | Nothing = Nothing
--     | Just (tt_r ** (Node l r) ** ttRI) = Nothing
--     | Just (tt_r ** (Leaf env_ttz idxCtx_ttz) ** ttRI)
--       with (reifyIdxStmt (MkVarSet ns is as fs) s_k env_ttz idxCtx_ttz)
--         | Nothing = Nothing
--         | Just (k_tt ** envCtx_kttz ** ttkRI)
--           with (reifyIdxStmt (MkVarSet ns is as fs) s_k (MkEnv nums idxs arys funs) (MkIdxCtx ubs))
--             | Nothing = Nothing
--             | Just (k_ff ** envCtx_kffz ** ffkRI)
--               with (reifyIdxBExp b (MkEnv nums idxs arys funs) (MkIdxCtx ubs))
--                 | No bNRI = Nothing
--                 | Yes (b_r ** bRI) =
--                   Just $ assert_total (Iftt b_r tt_r (Node (Leaf k_tt) (Leaf k_ff)) MkNotLeaf
--                                         ** Node envCtx_kttz envCtx_kffz
--                                         ** Iftt bRI ttRI ttkRI ffkRI)

-- reifyIdxStmt vs s env idxCtx = ?holeReifyIdxStmt
reifyIdxStmt vs Stop env idxCtx = Just (Stop ** Stop)

reifyIdxStmt vs (Cert b s_k) env_0 idxCtx_0 with (reifyIdxBExp b env_0 idxCtx_0)
  | No bNRI = Nothing
  | Yes (b_r ** bRI) with (reifyIdxStmt vs s_k env_0 idxCtx_0)
    | Nothing = Nothing
    | Just (k_r ** kRI) = Just (Cert b_r k_r ** Cert bRI kRI)
