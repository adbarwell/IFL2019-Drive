module LoopUnrolling

import public EnvCtxUtil

%default total
%access public export

{-
  Semantics at the statement level requires loop-unrolling.
-}

-- [Loop Unrolling] -------------------------------------------------------------------------------

data LUStmt : (c : Type) -> (cnst : Struct c set kind) -> (vs : VarSet ns is as fs) -> Type where
  Assn : (var : Elem NumVar ns)
      -> (a : AExp c cnst (MkVarSet ns is as fs))
      -> (s_k : LUStmt c cnst (MkVarSet ns is as fs))
      -> LUStmt c cnst (MkVarSet ns is as fs)
  Idxd : (idx : Elem IdxVar is)
      -> (s_k : LUStmt c cnst (MkVarSet ns is as fs))
      -> LUStmt c cnst (MkVarSet ns is as fs)
  Idxi : (idx : Elem IdxVar is)
      -> (s_k : LUStmt c cnst (MkVarSet ns is as fs))
      -> LUStmt c cnst (MkVarSet ns is as fs)
  Aryd : (var : Elem AryVar as)
      -> (len : Nat)
      -> (lenNZ : NotZero len)
      -> (s_k : LUStmt c cnst (MkVarSet ns is as fs))
      -> LUStmt c cnst (MkVarSet ns is as fs)
  Aryu : (var : Elem AryVar as)
      -> (len : Nat)
      -> (lenNZ : NotZero len)
      -> (idx : Elem IdxVar is)
      -> (a : AExp c cnst (MkVarSet ns is as fs))
      -> (s_k : LUStmt c cnst (MkVarSet ns is as fs))
      -> LUStmt c cnst (MkVarSet ns is as fs)
  -- Iftt : (b : BExp c cnst vs)
  --     -> (k_tt : LUStmt c cnst vs)
  --     -> (k_ff : LUStmt c cnst vs)
  --     -> LUStmt c cnst vs
  Stop : LUStmt c cnst vs

  Cert : (b : BExp c cnst vs) -> (s_k : LUStmt c cnst vs) -> LUStmt c cnst vs

(++) : (s1 : LUStmt c cnst vs) -> (s2 : LUStmt c cnst vs) -> LUStmt c cnst vs
(++) (Assn var a s_k) s2 = Assn var a (s_k ++ s2)
(++) (Idxd var s_k) s2 = Idxd var (s_k ++ s2)
(++) (Idxi var s_k) s2 = Idxi var (s_k ++ s2)
(++) (Aryd var len lenNZ s_k) s2 = Aryd var len lenNZ (s_k ++ s2)
(++) (Aryu var len lenNZ idx a s_k) s2 = Aryu var len lenNZ idx a (s_k ++ s2)
-- (++) (Iftt b k_tt k_ff) s2 = Iftt b (k_tt ++ s2) (k_ff ++ s2)
(++) Stop s2 = s2

(++) (Cert b s_k) s2 = Cert b (s_k ++ s2)

namespace LURel
  ||| .
  ||| @env_0 the environment for `s` and `s_lu`; we only consider array declarations here.
  ||| @env_z the environment at the very end of `s_lu`; useful for for statements.
  data UnrollCPStmt : (s : CPStmt c cnst vs)
                   -> (env_0 : Env vs)
                   -> (s_lu : LUStmt c cnst vs)
                  --  -> (env_z : Tree (Env vs))
                   -> (env_z : Env vs)
                   -> Type where
    Assn : (kLU : UnrollCPStmt s_k env_0 k_lu env_z)
        -> UnrollCPStmt (Assn var a s_k) env_0 (Assn var a k_lu) env_z
    Idxd : (kLU : UnrollCPStmt s_k env_0 k_lu env_z)
        -> UnrollCPStmt (Idxd idx s_k) env_0 (Idxd idx k_lu) env_z
    Idxi : (kLU : UnrollCPStmt s_k env_0 k_lu env_z)
        -> UnrollCPStmt (Idxi idx s_k) env_0 (Idxi idx k_lu) env_z
    Aryd : (kLU : UnrollCPStmt s_k (MkEnv nums idxs ((var, (len ** lenNZ)) :: arys) funs) k_lu env_z)
        -> UnrollCPStmt (Aryd var len lenNZ s_k)
                        (MkEnv nums idxs arys funs)
                        (Aryd var len lenNZ k_lu) env_z
    Aryu : (kLU : UnrollCPStmt s_k env_0 k_lu env_z)
        -> UnrollCPStmt (Aryu var len lenNZ idx a s_k) env_0 (Aryu var len lenNZ idx a k_lu) env_z
    -- ||| We do not permit the occurrence of any variable declared in the true branch.
    -- ||| If the condition is *not* true and the variable *is not* otherwise declared prior to the 
    -- ||| occurrence of that variable in `s_k` then the program cannot be considered well-formed.
    -- Iftt : (ttLU : UnrollCPStmt k_tt env_0 tt_lu env_tz)
    --     -> (ffLU : UnrollCPStmt k_ff env_0 ff_lu env_fz)
    --     -> UnrollCPStmt (Iftt b k_tt k_ff) env_0 (Iftt b tt_lu ff_lu) (Node env_tz env_fz)
    ||| Iterations are guaranteed (via `lenNZ`) to execute their body at least once; so we permit
    ||| declarations of variables in the loop body to persist in the environment of `s_k`.
    Iter : (aryinarys : Elem (ary,(len ** lenNZ)) arys)
        -> (sLU : UnrollCPStmt s (MkEnv nums idxs arys funs) s_lu env_sz)
        -> (kLU : UnrollCPStmt s_k env_sz k_lu env_kz)
        -> UnrollCPStmt (Iter var idx ary len lenNZ s s_k) (MkEnv nums idxs arys funs) (Idxd idx (foldr (++) Stop (Vect.replicate (pred len) (Assn var (Acc ary len idx) (s_lu ++ (Idxi idx Stop))))) ++ (Assn var (Acc ary len idx) (s_lu ++ k_lu))) env_kz
    Stop : UnrollCPStmt Stop env Stop env

    Cert : (kLU : UnrollCPStmt s_k env k_lu env_z)
        -> UnrollCPStmt (Cert b s_k) env (Cert b k_lu) env_z

||| This is a Maybe instead of a Dec, because the type checker doesn't like us pattern matching on
||| the fold in the Iter clause; I imagine that I would need to write my own function for this.
||| Which, I note, is something that irritates me about dependent types: it's *harder* to use
||| recursion schemes.
unrollCPStmt : (s : CPStmt c cnst vs)
            -> (env : Env vs)
            -> Maybe (s_lu : LUStmt c cnst vs ** env_z : Env vs ** UnrollCPStmt s env s_lu env_z)
unrollCPStmt (Assn var a s_k) env with (unrollCPStmt s_k env)
  | Nothing = Nothing
  | Just (k_lu ** env_z ** kLU) = Just (Assn var a k_lu ** env_z ** Assn kLU)
unrollCPStmt (Idxd idx s_k) env with (unrollCPStmt s_k env)
  | Nothing = Nothing
  | Just (k_lu ** env_z ** kLU) = Just (Idxd idx k_lu ** env_z ** Idxd kLU)
unrollCPStmt (Idxi idx s_k) env with (unrollCPStmt s_k env)
  | Nothing = Nothing
  | Just (k_lu ** env_z ** kLU) = Just (Idxi idx k_lu ** env_z ** Idxi kLU)
unrollCPStmt (Aryd var len lenNZ s_k) (MkEnv nums idxs arys funs)
  with (unrollCPStmt s_k (MkEnv nums idxs ((var, (len ** lenNZ)) :: arys) funs))
    | Nothing = Nothing
    | Just (k_lu ** env_z ** kLU) = Just (Aryd var len lenNZ k_lu ** env_z ** Aryd kLU)
unrollCPStmt (Aryu var len lenNZ idx a s_k) env with (unrollCPStmt s_k env)
  | Nothing = Nothing
  | Just (k_lu ** env_z ** kLU) = Just (Aryu var len lenNZ idx a k_lu ** env_z ** Aryu kLU)
unrollCPStmt (Iftt b k_tt k_ff) env = Nothing
-- unrollCPStmt (Iftt b k_tt k_ff) env with (unrollCPStmt k_tt env, unrollCPStmt k_ff env)
--   | (Nothing, _) = Nothing
--   | (_, Nothing) = Nothing
--   | (Just (tt_lu ** env_tz ** ttLU), Just (ff_lu ** env_fz ** ffLU)) =
--     Just (Iftt b tt_lu ff_lu ** (Node env_tz env_fz) ** Iftt ttLU ffLU)
unrollCPStmt (Iter var idx ary len lenNZ s s_k) (MkEnv nums idxs arys funs)
  with (isElem (ary,(len ** lenNZ)) arys)
    -- | No aryninarys = No (\(foldrImpl (++) Stop id (replicate len s_lu) ++ k_lu ** env_z ** Iter aryinarys sLU kLU) => aryninarys aryinarys)
    | No aryninarys = Nothing
    | Yes aryinarys
      with (unrollCPStmt s (MkEnv nums idxs arys funs))
        | Nothing = Nothing
        | Just (s_lu ** env_sz ** sLU) with (unrollCPStmt s_k env_sz)
          | Nothing = Nothing
          | Just (k_lu ** env_kz ** kLU) =
            Just ((Idxd idx (foldr (++) Stop (Vect.replicate (pred len) (Assn var (Acc ary len idx) (s_lu ++ (Idxi idx Stop))))) ++ (Assn var (Acc ary len idx) (s_lu ++ k_lu)))
                  ** env_kz
                  ** Iter aryinarys sLU kLU)

-- unrollCPStmt s env = ?holeUnroll
unrollCPStmt Stop env = Just (Stop ** env ** Stop)

unrollCPStmt (Cert b s_k) env with (unrollCPStmt s_k env)
  | Nothing = Nothing
  | Just (k_lu ** env_z ** kLU) = Just (Cert b k_lu ** env_z ** Cert kLU)

-- [Well-Formedness] ------------------------------------------------------------------------------
{-
  A well-formed index-reified program implies that the equivalent loop-unrolled program is also 
  well-formed.
-}

{- No longer needed.
namespace WF
  data WFLRStmt : (s : LRStmt c cnst vs) -> (env : Env vs) -> Type where
    Assn : (a_wf : WFRAExp a (MkEnv nums idxs arys))
        -> (k_wf : WFLRStmt s_k (MkEnv (var :: nums) idxs arys))
        -> WFLRStmt (Assn var a s_k) (MkEnv nums idxs arys)
    Idxd : (k_wf : WFLRStmt s_k env) -> WFLRStmt (Idxd s_k) env
    Idxi : (k_wf : WFLRStmt s_k env) -> WFLRStmt (Idxi s_k) env
    Stop : WFLRStmt Stop env

  lemma_WFRStmt_implies_WFLRStmt : (s : RStmt c cnst vs)
                                -> (s_wf : WFRStmt s env)
                                -> (s_lr : LRStmt c cnst vs)
                                -> (rel : UnrollRStmt s s_wf s_lr)
                                -> WFLRStmt s_lr env
  lemma_WFRStmt_implies_WFLRStmt (Assn var a s_k) (Assn a_wf k_wf) (Assn var a k_lr) (Assn kLR) 
    with (lemma_WFRStmt_implies_WFLRStmt s_k k_wf k_lr kLR)
      | k_wf' = Assn a_wf k_wf'
  lemma_WFRStmt_implies_WFLRStmt (Idxd s_k) (Idxd k_wf) (Idxd k_lr) (Idxd kLR)
    with (lemma_WFRStmt_implies_WFLRStmt s_k k_wf k_lr kLR)
        | k_wf' = Idxd k_wf'
  lemma_WFRStmt_implies_WFLRStmt (Idxi s_k) (Idxi k_wf) (Idxi k_lr) (Idxi kLR)
    with (lemma_WFRStmt_implies_WFLRStmt s_k k_wf k_lr kLR)
        | k_wf' = Idxi k_wf'
  -- lemma_WFRStmt_implies_WFLRStmt s s_wf s_lr rel = ?holeLemma
  lemma_WFRStmt_implies_WFLRStmt Stop Stop Stop Stop = Stop
-}
