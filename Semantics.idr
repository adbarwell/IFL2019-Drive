module Semantics

import public WellFormedness

%default total
%access public export

{-
  Two stage approach: reification (loop-unfolding -> indices) and reduction

  Loops are bound, so we can unroll them easily.
-}

-- [Arithmetic Expressions] -----------------------------------------------------------------------

||| Big-step operational semantics for index-reified arithmetic expressions.
data SRAExp : (cnst: Struct c set kind)
           -> (a : RAExp c cnst vs)
           -> (env : Env vs)
           -> (a_wf : WFRAExp a env)
           -> (ctx : Ctx c env)
           -> (val : c)
           -> Type where
  Val : SRAExp cnst (Val n) env Val ctx n
  Var : (arr : ArrVarC nums vals varinenv val)
     -> SRAExp cnst (Var var) (MkEnv nums idxs arys funs) (Var varinenv) (MkCtx nvals avals ok) val
  Acc : (arr : ArrVarIdxC arys avals ok varinenv (natToFin idx len idxLTlen) val)
     -> SRAExp cnst (Acc var len idx) (MkEnv nums idxs arys funs) (Acc lenNZ varinenv idxLTlen) (MkCtx nvals avals ok) val
  Neg : (a_s : SRAExp cnst a env a_wf ctx val)
     -> SRAExp cnst (Neg a ok) env (Neg a_wf) ctx (inverseFn (projNeg cnst ok) val)
  Add : (a1_s : SRAExp cnst a1 env a1_wf ctx a1_val)
     -> (a2_s : SRAExp cnst a2 env a2_wf ctx a2_val)
     -> SRAExp cnst (Add a1 a2) env (Add a1_wf a2_wf) ctx (binOpFn (projPlus cnst) a1_val a2_val)
  Mul : (a1_s : SRAExp cnst a1 env a1_wf ctx a1_val)
     -> (a2_s : SRAExp cnst a2 env a2_wf ctx a2_val)
     -> SRAExp cnst (Mul a1 a2 ok) env (Mul a1_wf a2_wf) ctx (binOpFn (projMul cnst ok) a1_val a2_val)

sraexp : {vs : VarSet numvs idxsvs aryvs funvs}
      -> (cnst : Struct c set kind)
      -> (a : RAExp c cnst vs)
      -> (env : Env vs)
      -> (a_wf : WFRAExp a env)
      -> (ctx : Ctx c env)
      -> (val : c ** SRAExp cnst a env a_wf ctx val)
sraexp cnst (Val n) env Val ctx = (n ** Val)
sraexp cnst (Var var) (MkEnv nums idxs arys funs) (Var varinenv) (MkCtx nvals avals ok) -- = ?holeHere
  with (arrVarC nums nvals varinenv)
    | (val ** arr) = (val ** Var arr)
sraexp cnst (Acc var len idx) (MkEnv nums idxs arys funs) (Acc lenNZ varinenv idxLTlen) (MkCtx nvals avals ok)
  with (arrVarIdxC arys avals ok varinenv (natToFin idx len idxLTlen))
    | (val ** arr) = (val ** Acc arr)
sraexp cnst (Neg a ok) env (Neg a_wf) ctx
  with (sraexp cnst a env a_wf ctx)
    | (val ** a_s) = (inverseFn (projNeg cnst ok) val ** Neg a_s)
sraexp cnst (Add a1 a2) env (Add a1_wf a2_wf) ctx
  with (sraexp cnst a1 env a1_wf ctx, sraexp cnst a2 env a2_wf ctx)
    | ((a1_val ** a1_s),(a2_val ** a2_s)) =
      (binOpFn (projPlus cnst) a1_val a2_val ** Add a1_s a2_s)
sraexp cnst (Mul a1 a2 ok) env (Mul a1_wf a2_wf) ctx
  with (sraexp cnst a1 env a1_wf ctx, sraexp cnst a2 env a2_wf ctx)
    | ((a1_val ** a1_s),(a2_val ** a2_s)) =
      (binOpFn (projMul cnst ok) a1_val a2_val ** Mul a1_s a2_s)

data SAExp : Type where

-- [Boolean Expressions] --------------------------------------------------------------------------

data SRBExp : (cnst: Struct c set kind)
           -> (b : RBExp c cnst vs)
           -> (env : Env vs)
           -> (b_wf : WFRBExp b env)
           -> (ctx : Ctx c env)
           -> (val : Bool)
           -> Type where
  Eq : (a1_s : SRAExp cnst a1 env a1_wf ctx a1_val)
    -> (a2_s : SRAExp cnst a2 env a2_wf ctx a2_val)
    -> SRBExp cnst (Eq a1 a2) env (Eq a1_wf a2_wf) ctx (setDefnFn (projSet cnst) a1_val a2_val)
  LTE : (a1_s : SRAExp (OrdSemigroup sgp (MkTotalOrder ltety is_lte def_lte)) a1 env a1_wf ctx a1_val)
     -> (a2_s : SRAExp (OrdSemigroup sgp (MkTotalOrder ltety is_lte def_lte)) a2 env a2_wf ctx a2_val)
     -> SRBExp (OrdSemigroup sgp (MkTotalOrder ltety is_lte def_lte)) (LTE a1 a2 OrdSemigroup) env (LTE a1_wf a2_wf) ctx (def_lte a1_val a2_val)

srbexp : (cnst: Struct c set kind)
      -> (b : RBExp c cnst vs)
      -> (env : Env vs)
      -> (b_wf : WFRBExp b env)
      -> (ctx : Ctx c env)
      -> (val : Bool ** SRBExp cnst b env b_wf ctx val)
srbexp cnst (Eq a1 a2) env (Eq a1_wf a2_wf) ctx
  with (sraexp cnst a1 env a1_wf ctx, sraexp cnst a2 env a2_wf ctx)
    | ((a1_val ** a1_s), (a2_val ** a2_s)) =
      (setDefnFn (projSet cnst) a1_val a2_val ** Eq a1_s a2_s)
srbexp (OrdSemigroup sgp (MkTotalOrder ltety is_lte def_lte)) (LTE a1 a2 OrdSemigroup) env (LTE a1_wf a2_wf) ctx
  with (sraexp (OrdSemigroup sgp (MkTotalOrder ltety is_lte def_lte)) a1 env a1_wf ctx, sraexp (OrdSemigroup sgp (MkTotalOrder ltety is_lte def_lte)) a2 env a2_wf ctx)
    | ((a1_val ** a1_s), (a2_val ** a2_s)) =
      let val = def_lte a1_val a2_val
      in (val ** LTE a1_s a2_s)

-- [Statements] -----------------------------------------------------------------------------------

data AryCtxUpdateDecl : (cnst : Struct c set kind)
                     -> (arys : Vect m (Elem AryVar as, (s : Nat ** NotZero s)))
                     -> (avals_0 : Vect m (t : Nat ** Vect t c))
                     -> (ok_0 : StructSame arys avals_0)
                     -> (var : Elem AryVar as)
                     -> (len : Nat)
                     -> (lenNZ : NotZero len)
                     -> (avals : Vect (S m) (u : Nat ** Vect u c))
                     -> (ok : StructSame ((var,(len ** lenNZ)) :: arys) avals)
                     -> Type where
  MkAryCtxUpdateDecl : AryCtxUpdateDecl cnst arys avals_0 ok_0 var len lenNZ ((len ** replicate len (zeroFn cnst)) :: avals_0) (Cons Refl ok_0)

aryCtxUpdateDecl : (cnst : Struct c set kind)
                -> (arys : Vect m (Elem AryVar as, (s : Nat ** NotZero s)))
                -> (avals_0 : Vect m (t : Nat ** Vect t c))
                -> (ok_0 : StructSame arys avals_0)
                -> (var : Elem AryVar as)
                -> (len : Nat)
                -> (lenNZ : NotZero len)
                -> (avals : Vect (S m) (u : Nat ** Vect u c)
                    ** ok : StructSame ((var,(len ** lenNZ)) :: arys) avals
                    ** AryCtxUpdateDecl cnst arys avals_0 ok_0 var len lenNZ avals ok)
aryCtxUpdateDecl cnst arys avals_0 ok_0 var len lenNZ =
  (((len ** replicate len (zeroFn cnst)) :: avals_0) ** (Cons Refl ok_0) ** MkAryCtxUpdateDecl)

||| proof of properties? (e.g. doesn't affect any other element; doesn't change length of vect)
updateByElem : (xs : Vect k t) -> Elem x xs -> (t -> t) -> Vect k t
updateByElem (x :: xs) Here f = (f x :: xs)
updateByElem (y :: xs) (There later) f = (y :: updateByElem xs later f)

updateByElemFudge : (ys : Vect k t) -> (ptr : Elem y ys) -> (xs : Vect k s) -> (s -> s) -> Vect k s
updateByElemFudge (y :: ys) Here (x :: xs) f = (f x :: xs)
updateByElemFudge (z :: ys) (There later) (w :: xs) f = (w :: updateByElemFudge ys later xs f)

{- Transforms varinarys into varinavals. Needed for proper AryCtxUpdateAssn.
arys_ptr_implies_avals_ptr : (arys : Vect m (Elem AryVar as, (s : Nat ** NotZero s)))
                          -> (varinarys : Elem (var, (len ** lenNZ)) arys)
                          -> (avals : Vect m (u : Nat ** Vect u c))
                          -> (ok : StructSame arys avals)
                          -> (aval : (t : Nat ** Vect t c) ** Elem aval avals)
-}

data AryCtxUpdateAssn : (cnst : Struct c set kind)
                     -> (arys : Vect m (Elem AryVar as, (s : Nat ** NotZero s)))
                     -> (avals_0 : Vect m (t : Nat ** Vect t c))
                     -> (ok_0 : StructSame arys avals_0)
                     -> (var : Elem AryVar as)
                     -> (len : Nat)
                     -> (lenNZ : NotZero len)
                     -> (varinarys : Elem (var, (len ** lenNZ)) arys)
                     -> (idx : Fin len)
                     -> (val : c)
                     -> (avals : Vect m (u : Nat ** Vect u c))
                     -> (ok : StructSame arys avals)
                     -> Type where
  -- MkAryCtxUpdateAssn : AryCtxUpdateAssn cnst arys avals_0 ok_0 var len lenNZvar varinavals idx val (updateByElem avals_0 varinavals (\(s ** xs) => (s ** replaceAt idx val xs))) -- ok

  ||| This is a cheat!
  MkAryCtxUpdateAssn : (avals : Vect m (u : Nat ** Vect u c))
                    -> (ok : StructSame arys avals)
                    -> AryCtxUpdateAssn cnst arys avals_0 ok_0 var len lenNZvar varinarys idx val avals ok

aryCtxUpdateAssn : (cnst : Struct c set kind)
                -> (arys : Vect m (Elem AryVar as, (s : Nat ** NotZero s)))
                -> (avals_0 : Vect m (t : Nat ** Vect t c))
                -> (ok_0 : StructSame arys avals_0)
                -> (var : Elem AryVar as)
                -> (len : Nat)
                -> (lenNZ : NotZero len)
                -> (varinarys : Elem (var, (len ** lenNZ)) arys)
                -> (idx : Fin len)
                -> (val : c)
                -> (avals : Vect m (u : Nat ** Vect u c)
                    ** ok : StructSame arys avals
                    ** AryCtxUpdateAssn cnst arys avals_0 ok_0 var len lenNZ varinarys idx val avals ok)
-- aryCtxUpdateAssn cnst arys avals_0 ok_0 var len lenNZ varinarys idx val =
--   let avals = updateByElemFudge arys varinarys avals_0 (\(s ** xs) => (s ** replaceAt idx val xs))
--       -- ok = ?holeHere
--   in (avals ** MkAryCtxUpdateAssn avals)
aryCtxUpdateAssn cnst ((var,(len ** lenNZ)) :: arys) ((len ** xs) :: avals_0) (Cons Refl tl) var len lenNZ Here idx val
  = let avals = ((len ** replaceAt idx val xs) :: avals_0)
        ok = Cons Refl tl
    in (avals ** ok ** MkAryCtxUpdateAssn avals ok)

aryCtxUpdateAssn cnst ((elem,(l ** lNZ)) :: arys) ((s ** vect) :: avals_0) (Cons p tl) var len lenNZ (There later) idx val 
  with (aryCtxUpdateAssn cnst arys avals_0 tl var len lenNZ later idx val)
    | (avals ** ok ** MkAryCtxUpdateAssn avals ok) =
      (((s ** vect) :: avals) ** Cons p ok ** MkAryCtxUpdateAssn ((s ** vect) :: avals) (Cons p ok))

||| Context *is* the state?
data SRStmt : (cnst: Struct c set kind)
           -> (s : RStmt c cnst vs)
           -> (env : Env vs)
           -> (s_wf : WFRStmt s env)
           -> (ctx : Ctx c env)
           -> Type where
  Assn : (a_s : SRAExp cnst a (MkEnv nums idxs arys funs) a_wf (MkCtx nvals avals ok) a_val)
      -> (k_s : SRStmt cnst s_k (MkEnv (var :: nums) idxs arys funs) k_wf (MkCtx (a_val :: nvals) avals ok))
      -> SRStmt cnst (Assn var a s_k) (MkEnv nums idxs arys funs) (Assn a_wf k_wf) (MkCtx nvals avals ok)
  Idxd : (k_s : SRStmt cnst s_k env k_wf idxCtx) -> SRStmt cnst (Idxd s_k) env (Idxd k_wf) idxCtx
  Idxi : (k_s : SRStmt cnst s_k env k_wf idxCtx) -> SRStmt cnst (Idxi s_k) env (Idxi k_wf) idxCtx
  Aryd : (newAry : AryCtxUpdateDecl cnst arys avals ok var len lenNZ avals' ok')
      -> (k_s : SRStmt cnst s_k (MkEnv nums idxs ((var,(len ** lenNZ)) :: arys) funs) k_wf (MkCtx nvals avals' ok'))
      -> SRStmt cnst (Aryd var len lenNZ s_k) (MkEnv nums idxs arys funs) (Aryd k_wf) (MkCtx nvals avals ok)
  Aryu : (a_s : SRAExp cnst a (MkEnv nums idxs arys funs) a_wf (MkCtx nvals avals ok) a_val)
      -> (newAry : AryCtxUpdateAssn cnst arys avals ok var len lenNZ varinarys (natToFin idx len idxLTlen) a_var avals' ok')
      -> (k_s : SRStmt cnst s_k (MkEnv nums idxs arys funs) k_wf (MkCtx nvals avals' ok'))
      -> SRStmt cnst (Aryu var len lenNZ idx a s_k) (MkEnv nums idxs arys funs) (Aryu varinarys idxLTlen a_wf k_wf) (MkCtx nvals avals ok)
  Stop : SRStmt cnst Stop env Stop ctx

  Cert : (val : Bool)
      -> (b_s : SRBExp cnst b env b_wf ctx val)
      -> (k_s : SRStmt cnst s_k env k_wf ctx)
      -> SRStmt cnst (Cert b s_k) env (Cert b_wf k_wf) ctx

srstmt : (cnst: Struct c set kind)
      -> (s : RStmt c cnst vs)
      -> (env : Env vs)
      -> (s_wf : WFRStmt s env)
      -> (ctx : Ctx c env)
      -> SRStmt cnst s env s_wf ctx
srstmt cnst (Assn var a s_k) (MkEnv nums idxs arys funs) (Assn a_wf k_wf) (MkCtx nvals avals ok)
  with (sraexp cnst a (MkEnv nums idxs arys funs) a_wf (MkCtx nvals avals ok))
    | (a_val ** a_s) =
      Assn a_s (srstmt cnst s_k (MkEnv (var :: nums) idxs arys funs) k_wf (MkCtx (a_val :: nvals) avals ok))
srstmt cnst (Idxd s_k) env (Idxd k_wf) ctx = Idxd (srstmt cnst s_k env k_wf ctx)
srstmt cnst (Idxi s_k) env (Idxi k_wf) ctx = Idxi (srstmt cnst s_k env k_wf ctx)
srstmt cnst (Aryd var len lenNZ s_k) (MkEnv nums idxs arys funs) (Aryd k_wf) (MkCtx nvals avals ok)
  with (aryCtxUpdateDecl cnst arys avals ok var len lenNZ)
    | (avals' ** ok' ** prf) with (srstmt cnst s_k (MkEnv nums idxs ((var,(len ** lenNZ)) :: arys) funs) k_wf (MkCtx nvals avals' ok'))
      | k_s = Aryd prf k_s
srstmt cnst (Aryu var len lenNZ idx a s_k) (MkEnv nums idxs arys funs) (Aryu varinarys idxLTlen a_wf k_wf) (MkCtx nvals avals ok)
  with (sraexp cnst a (MkEnv nums idxs arys funs) a_wf (MkCtx nvals avals ok))
    | (a_val ** a_s) with (aryCtxUpdateAssn cnst arys avals ok var len lenNZ varinarys (natToFin idx len idxLTlen) a_val)
      | (avals' ** ok' ** p)
        with (srstmt cnst s_k (MkEnv nums idxs arys funs) k_wf (MkCtx nvals avals' ok'))
          | k_s = Aryu a_s p k_s

-- srstmt cnst s env s_wf ctx = ?holeSRStmt
srstmt cnst Stop env Stop ctx = Stop

srstmt cnst (Cert b s_k) env (Cert b_wf k_wf) ctx
  with (srbexp cnst b env b_wf ctx)
    | (val ** b_s) = Cert val b_s (srstmt cnst s_k env k_wf ctx)


getFinalState: {cnst : Struct c set kind}
            -> {s : RStmt c cnst vs}
            -> {env_0 : Env vs}
            -> (s_s : SRStmt cnst s env_0 s_wf ctx_0)
            -> (env : Env vs ** Ctx c env)
getFinalState (Assn a_s k_s) = getFinalState k_s
getFinalState (Idxd k_s) = getFinalState k_s
getFinalState (Idxi k_s) = getFinalState k_s
getFinalState (Aryd newAry k_s) = getFinalState k_s
getFinalState (Aryu a_s newAry k_s) = getFinalState k_s
-- getFinalState s = ?holeFinalState 
getFinalState (Stop {env} {ctx}) = (env ** ctx)

getFinalState (Cert val b_s k_s) = getFinalState k_s
