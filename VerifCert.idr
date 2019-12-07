module VerifCert

import public Semantics

%default total
%access public export

-- [Boolean Expressions] --------------------------------------------------------------------------

{-
data VCRBExp : (cnst : Struct c set kind)
            -> (b : RBExp c cnst vs)
            -> (env : Env vs)
            -> (b_wf : WFRBExp b env)
            -> (ctx : Ctx c env)
            -> Type where
  Eq : {cong : c -> c -> Type}
    -> {set : Setoid c cong}
    -> {cnst : Struct c set kind}
    -> {ctx : Ctx c env}
    -> (a1_s : SRAExp cnst a1 env a1_wf ctx a1_val)
    -> (a2_s : SRAExp cnst a2 env a2_wf ctx a2_val)
    -> (prf : cong a1_val a2_val)
    -> VCRBExp cnst (Eq a1 a2) env (Eq a1_wf a2_wf) ctx

isVCRBExp : (cnst : Struct c set kind)
         -> (b : RBExp c cnst vs)
         -> (env : Env vs)
         -> (b_wf : WFRBExp b env)
         -> (ctx : Ctx c env)
         -> Dec (VCRBExp cnst b env b_wf ctx)
isVCRBExp cnst b env b_wf ctx = ?holeVB

isVCRBExp cnst (Eq a1 a2) env (Eq a1_wf a2_wf) ctx
  with (sraexp cnst a1 env a1_wf ctx)
    | (a1_val ** a1_s) with (sraexp cnst a2 env a2_wf ctx)
      | (a2_val ** a2_s) with (projSetEqFn cnst a1_val a2_val)
        | No neq = No (\(Eq a1_s a2_s eq) =)
-}

{-
data VCRBExp : (cong : c -> c -> Type)
            -> {set : Setoid c cong}
            -> (cnst : Struct c set kind)
            -> (b : RBExp c cnst vs)
            -> (env : Env vs)
            -> (b_wf : WFRBExp b env)
            -> (ctx : Ctx c env)
            -> (val : Bool)
            -> (b_s : SRBExp cnst b env b_wf ctx val)
            -> Type where
  MkVCRBExp : (prf : eq a1_val a2_val)
           -> {a1_s : SRAExp cnst a1 env a1_wf ctx a1_val}
           -> {a2_s : SRAExp cnst a2 env a2_wf ctx a2_val}
           -> VCRBExp eq cnst (Eq a1 a2) env (Eq a1_wf a2_wf) ctx ((setDefnFn (projSet cnst) a1_val a2_val)) (Eq a1_s a2_s)
-}

data OrdVCRBExp : {set : Setoid c eq}
               -> (cnst : Struct c set kind)
               -> (b : RBExp c cnst vs)
               -> (env : Env vs)
               -> (b_wf : WFRBExp b env)
               -> (ctx : Ctx c env)
               -> (b_s : SRBExp cnst b env b_wf ctx val)
               -> Type where
  Eq : {set : Setoid c eq}
    -> {cnst : Struct c set kind}
    -> (prf : eq a1_val a2_val)
    -> {a1_s : SRAExp cnst a1 env a1_wf ctx a1_val}
    -> {a2_s : SRAExp cnst a2 env a2_wf ctx a2_val}
    -> OrdVCRBExp cnst (Eq a1 a2) env (Eq a1_wf a2_wf) ctx (Eq a1_s a2_s)
  LTE : {lte : c -> c -> Type}
     -> (prf : lte a1_val a2_val)
     -> {a1_s : SRAExp (OrdSemigroup sgp (MkTotalOrder lte is_lte def_lte)) a1 env a1_wf ctx a1_val}
     -> {a2_s : SRAExp (OrdSemigroup sgp (MkTotalOrder lte is_lte def_lte)) a2 env a2_wf ctx a2_val}
     -> OrdVCRBExp (OrdSemigroup sgp (MkTotalOrder lte is_lte def_lte)) (LTE a1 a2 OrdSemigroup) env (LTE a1_wf a2_wf) ctx (LTE a1_s a2_s)

projSetEqFn : {cong : c -> c -> Type}
           -> (set : Setoid c cong)
           -> ((i : c) -> (j : c) -> Dec (cong i j))
projSetEqFn (MkSetoid c zero (MkPropEq cong refl sym trans set_cong p) defnEq agree1 agree2) =
  set_cong

{-
isVCRBExp : (cong : c -> c -> Type)
         -> {set : Setoid c cong}
         -> (cnst : Struct c set kind)
         -> (nok : Not (HasOrdering kind))
         -> (set_eq : (i : c) -> (j : c) -> Dec (cong i j))
         -> (b : RBExp c cnst vs)
         -> (env : Env vs)
         -> (b_wf : WFRBExp b env)
         -> (ctx : Ctx c env)
         -> (val : Bool)
         -> (b_s : SRBExp cnst b env b_wf ctx val)
         -> Dec (VCRBExp cong cnst b env b_wf ctx val b_s)
-- isVCRBExp {cong} cnst (Eq a1 a2) env (Eq a1_wf a2_wf) ctx (setDefnFn (projSet cnst) a1_val a2_val) (Eq a1_s a2_s) =
--   case projSetEqFn (projSet cnst) a1_val a2_val of
--     Yes prf => Yes (MkVCRBExp prf)
--     No contra => No (\(MkVCRBExp prf) => ?holeHere) -- impossible (show that cong eq cong)
isVCRBExp cong cnst nok set_eq (Eq a1 a2) env (Eq a1_wf a2_wf) ctx (setDefnFn (projSet cnst) a1_val a2_val) (Eq a1_s a2_s) =
  case set_eq a1_val a2_val of
    Yes prf => Yes (MkVCRBExp prf)
    No contra => No (\(MkVCRBExp prf) => contra prf)
-}

isOrdVCRBExp : (cnst : Struct c set kind)
            -> (b : RBExp c cnst vs)
            -> (env : Env vs)
            -> (b_wf : WFRBExp b env)
            -> (ctx : Ctx c env)
            -> (b_s : SRBExp cnst b env b_wf ctx val)
            -> Dec (OrdVCRBExp cnst b env b_wf ctx b_s)
isOrdVCRBExp {set} cnst (Eq a1 a2) env (Eq a1_wf a2_wf) ctx (Eq {a1_val} {a2_val} a1_s a2_s) = 
  case projSetEqFn set a1_val a2_val of
    Yes prf => Yes (Eq prf)
    No contra => No (\(Eq prf) => contra prf)

isOrdVCRBExp (OrdSemigroup sgp (MkTotalOrder lte is_lte def_lte)) (LTE a1 a2 OrdSemigroup) env (LTE a1_wf a2_wf) ctx (LTE {a1_val} {a2_val} a1_s a2_s) =
  case is_lte a1_val a2_val of
    Yes prf => Yes (LTE prf)
    No contra => No (\(LTE prf) => contra prf)


-- isOrdVCRBExp : (eq : c -> c -> Type)
--             -- -> (lte : c -> c -> Type)
--             -> {set : Setoid c eq}
--             -> (cnst : Struct c set kind)
--             -> (ok : HasOrdering kind)
--             -- -> (is_lte : (s : c) -> (t : c) -> Dec (lte s t))
--             -> (set_eq : (i : c) -> (j : c) -> Dec (eq i j))
--             -> (b : RBExp c cnst vs)
--             -> (env : Env vs)
--             -> (b_wf : WFRBExp b env)
--             -> (ctx : Ctx c env)
--             -- -> (val : Bool)
--             -> (b_s : SRBExp cnst b env b_wf ctx val)
--             -> Dec (OrdVCRBExp eq cnst ok b env b_wf ctx b_s)
-- isOrdVCRBExp eq cnst ok set_eq (Eq a1 a2) env (Eq a1_wf a2_wf) ctx (Eq {a1_val} {a2_val} a1_s a2_s) =
--   case set_eq a1_val a2_val of
--     Yes prf => Yes (Eq prf)
--     No contra => No (\(Eq prf) => contra prf)
-- isOrdVCRBExp eq cnst ok set_eq (Reification.LTE a1 a2 ok) env (WellFormedness.LTE a1_wf a2_wf) ctx (Semantics.LTE a1_s a2_s) = ?holeHere
-- isOrdVCRBExp eq cnst ok set_eq (LTE a1 a2 ok) env (LTE a1_wf a2_wf) ctx (LTE {a1_val} {a2_val} a1_s a2_s) = ?holeKoko
  -- case projIsLTE cnst ok a1_val a2_val of
  --   Yes prf => Yes ?holeKoko -- (LTE prf)
  --   No contra => No ?holeSoko -- (\(LTE prf) => contra prf)

-- [Statements] -----------------------------------------------------------------------------------

data VCRStmt : (cnst : Struct c set kind)
            -> (s : RStmt c cnst vs)
            -> (env : Env vs)
            -> (s_wf : WFRStmt s env)
            -> (ctx : Ctx c env)
            -> (s_s : SRStmt cnst s env s_wf ctx)
            -> Type where
  Assn : (k_vc : VCRStmt cnst s_k (MkEnv (var :: nums) idxs arys funs) k_wf (MkCtx (a_val :: nvals) avals ok) k_s)
      -> VCRStmt cnst (Assn var a s_k) (MkEnv nums idxs arys funs) (Assn a_wf k_wf) (MkCtx nvals avals ok) (Assn a_s k_s)
  Idxd : (k_vc : VCRStmt cnst s_k env (k_wf) ctx k_s)
      -> VCRStmt cnst (Idxd s_k) env (Idxd k_wf) ctx (Idxd k_s)
  Idxi : (k_vc : VCRStmt cnst s_k env k_wf ctx k_s)
      -> VCRStmt cnst (Idxi s_k) env (Idxi k_wf) ctx (Idxi k_s)
  Aryd : (k_vc : VCRStmt cnst s_k (MkEnv nums idxs ((var, (len ** lenNZ)) :: arys) funs) k_wf (MkCtx nvals avals' ok') k_s)
      -> VCRStmt cnst (Aryd var len lenNZ s_k) (MkEnv nums idxs arys funs) (Aryd k_wf) (MkCtx nvals avals ok) (Aryd newAry k_s)
  Aryu : (k_vc : VCRStmt cnst s_k (MkEnv nums idxs arys funs) k_wf (MkCtx nvals avals' ok') k_s)
      -> VCRStmt cnst (Aryu var len lenNZ idx a s_k) (MkEnv nums idxs arys funs) (Aryu varinarys ubLTlen a_wf k_wf) (MkCtx nvals avals ok) (Aryu a_s newAry k_s)
  Stop : VCRStmt cnst Stop env Stop ctx Stop

  Cert : {cong : c -> c -> Type}
      -> {set : Setoid c cong}
      -> {cnst : Struct c set kind}
      -> (ok : Not (HasOrdering kind))
      -> (b_prf : Dec (OrdVCRBExp cnst b env b_wf ctx b_s))
      -> (k_vc : VCRStmt cnst s_k env k_wf ctx k_s)
      -> VCRStmt cnst (Cert b s_k) env (Cert b_wf k_wf) ctx (Cert val b_s k_s)
  OrdCert : {cong : c -> c -> Type}
         -> {set : Setoid c cong}
         -> {cnst : Struct c set kind}
         -> (ok : HasOrdering kind)
         -> (b_prf : Dec (OrdVCRBExp cnst b env b_wf ctx b_s))
         -> (k_vc : VCRStmt cnst s_k env k_wf ctx k_s)
         -> VCRStmt cnst (Cert b s_k) env (Cert b_wf k_wf) ctx (Cert val b_s k_s)

implementation Uninhabited (HasOrdering Magma) where
  uninhabited OrdSemigroup impossible
implementation Uninhabited (HasOrdering Semigroup) where
  uninhabited OrdSemigroup impossible
implementation Uninhabited (HasOrdering Monoid) where
  uninhabited OrdSemigroup impossible
implementation Uninhabited (HasOrdering Group) where
  uninhabited OrdSemigroup impossible
implementation Uninhabited (HasOrdering AbelianGroup) where
  uninhabited OrdSemigroup impossible
implementation Uninhabited (HasOrdering Ring) where
  uninhabited OrdSemigroup impossible

hasOrdering : (cnst : Struct c set kind) -> Dec (HasOrdering kind)
hasOrdering (OrdSemigroup sgp ord) = Yes OrdSemigroup
hasOrdering (Magma set x) = No absurd
hasOrdering (Semigroup s x) = No absurd
hasOrdering (Monoid s x) = No absurd
hasOrdering (Group s x) = No absurd
hasOrdering (AbelianGroup s x) = No absurd
hasOrdering (Ring s x y z w) = No absurd

vcrstmt : {cong : c -> c -> Type}
       -> {set : Setoid c cong}
       -> (cnst : Struct c set kind)
       -> (s : RStmt c cnst vs)
       -> (env : Env vs)
       -> (s_wf : WFRStmt s env)
       -> (ctx : Ctx c env)
       -> (s_s : SRStmt cnst s env s_wf ctx)
       -> VCRStmt cnst s env s_wf ctx s_s
vcrstmt cnst (Assn var a s_k) (MkEnv nums idxs arys funs) (Assn a_wf k_wf) (MkCtx nvals avals ok) (Assn {a_val} a_s k_s) =
  Assn (vcrstmt cnst s_k (MkEnv (var :: nums) idxs arys funs) k_wf (MkCtx (a_val :: nvals) avals ok) k_s)
vcrstmt cnst (Idxd s_k) env (Idxd k_wf) ctx (Idxd k_s) =
  Idxd (vcrstmt cnst s_k env k_wf ctx k_s)
vcrstmt cnst (Idxi s_k) env (Idxi k_wf) ctx (Idxi k_s) =
  Idxi (vcrstmt cnst s_k env k_wf ctx k_s)
vcrstmt cnst (Aryd var len lenNZ s_k) (MkEnv nums idxs arys funs) (Aryd k_wf) (MkCtx nvals avals ok) (Aryd {avals'} {ok'} newAry k_s) =
  Aryd (vcrstmt cnst s_k (MkEnv nums idxs ((var,(len ** lenNZ)) :: arys) funs) k_wf (MkCtx nvals avals' ok') k_s)
vcrstmt cnst (Aryu var len lenNZ idx a s_k) (MkEnv nums idxs arys funs) (Aryu varinarys ubLTlen a_wf k_wf) (MkCtx nvals avals ok) (Aryu {avals'} {ok'} a_s newAry k_s) =
  Aryu (vcrstmt cnst s_k (MkEnv nums idxs arys funs) k_wf (MkCtx nvals avals' ok') k_s)
vcrstmt cnst Stop env Stop ctx Stop = Stop

vcrstmt {cong=eq} {set=MkSetoid c zero (MkPropEq eq refl sym trans set_eq p) defnEq agree1 agree2} cnst (Cert b s_k) env (Cert b_wf k_wf) ctx (Cert val b_s k_s) =
  case hasOrdering cnst of
    Yes ord =>
      OrdCert ord (isOrdVCRBExp cnst b env b_wf ctx b_s) (vcrstmt cnst s_k env k_wf ctx k_s)
    No nord => 
      Cert nord (isOrdVCRBExp cnst b env b_wf ctx b_s) (vcrstmt cnst s_k env k_wf ctx k_s)
