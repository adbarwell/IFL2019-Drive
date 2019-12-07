module Syntax

import public Data.So
import public Data.Vect

%default total
%access public export

-- [Variable Representation] ----------------------------------------------------------------------

namespace Variable
  data VarKind : Type where
    Numerical : VarKind
    Index : VarKind
    Array : VarKind
    Function : VarKind

  data NotZero : (n : Nat) -> Type where
    MkNotZero : NotZero (S k)

  implementation Uninhabited (NotZero Z) where
    uninhabited MkNotZero impossible

  data Var : (ty : VarKind) -> Type where
    NumVar : Var Numerical
    IdxVar : Var Index
    AryVar : Var Array
    FunVar : Var Function

  data VarSet : (numvs : Vect n (Var Numerical))
             -> (idxvs : Vect k (Var Index))
             -> (aryvs : Vect m (Var Array))
             -> (funvs : Vect s (Var Function))
             -> Type where
    MkVarSet : (numvs : Vect n (Var Numerical))
            -> (idxvs : Vect k (Var Index))
            -> (aryvs : Vect m (Var Array))
            -> (funvs : Vect s (Var Function))
            -> VarSet numvs idxvs aryvs funvs

-- [Basic Assumptions] ----------------------------------------------------------------------------

data PropEq : (c : Type) -> (cong : c -> c -> Type) -> Type where
  MkPropEq : (cong  : c -> c -> Type)
          -> (refl  : (x : c) -> cong x x)
          -> (sym   : {a : c} -> {b : c} -> cong a b -> cong b a)
          -> (trans : {w : c} -> {y : c} -> {z : c} -> cong w y -> cong y z -> cong w z)
          -> (set_cong : (i : c) -> (j : c) -> Dec (cong i j))
          -> (cong_preserves_cong : (t : c) -> (s : c) -> (c1 : c) -> (c2 : c)
                                 -> (cong t c1) -> (cong s c2) -> (cong c1 c2) -> cong t s)
          -> PropEq c cong

||| We require that cong iff equiv, so we don't need to prove all the properties again.
data DefnEq : (c : Type) -> Type where
  MkDefnEq : (equiv  : c -> c -> Bool)
          -- -> (sym   : (a : c) -> (b : c) -> So (equiv a b) -> So (equiv b a))
          -- -> (trans : (w : c) -> (y : c) -> (z : c)
          --          -> So (equiv w y) -> So (equiv y z) -> So (equiv w z))
          -- -> (equiv_preserves_equiv : (t : c) -> (s : c) -> (c1 : c) -> (c2 : c)
          --                          -> So (equiv t c1) -> So (equiv s c2) -> So (equiv c1 c2)
          --                          -> So (equiv t s))
          -> DefnEq c -- equiv

namespace DefnEq
  ProjEquiv : DefnEq c -> (c -> c -> Bool)
  ProjEquiv (MkDefnEq equiv) = equiv

data Setoid : (c : Type) -> (cong : c -> c -> Type) -> Type where
  ||| .
  ||| @zero default value array elements upon declaration.
  MkSetoid : (c : Type)
          -> (zero : c)
          -> {cong : c -> c -> Type}
          -> (propEq : PropEq c cong)
          -> (defnEq : DefnEq c)
          -> (cong_equiv_agree : (x : c) -> (y : c) -> (cong x y) -> So (ProjEquiv defnEq x y))
          -> (equiv_cong_agree : (x : c) -> (y : c) -> So (ProjEquiv defnEq x y) -> cong x y)
          -> Setoid c cong

namespace Setoid
  ProjEquiv : {cong : c -> c -> Type} -> Setoid c cong -> (c -> c -> Bool)
  ProjEquiv (MkSetoid c zero propEq defnEq agree1 agree2) = ProjEquiv defnEq

-- [Algebraic Structures] -------------------------------------------------------------------------

namespace Kinds
  data StructKind : Type where
    Magma : StructKind
    Semigroup : StructKind
    Monoid : StructKind
    Group : StructKind
    AbelianGroup : StructKind
    Ring : StructKind
    -- OrdMagma : StructKind
    OrdSemigroup : StructKind

  ||| With total ordered sets this is now a *partial* ordering over StructKind
  data GT : StructKind -> StructKind -> Type where
    SgpMg : GT Semigroup Magma
    MndMg : GT Monoid Magma
    GrpMg : GT Group Magma
    AGpMg : GT AbelianGroup Magma
    RngMg : GT Ring Magma
    -- OMgMg : GT OrdMagma Magma
    -- OSgMg : GT OrdSemigroup Magma
    MndSgp : GT Monoid Semigroup
    GrpSgp : GT Group Semigroup
    AGpSgp : GT AbelianGroup Semigroup
    RngSgp : GT Ring Semigroup
    -- OSgSgp : GT OrdSemigroup Semigroup
    GrpMnd : GT Group Monoid
    AGpMnd : GT AbelianGroup Monoid
    RngMnd : GT Ring Monoid
    AGpGrp : GT AbelianGroup Group
    RngAGp : GT Ring AbelianGroup
    -- OgSgMg : GT OrdSemigroup OrdMagma

data BinOp : (c : Type) -> (set : Setoid c eq) -> Type where
  MkBinOp : {set : Setoid c eq}
         -> (op : c -> c -> c)
         -> (op_preserves_cong : (x,y,c1,c2 : c) -> (eq x c1) -> (eq y c2)
                             -> (eq (op x y) (op c1 c2)))
         -> BinOp c set
  
data Associativity : (c : Type) -> (set : Setoid c eq) -> (BinOp c set) -> Type where
  MkAssociativity : {set : Setoid c eq}
                 -> ((x : c) -> (y : c) -> (z : c) -> eq (op (op x y) z) (op x (op y z)))
                 -> Associativity c set (MkBinOp op p)

data Identity : (c : Type) -> (set : Setoid c eq) -> (BinOp c set) -> Type where
  MkIdentity : {set : Setoid c eq}
            -> (e : c) -> (eq (op e x) (op x e)) -> (eq (op x e) x) -> Identity c set (MkBinOp op p)

data Inverse : (c : Type)
            -> (set : Setoid c eq)
            -> (binop : BinOp c set)
            -> (Identity c set binop)
            -> Type where
  MkInverse : {set : Setoid c eq}
            -> (neg : c -> c)
            -> (eq (op x (neg x)) e)
            -> Inverse c set (MkBinOp op p) (MkIdentity e p1 p2)

data Commutativity : (c : Type) -> (set : Setoid c eq) -> (binop : BinOp c set) -> Type where
  MkCommutativity : {set : Setoid c eq}
                 -> (eq (op x y) (op y x)) -> Commutativity c set (MkBinOp op p)

data Distributive : (c : Type)
                  -> (set : Setoid c eq)
                  -> (plus : BinOp c set)
                  -> (mul : BinOp c set)
                  -> Type where
  MkDistributive : {set : Setoid c eq}
                -> (eq (mul x (add y z)) (add (mul x y) (mul x z)))
                -> (eq (mul (add y z) x) (add (mul y x) (mul z x)))
                -> Distributive c set (MkBinOp add padd) (MkBinOp mul pmul)

||| Probably missing proofs here...
data TotalOrder : (c : Type) -> (set : Setoid c eq) -> Type where
  MkTotalOrder : (lte : (i : c) -> (j : c) -> Type)
              -> (is_lte : (i : c) -> (j : c) -> Dec (lte i j))
              -> (def_lte : (i : c) -> (j : c) -> Bool)
              -- -> (agree1 : (i : c) -> (j : c) -> (lte i j))
              -> TotalOrder c set

mutual
  data Struct : (c : Type) -> (set : Setoid c eq) -> (kind : StructKind) -> Type where
    Magma        : (set : Setoid c eq) -> (binop : BinOp c set) -> Struct c set Magma
    Semigroup    : (magma : Struct c set Magma)
                -> (assoc : Associativity c set (projPlus magma))
                -> Struct c set Semigroup
    Monoid       : (sgp : Struct c set Semigroup)
                -> (id : Identity c set (projPlus sgp))
                -> Struct c set Monoid
    Group        : (mnd : Struct c set Monoid)
                -> (inv : Inverse c set (projPlus mnd) (projId mnd MndSgp))
                -> Struct c set Group
    AbelianGroup : (grp : Struct c set Group)
                -> (comm : Commutativity c set (projPlus grp))
                -> Struct c set AbelianGroup
    Ring         : (agp : Struct c set AbelianGroup)
                -> (mul : BinOp c set)
                -> (mulAssoc : Associativity c set mul)
                -> (mulId : Identity c set mul)
                -> (dist : Distributive c set (projPlus agp) mul)
                -> Struct c set Ring
    -- OrdMagma : (magma : Struct c set Magma)
    --         -> (ord : TotalOrder c set)
    --         -> Struct c set OrdMagma
    OrdSemigroup : (sgp : Struct c set Semigroup)
                -> (ord : TotalOrder c set)
                -> Struct c set OrdSemigroup

  projPlus : Struct c set kind -> BinOp c set
  projPlus (Magma set addition) = addition
  projPlus (Semigroup magma assoc) = projPlus magma
  projPlus (Monoid sgp id) = projPlus sgp
  projPlus (Group mnd inv) = projPlus mnd
  projPlus (AbelianGroup grp comm) = projPlus grp
  projPlus (Ring agp mul mulAssoc mulId dist) = projPlus agp
  projPlus (OrdSemigroup sgp ord) = projPlus sgp

  projId : (struct : Struct c set kind) -> GT kind Semigroup -> Identity c set (projPlus struct)
  projId (Monoid sgp id) MndSgp = id
  projId (Group mnd inv) GrpSgp = projId mnd MndSgp
  projId (AbelianGroup grp comm) AGpSgp = projId grp GrpSgp
  projId (Ring agp mul mulAssoc mulId dist) RngSgp = projId agp AGpSgp

ArrBinOp : (cnst : Struct c set kind)
        -> BinOp c set
ArrBinOp (Magma set binop) = binop -- ???
ArrBinOp (Semigroup magma assoc) = projPlus magma
ArrBinOp (Monoid sgp id) = projPlus sgp
ArrBinOp (Group mnd inv) = projPlus mnd
ArrBinOp (AbelianGroup grp comm) = projPlus grp
ArrBinOp (Ring agp mul mulAssoc mulId dist) = projPlus agp
ArrBinOp (OrdSemigroup sgp ord) = projPlus sgp

ArrIdentity : (cnst : Struct c set kind)
           -> (ok : GT kind Semigroup)
           -> Identity c set (ArrBinOp cnst)
ArrIdentity (Monoid sgp id) MndSgp = id -- ???
ArrIdentity (Group mnd inv) GrpSgp = projId mnd MndSgp
ArrIdentity (AbelianGroup grp comm) AGpSgp = projId grp GrpSgp
ArrIdentity (Ring agp mul mulAssoc mulId dist) RngSgp = projId agp AGpSgp

WeakenGTMonoidToGTSemigroup : (ok : GT kind Monoid) -> GT kind Semigroup
WeakenGTMonoidToGTSemigroup GrpMnd = GrpSgp
WeakenGTMonoidToGTSemigroup AGpMnd = AGpSgp
WeakenGTMonoidToGTSemigroup RngMnd = RngSgp

projNeg : (cnst : Struct c set kind)
       -> (ok : GT kind Monoid)
       -> Inverse c set (ArrBinOp cnst) (ArrIdentity cnst (WeakenGTMonoidToGTSemigroup ok))
projNeg (Group mnd inv) GrpMnd = inv
projNeg (AbelianGroup grp comm) AGpMnd = projNeg grp GrpMnd
projNeg (Ring agp mul mulAssoc mulId dist) RngMnd = projNeg agp AGpMnd

projMul : (cnst : Struct c set kind)
       -> (ok : GT kind AbelianGroup)
       -> BinOp c set
projMul (Ring agp mul mulAssoc mulId dist) RngAGp = mul

projSet : {cong : c -> c -> Type} -> {set : Setoid c cong} -> (cnst : Struct c set kind)
       -> Setoid c cong
projSet {set} cnst = set

inverseFn : Inverse c set binop id -> (c -> c)
inverseFn (MkInverse neg p) = neg

binOpFn : BinOp c set -> (c -> c -> c)
binOpFn (MkBinOp op p) = op

setPropFn : {cong : c -> c -> Type} -> Setoid c cong -> ((x : c) -> (y : c) -> Dec (cong x y))
setPropFn (MkSetoid c zero (MkPropEq cong refl sym trans set_cong cong_preserves_cong) defnEq agree1 agree2) =
  set_cong

setDefnFn : {cong : c -> c -> Type} -> (set : Setoid c cong) -> (c -> c -> Bool)
setDefnFn (MkSetoid c zero propEq (MkDefnEq equiv) agree1 agree2) = equiv

zeroFn : {cong : c -> c -> Type} -> {set : Setoid c cong} -> (struct : Struct c set kind) -> c
zeroFn {set=(MkSetoid c zero propEq defnEq agree1 agree2)} struct = zero

namespace Ordering
  data HasOrdering : (kind : StructKind) -> Type where
    -- OrdMagma : HasOrdering OrdMagma
    OrdSemigroup : HasOrdering OrdSemigroup

projLTE : (struct : Struct c set kind)
       -> (ok : HasOrdering kind)
       -> ((i : c) -> (j : c) -> Type)
projLTE (OrdSemigroup sgp (MkTotalOrder lte is_lte def_lte)) OrdSemigroup = lte

projIsLTE : (struct : Struct c set kind)
         -> (ok : HasOrdering kind)
         -> ((i : c) -> (j : c) -> Dec (projLTE struct ok i j))
projIsLTE (OrdSemigroup sgp (MkTotalOrder lte is_lte def_lte)) OrdSemigroup = is_lte

projDefLTE : (struct : Struct c set kind)
          -> (ok : HasOrdering kind)
          -> ((i : c) -> (j : c) -> Bool)
projDefLTE (OrdSemigroup sgp (MkTotalOrder lte is_lte def_lte)) OrdSemigroup = def_lte

-- [Arithmetic Expressions] -----------------------------------------------------------------------

data AExp : (c : Type) -> (cnst : Struct c set kind) -> (vs : VarSet ns is as fs) -> Type where
  Val : (n : c) -> AExp c cnst vs
  Var : {vs : VarSet ns is as fs} -> (var : Elem NumVar ns) -> AExp c cnst vs
  Acc : {vs : VarSet ns is as fs}
     -> (var : Elem AryVar as) -> (len : Nat) -> (idx : Elem IdxVar is) -> AExp c cnst vs
  Neg : {cnst : Struct c set kind}
     -> (a : AExp c cnst vs) -> (ok : GT kind Monoid) -> AExp c cnst vs
  Add : (a1 : AExp c cnst vs) -> (a2 : AExp c cnst vs) -> AExp c cnst vs
  Mul : {cnst : Struct c set kind}
     -> (a1 : AExp c cnst vs) -> (a2 : AExp c cnst vs) -> (GT kind AbelianGroup) -> AExp c cnst vs

-- [Boolean Expressions] --------------------------------------------------------------------------

data BExp : (c : Type) -> (cnst : Struct c set kind) -> (vs : VarSet ns is as fs) -> Type where
  Eq : (a1 : AExp c cnst vs) -> (a2 : AExp c cnst vs) -> BExp c cnst vs
  LTE : {cnst : Struct c set kind}
     -> (a1 : AExp c cnst vs) -> (a2 : AExp c cnst vs) -> (HasOrdering kind) -> BExp c cnst vs


-- [Statements] -----------------------------------------------------------------------------------

data Stmt : (c : Type) -> (cnst : Struct c set kind) -> (vs : VarSet ns is as fs) -> Type where
  Assn : (var : Elem NumVar ns) -> (a : AExp c cnst (MkVarSet ns is as fs))
      -> Stmt c cnst (MkVarSet ns is as fs)
  ||| Declare index variable (set to Z).
  Idxd : (idx : Elem IdxVar is) -> Stmt c cnst (MkVarSet ns is as fs)
  ||| Increment index variable by one.
  Idxi : (idx : Elem IdxVar is) -> Stmt c cnst (MkVarSet ns is as fs)
  ||| Declare fixed-length array.
  Aryd : (var : Elem AryVar as)
      -> (len : Nat)
      -> (lenNZ : NotZero len)
      -> Stmt c cnst (MkVarSet ns is as fs)
  ||| Update element of array.
  Aryu : (var : Elem AryVar as)
      -> (len : Nat)
      -> (lenNZ : NotZero len)
      -> (idx : Elem IdxVar is)
      -> (a : AExp c cnst (MkVarSet ns is as fs))
      -> Stmt c cnst (MkVarSet ns is as fs)
  ||| Only true branch in order to avoid needing to unioning environments in LoopUnrolling.
  ||| Unioning environments is painful because we are using vectors.
  Iftt : (b : BExp c cnst vs)
      -> (s_tt : Stmt c cnst vs)
      -> Stmt c cnst vs
  Iter : (var : Elem NumVar ns)
      -> (idx : Elem IdxVar is)
      -> (ary : Elem AryVar as)
      -> (len : Nat)
      -> (lenNZ : NotZero len)
      -> (s : Stmt c cnst (MkVarSet ns is as fs))
      -> Stmt c cnst (MkVarSet ns is as fs)

  Comp : (s_1 : Stmt c cnst vs) -> (s_2 : Stmt c cnst vs) -> Stmt c cnst vs

  -- CSLCAnn : (fun : Elem FunVar fs)
  --        -> (s : Stmt c cnst (MkVarSet ns is as fs))
  --        -> Stmt c cnst (MkVarSet ns is as fs)

  Cert : (b : BExp c cnst vs) -> Stmt c cnst vs

-- [Program] --------------------------------------------------------------------------------------

data Prog : (c : Type) -> (cnst : Struct c set kind) -> (vs : VarSet ns is as fs) -> Type where
  MkProg : (s_0 : Stmt c cnst vs) -> Prog c cnst vs

