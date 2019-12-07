module EnvCtxUtil

import public CPStmt

%default total
%access public export

-- [Utility] --------------------------------------------------------------------------------------

implementation Uninhabited (Here = (There later)) where
  uninhabited Refl impossible

implementation DecEq (Elem x xs) where
  decEq Here Here = Yes Refl
  decEq Here (There later) = No absurd
  decEq (There later) Here = No (absurd . sym)
  decEq (There later) (There subsequent) with (decEq later subsequent)
    decEq (There later) (There subsequent) | (Yes prf) = Yes (cong prf)
    decEq (There later) (There subsequent) | (No contra) = No (\Refl => contra Refl)

implementation DecEq (DPair Nat NotZero) where
  decEq ((S n) ** MkNotZero) ((S m) ** MkNotZero) with (decEq n m)
    decEq ((S m) ** MkNotZero) ((S m) ** MkNotZero) | Yes Refl = Yes Refl
    decEq ((S n) ** MkNotZero) ((S m) ** MkNotZero) | No contra = No (\Refl => contra Refl)

natToFin : (k : Nat) -> (ub : Nat) -> (ok : LT k ub) -> Fin ub
natToFin Z (S Z) (LTESucc x) = FZ
natToFin Z (S (S k)) (LTESucc x) = FZ
natToFin (S k) (S right) (LTESucc x) = FS (natToFin k right x)

data Tree : (c : Type) -> Type where
  Leaf : (x : c) -> Tree c
  Node : (left : Tree c) -> (right : Tree c) -> Tree c

-- [Environment] ----------------------------------------------------------------------------------

||| A list of variables that are in scope. (Variables that have been declared.)
|||
||| @ns numeric variable symbols
||| @as array variable symbols
data Env : (vs : VarSet ns is as fs)
        -> Type where
  MkEnv : {vs : VarSet ns is as fs}
       -> (nums : Vect n' (Elem NumVar ns))
       -> (idxs : Vect k' (Elem IdxVar is))
       -> (arys : Vect m' ((Elem AryVar as, (len ** NotZero len))))
       -> (funs : Vect s' (Elem FunVar fs))
       -> Env vs

-- [Index Context] -------------------------------------------------------------------------------

||| Context for indices variable symbols.
||| Invariant at expression level, inferred (statically) at the statement level.
|||
||| Think `(zip idxs' idxbounds)`.
|||
||| Indices are mapped (here) to an upper and lower bound because we have loops.
data IdxCtx : (vs : VarSet ns is as fs) -> (env : Env vs) -> Type where
  ||| .
  ||| @idxs .
  MkIdxCtx : {idxs : Vect i (Elem IdxVar is)}
          -> (idxbounds : Vect i Nat)
          -> IdxCtx (MkVarSet ns is as fs) (MkEnv nums idxs arys funs)

||| Relates an index variable symbol in the environment to its value in the context.
data ArrIdxBounds : (idxs' : Vect k' (Elem IdxVar idxs))
                 -> (ubs : Vect k' Nat)
                 -> (idxinenv : Elem idx idxs')
                 -> (ub : Nat)
                 -> Type where
  Here : ArrIdxBounds (idx :: idxs') (ub :: ubs) Here ub
  There : (laterArr : ArrIdxBounds idxs' ubs later ub)
       -> ArrIdxBounds (i :: idxs') (b :: ubs) (There later) ub

arrIdxBounds : (idxs' : Vect k' (Elem IdxVar idxs))
            -> (ubs : Vect k' Nat)
            -> (idxinenv : Elem idx idxs')
            -> (ub : Nat ** ArrIdxBounds idxs' ubs idxinenv ub)
arrIdxBounds (idx :: idxs') (ub :: ubs) Here = (ub ** Here)
arrIdxBounds (i :: idxs') (b :: ubs) (There later) with (arrIdxBounds idxs' ubs later)
  | (ub ** laterArr) = (ub ** There laterArr)

lemma_same_ub_two_ArrIdxBounds : (arr1 : ArrIdxBounds idxs' ubs idxinenv ub1)
                              -> (arr2 : ArrIdxBounds idxs' ubs idxinenv ub2)
                              -> (arr1 = arr2)
lemma_same_ub_two_ArrIdxBounds Here Here = Refl
lemma_same_ub_two_ArrIdxBounds (There laterArr1) (There laterArr2)
  with (lemma_same_ub_two_ArrIdxBounds laterArr1 laterArr2)
    lemma_same_ub_two_ArrIdxBounds (There laterArr2) (There laterArr2) | Refl = Refl

-- [Numeric & Array Context] ----------------------------------------------------------------------

{-
data SumLen : (arys : Vect m (Elem AryVar as, (len ** NotZero len))) -> (s : Nat) -> Type where
  Nil : SumLen [] Z
  Cons : (tl : SumLen arys s) -> SumLen ((elem, (l ** nZ)) :: arys) (l + s)

sumLen : (arys : Vect m (Elem AryVar as, (len ** NotZero len))) -> (s ** SumLen arys s)
sumLen [] = (Z ** Nil)
sumLen ((elem, (l ** nZ)) :: arys) with (sumLen arys)
  | (s ** arysSL) = (l + s ** Cons arysSL)
-}

||| Proof that the nested vectors in `avals` have the lengths specified in `arys`.
data StructSame : (arys : Vect m (Elem AryVar as, (len ** NotZero len)))
               -> (avals : Vect m (s ** Vect s c))
               -> Type where
  Nil : StructSame [] []
  Cons : (leqs : l = s)
      -> (tl : StructSame arys avals)
      -> StructSame ((elem, (l ** lNZ)) :: arys) ((s ** vect) :: avals)

isStructSame : (arys : Vect m (Elem AryVar as, (len ** NotZero len)))
            -> (avals : Vect m (s ** Vect s c))
            -> Dec (StructSame arys avals)
isStructSame [] [] = Yes Nil
isStructSame ((elem, (l ** lNZ)) :: arys) ((s ** vect) :: avals) with (decEq l s)
  isStructSame ((elem, (l ** lNZ)) :: arys) ((s ** vect) :: avals) | No lneqs =
    No (\(Cons leqs tl) => lneqs leqs)
  isStructSame ((elem, (s ** lNZ)) :: arys) ((s ** vect) :: avals) | Yes Refl
    with (isStructSame arys avals)
      | No notSS = No (\(Cons leqs tl) => notSS tl)
      | Yes isSS = Yes (Cons Refl isSS)


||| A fancy zip: the nth element in nums' is paired with the nth element in nvals.
data Ctx : (c : Type)
        -> (env : Env vs)
        -- -> (nvals : Vect n c)
        -- -> (avals : Vect m (s ** Vect s c)) -- length is (sum lengths arys')
        -> Type where
  MkCtx : {nums : Vect n (Elem NumVar ns)}
       -> {arys : Vect m (Elem AryVar as, (len ** NotZero len))}
       -> (nvals : Vect n c)
       -> (avals : Vect m (s ** Vect s c))
       -> (ok : StructSame arys avals) -- proof that structures are same
       -> Ctx c (MkEnv nums idxs arys funs) -- nvals avals

namespace NumVar
  data ArrVarC : (nums : Vect n' (Elem NumVar ns))
              -> (vals : Vect n' c)
              -> (varinnums : Elem var nums)
              -> (val : c)
              -> Type where
    Here : ArrVarC (var :: nums) (val :: vals) Here val
    There : (laterArr : ArrVarC nums vals later val)
         -> ArrVarC (v :: nums) (n :: vals) (There later) val

  arrVarC : (nums : Vect n' (Elem NumVar ns))
         -> (vals : Vect n' c)
         -> (varinnums : Elem var nums)
         -> (val : c ** ArrVarC nums vals varinnums val)
  arrVarC (var :: nums) (val :: vals) Here = (val ** Here)
  arrVarC (v :: nums) (n :: vals) (There later) with (arrVarC nums vals later)
    | (val ** laterArr) = (val ** There laterArr)

namespace AryVar
  data ArrVarIdxC : (arys : Vect m (Elem AryVar as, (len ** NotZero len)))
                 -> (avals : Vect m (s ** Vect s c))
                 -> (structSame : StructSame arys avals)
                 -> (varinarys : Elem (var, (l ** lNZ)) arys)
                 -> (idx : Fin l)
                 -> (val : c)
                 -> Type where
    Here : ArrVarIdxC ((var, (l ** lNZ)) :: arys) ((l ** cs) :: avals) (Cons Refl tl) Here idx (index idx cs)
    There : (laterArr : ArrVarIdxC arys avals tl later idx val)
         -> ArrVarIdxC ((v,(l ** lNZ)) :: arys) ((s ** n) :: avals) (Cons leqs tl) (There later) idx val
  
  arrVarIdxC : (arys : Vect m (Elem AryVar as, (len ** NotZero len)))
            -> (avals : Vect m (s ** Vect s c))
            -> (structSame : StructSame arys avals)
            -> (varinarys : Elem (var, (l ** lNZ)) arys)
            -> (idx : Fin l)
            -> (val : c ** ArrVarIdxC arys avals structSame varinarys idx val)
  arrVarIdxC ((var,(l ** lNZ))::arys) ((l ** cs)::avals) (Cons Refl tl) Here idx =
    (index idx cs ** Here)
  arrVarIdxC ((v,(l ** lNZ))::arys) ((s ** cs)::avals) (Cons leqs tl) (There later) idx
    with (arrVarIdxC arys avals tl later idx)
      | (val ** laterArr) = (val ** There laterArr)
