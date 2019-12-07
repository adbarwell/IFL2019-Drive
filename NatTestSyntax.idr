module NatTestSyntax

import public Syntax

%default total
%access public export

-- [Var Rep] --------------------------------------------------------------------------------------

testVs : VarSet [NumVar,NumVar,NumVar,NumVar,NumVar] [IdxVar,IdxVar] [AryVar,AryVar] []
testVs = MkVarSet [NumVar,NumVar,NumVar,NumVar,NumVar] [IdxVar,IdxVar] [AryVar, AryVar] []

-- [Nat Semigroup] --------------------------------------------------------------------------------

namespace PropEq
  cong : Nat -> Nat -> Type
  cong = (=)

  refl : (x : Nat) -> cong x x
  refl x = Refl

  symNat : {a : Nat} -> {b : Nat} -> cong a b -> cong b a
  symNat Refl = Refl

  transNat : {w : Nat} -> {y : Nat} -> {z : Nat} -> cong w y -> cong y z -> cong w z
  transNat Refl Refl = Refl

  set_cong : (i : Nat) -> (j : Nat) -> Dec (cong i j)
  set_cong i j = decEq i j

  cong_preserves_cong : (t : Nat) -> (s : Nat) -> (c1 : Nat) -> (c2 : Nat)
                     -> (cong t c1) -> (cong s c2) -> (cong c1 c2) -> cong t s
  cong_preserves_cong x y x y Refl Refl p_x_y = p_x_y

  add_preserves_cong' : (c1,c2 : Nat) -> (cong (plus c1 c2) (plus c1 c2))
  add_preserves_cong' Z c2 = Refl
  add_preserves_cong' (S k) c2 = cong (add_preserves_cong' k c2)

  add_preserves_cong : (x,y,c1,c2 : Nat) -> (cong x c1) -> (cong y c2)
                    -> (cong (plus x y) (plus c1 c2))
  add_preserves_cong c1 c2 c1 c2 Refl Refl = add_preserves_cong' c1 c2 

namespace DefnEq
  equiv : Nat -> Nat -> Bool
  equiv Z Z = True
  equiv Z (S y) = False
  equiv (S x) Z = False
  equiv (S x) (S y) = equiv x y

  refl : (x : Nat) -> So (equiv x x)
  refl Z = Oh
  refl (S x) = refl x

  -- symNat : (a,b : Nat) -> So (equiv a b) -> So (equiv b a)
  -- symNat Z Z Oh = Oh
  -- symNat (S a) (S b) ok = symNat a b ok

  -- transNat : (w,y,z : Nat) -> So (equiv w y) -> So (equiv y z) -> So (equiv w z)
  -- transNat Z Z Z Oh Oh = Oh
  -- transNat (S w) (S y) (S z) okwy okyz = transNat w y z okwy okyz

  -- equiv_preserves_equiv : (t,s,c1,c2 : Nat)
  --                      -> So (equiv t c1) -> So (equiv s c2) -> So (equiv c1 c2) -> So (equiv t s)
  -- equiv_preserves_equiv Z Z Z Z Oh Oh Oh = Oh
  -- equiv_preserves_equiv (S t) (S s) (S c1) (S c2) oktc1 oksc2 okc1c2 =
  --   equiv_preserves_equiv t s c1 c2 oktc1 oksc2 okc1c2
  -- equiv_preserves_equiv t s c1 c2 oktc1 oksc2 okc1c2 = ?holeEquivPresEquivNat

propEqNat : PropEq Nat PropEq.cong
propEqNat = MkPropEq cong refl symNat transNat set_cong cong_preserves_cong

defnEqNat : DefnEq Nat
defnEqNat = MkDefnEq equiv -- symNat transNat equiv_preserves_equiv

agree1 : (x : Nat) -> (y : Nat) -> cong x y -> So (equiv x y)
agree1 y y Refl = refl y

agree2 : (x : Nat) -> (y : Nat) -> So (equiv x y) -> cong x y
agree2 Z Z Oh = Refl
agree2 (S x) (S y) oh = cong (agree2 x y oh)

setoidNat : Setoid Nat PropEq.cong
setoidNat = MkSetoid Nat 0 propEqNat defnEqNat agree1 agree2

sgpNat : Struct Nat NatTestSyntax.setoidNat Semigroup
sgpNat =
  Semigroup (Magma setoidNat (MkBinOp (Nat.plus) add_preserves_cong)) (MkAssociativity (\x, y, z => sym (plusAssociative x y z))) -- really need add_preserves_equiv as well...

totalOrderNat : TotalOrder Nat NatTestSyntax.setoidNat
totalOrderNat = MkTotalOrder (LTE) (isLTE) lte

ordNat : Struct Nat NatTestSyntax.setoidNat OrdSemigroup
ordNat = OrdSemigroup sgpNat totalOrderNat

  --- How much do we really need to prove about definitional equality?
  --- We're mostly interested in propositional equality,
  --- it's only in the semantics that we really care. Just state that this is future work.
  --- Explain that because they agree, we don't need to redefine them.

-- [Arith Exp] ------------------------------------------------------------------------------------

valAExpNatSgp : AExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
valAExpNatSgp = Val 42
varAExpNatSgp : AExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
varAExpNatSgp = Var (There Here)
accAExpNatSgp : AExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
accAExpNatSgp = Acc (There Here) 5 Here
addAExpNatSgp : AExp Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
addAExpNatSgp = Add valAExpNatSgp accAExpNatSgp

-- [Statements] -----------------------------------------------------------------------------------

{-
  x_2 := 42;
  dec i;
  i++;
  dec a^5_2;
  a^5_2[i] := 5;
  x_2 := a^5_2[i];
  x_1 := 0;
  if (x_2 = 5) then (x_1 := 1);
  x_3 := 0;
  if (x_2 = 42) then (x_3 := 1);
  dec a^2_1;
  dec j;
  x_4 := 0;
  for x_5 in a^2_1 do
    x_4 := x_4 + 1
-}

-- stmtNatSgp : Stmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
-- stmtNatSgp =
--   Comp (Assn (There Here) valAExpNatSgp) $
--   Comp (Idxd Here) $
--   Comp (Idxi Here) $
--   Comp (Aryd (There Here) 5 MkNotZero) $
--   Comp (Aryu (There Here) 5 MkNotZero Here (Val 5)) $
--   Comp (Assn (There Here) accAExpNatSgp) $
--   Comp (Assn Here (Val 0)) $
--   -- Comp (Iftt (Eq (Var (There Here)) (Val 5)) (Assn Here (Val 1))) $ -- true
--   Comp (Assn (There (There (Here))) (Val 0)) $
--   -- Comp (Iftt (Eq (Var (There Here)) (Val 42)) (Assn (There (There (Here))) (Val 1))) $ -- false
--   Comp (Aryd Here 2 MkNotZero) $
--   Comp (Idxd (There Here)) $
--   Comp (Assn (There (There (There Here))) (Val 0)) $
--   Iter (There (There (There (There Here)))) Here 2 MkNotZero $
--     Assn (There (There (There Here))) (Add (Var (There (There (There Here)))) (Val 0))

{-
  x_2 := 42;
  x_1 := 0;
  if (x_2 = 42) then (x_1 := 1);
  x_3 := 10;
-}
-- ifstmtNatSgp : Stmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
-- ifstmtNatSgp =
--   Comp (Assn (There Here) valAExpNatSgp) $
--   Comp (Assn Here (Val 0)) $
--   Comp (Iftt (Eq (Var (There Here)) (Val 42)) (Assn Here (Val 1))) $
--   (Assn (There (There Here)) (Val 10))


-- assnNatSgp : Stmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
-- assnNatSgp = Assn (There Here) valAExpNatSgp

-- certNatSgp : Stmt Nat NatTestSyntax.sgpNat NatTestSyntax.testVs
-- certNatSgp = 
--   Comp (Assn (There Here) valAExpNatSgp) $
--   Comp (Cert (Eq (Var (There Here)) (Val 42))) $
--   Cert (Eq (Var (There Here)) (Val 5))

-- ordNatSgp : Stmt Nat NatTestSyntax.ordNat NatTestSyntax.testVs
-- ordNatSgp = 
--   Comp (Assn (There Here) (Val 42)) $
--   Cert (LTE (Val 42) (Var (There Here)) OrdSemigroup)
