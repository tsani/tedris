module NatToFin

import Data.Fin

public export
bump : (n : Nat ** LTE n m) -> (n' : Nat ** LTE n' (S m))
bump (n ** p) = (S n ** LTESucc p)

||| A recursive view representing a dependent pair of a Nat and a bounds-proof
||| as a sequence of "bumps"
public export
data Bumped : (n : Nat ** LTE n m) -> Type where
  Bottom : Bumped (id (Z ** LTEZero))
  BumpUp : Bumped e -> Bumped (bump e)

public export
bumped : (e : (n : Nat ** LTE n m)) -> Bumped e
bumped (Z ** LTEZero) = Bottom
bumped (S n ** LTESucc p) = BumpUp (bumped (n ** p))

-- bumped : (e : (n : Nat ** LTE n (S m))) -> Bumped e
-- bumped (Z ** LTEZero) = Bottom
-- bumped (S Z ** LTESucc LTEZero) {m=Z} = BumpUp Bottom
-- bumped (S (S n) ** LTESucc p) {m=Z} = ?b
-- bumped (S n ** LTESucc p) {m=S m} = let ih = bumped (n ** p) in ?c

||| Improved version of 'natToFin' that takes a proof that the given number is
||| within the bound. This eliminates the need for 'Maybe'.
public export
nat2Fin : (n : Nat ** LTE n m) -> Fin (S m)
nat2Fin (Z ** LTEZero) = FZ
nat2Fin (S n ** LTESucc p) = FS (nat2Fin (n ** p))

public export
nat2FinLT : (n : Nat ** LTE (S n) m) -> Fin m
nat2FinLT (Z ** LTESucc LTEZero) = FZ
nat2FinLT (S n ** LTESucc p) = FS (nat2FinLT (n ** p))

||| Improved version of 'finToNat' that provides a proof that the natural
||| returned is in the bound identified by the fin.
public export
fin2Nat : Fin (S m) -> (n : Nat ** LTE n m)
fin2Nat FZ = (Z ** LTEZero)
fin2Nat (FS f) {m=Z} = FinZElim f -- this case is impossible
fin2Nat (FS f) {m=S n} = bump (fin2Nat f)

public export
data FinAsNat : Fin (S m) -> Type where
  MkFinAsNat : (e : (n : Nat ** LTE n m)) -> FinAsNat (nat2Fin e)

||| View a 'Fin' as a natural number plus a proof
public export
finAsNat : (f : Fin (S m)) -> FinAsNat f
finAsNat FZ = MkFinAsNat (Z ** LTEZero)
finAsNat (FS f) {m=Z} = FinZElim f
  -- finAsNat (FS (nat2Fin e)) | (MkFinAsNat e) =
  --   MkFinAsNat (bump e)
finAsNat (FS f) {m=S m} =
  let (MkFinAsNat (n ** p)) = finAsNat f
      foo = MkFinAsNat (S n ** LTESucc p) in
      foo

public export
data NatAsFin : (n : Nat ** LTE n m) -> Type where
  MkNatAsFin : (f : Fin (S m)) -> NatAsFin (fin2Nat f)

public export
natAsFin : (e : (n : Nat ** LTE n m)) -> NatAsFin e
natAsFin e with (bumped e)
  natAsFin (id (Z ** LTEZero)) | Bottom = MkNatAsFin FZ
  natAsFin (bump x) | (BumpUp y) with (natAsFin x | y)
    natAsFin (bump (fin2Nat f)) | (BumpUp y) | (MkNatAsFin f) =
      MkNatAsFin (FS f)

public export
n2f2n : (e : (n : Nat ** LTE n m)) -> e = fin2Nat (nat2Fin e)
n2f2n e with (bumped e)
  n2f2n (id (Z ** LTEZero)) | Bottom = Refl
  n2f2n (bump x) | BumpUp y =
    let ih = n2f2n x | y in
        case x of
             (n ** p) => rewrite (sym ih) in Refl

public export
f2n2f : (f : Fin (S m)) -> (f = nat2Fin (fin2Nat f))
f2n2f f with (finAsNat f)
  f2n2f (nat2Fin e) | (MkFinAsNat e) =
    let lemma = n2f2n e in
        rewrite lemma in Refl
