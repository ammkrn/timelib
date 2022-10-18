import Mathlib.Init.Data.Int.Order
import Timelib.Util
import Timelib.Date.ScalarDate
import Timelib.Date.Month
import Timelib.SignedInt

structure SignedDuration (siPow : Int) where
  val : Int
deriving DecidableEq, Ord, Hashable, Repr

section base
variable {siPow : Int}
def SignedDuration.isNeg (d : SignedDuration siPow) : Bool := d.val < 0
def SignedDuration.isNonNeg (d : SignedDuration siPow) : Bool := ¬d.isNeg
def SignedDuration.abs (d : SignedDuration siPow) : SignedDuration siPow := SignedDuration.mk (d.val.natAbs)

instance : Neg (SignedDuration siPow) where
  neg d := ⟨-d.val⟩ 

theorem SignedDuration.neg_def (d : SignedDuration siPow) : -d = ⟨-d.val⟩ := by rfl


instance : Add (SignedDuration siPow) where
  add a b := ⟨a.val + b.val⟩ 

theorem SignedDuration.add_def (a b : SignedDuration siPow) : a + b = ⟨a.val + b.val⟩ := rfl

instance : Sub (SignedDuration siPow) where
  sub a b := ⟨a.val - b.val⟩ 

theorem SignedDuration.sub_def (a b :  SignedDuration siPow) : a - b = ⟨a.val - b.val⟩ := rfl

instance : HMul (SignedDuration siPow) Nat (SignedDuration siPow) where
  hMul d n := ⟨d.val * n⟩ 

instance : HMod (SignedDuration siPow) Int (SignedDuration siPow) where
  hMod a n := ⟨a.val % n⟩ 

instance : HDiv (SignedDuration siPow) Nat (SignedDuration siPow) where
  hDiv a b := ⟨a.val / b⟩ 

instance : HPow (SignedDuration siPow) Nat (SignedDuration siPow) where
  hPow a b := ⟨a.val ^ b⟩ 

instance : LT (SignedDuration siPow) where
  lt := InvImage Int.lt SignedDuration.val

instance : LE (SignedDuration siPow) where
  le := InvImage Int.le SignedDuration.val

theorem SignedDuration.le_def {d₁ d₂ : SignedDuration siPow} : (d₁ <= d₂) = (d₁.val <= d₂.val) := rfl
theorem SignedDuration.lt_def {d₁ d₂ : SignedDuration siPow} : (d₁ < d₂) = (d₁.val < d₂.val) := rfl

theorem SignedDuration.val_eq_of_eq : ∀ {d1 d2 : SignedDuration siPow} (h : d1 = d2), d1.val = d2.val
| ⟨_⟩, _, rfl => rfl

theorem SignedDuration.eq_of_val_eq : ∀ {d1 d2 : SignedDuration siPow} (h : d1.val = d2.val), d1 = d2
| ⟨_⟩, _, rfl => rfl

instance (a b : SignedDuration siPow) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : SignedDuration siPow) : Decidable (a <= b) := inferInstanceAs (Decidable (a.val <= b.val))

instance : LinearOrder (SignedDuration siPow) where
  le_refl (a) := le_refl a.val
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply SignedDuration.eq_of_val_eq
    rw [SignedDuration.le_def] at h2 h1
    exact le_antisymm h1 h2
  le_total := by simp [SignedDuration.le_def, le_total]
  decidable_le := inferInstance

theorem SignedDuration.monotone {d₁ d₂ : SignedDuration siPow} : d₁.val <= d₂.val -> d₁ <= d₂ := 
  fun h => (SignedDuration.le_def) ▸ h
  
instance (n : Nat) : OfNat (SignedDuration siPow) n where
  ofNat := ⟨n⟩ 

@[simp] theorem SignedDuration.zero_def : (0 : SignedDuration siPow).val = (0 : Int) := by rfl

instance : AddCommSemigroup (SignedDuration siPow) := {
  add_assoc := fun a b c => by simp [SignedDuration.add_def, AddSemigroup.add_assoc]
  add_comm := fun a b => by simp [SignedDuration.add_def]; exact AddCommSemigroup.add_comm (A := Int) _ _
}

instance : IsAddLeftCancel (SignedDuration siPow) where
  add_left_cancel := fun a b c h0 => by
    have h2 := SignedDuration.val_eq_of_eq h0
    simp only [SignedDuration.val] at h2
    exact SignedDuration.eq_of_val_eq (@Int.add_left_cancel a.val b.val c.val (h2))
  
instance : IsAddRightCancel (SignedDuration siPow) where
  add_right_cancel := fun a b c => by
    have h0 := @add_right_cancel Int _ _ a.val b.val c.val
    intro h1
    have h2 := SignedDuration.val_eq_of_eq h1
    simp only [SignedDuration.add_def, SignedDuration.val] at h2
    specialize h0 h2
    exact SignedDuration.eq_of_val_eq h0

instance : AddCommMonoid (SignedDuration siPow) where
  add_zero := by simp [SignedDuration.eq_of_val_eq, SignedDuration.add_def, add_zero]
  zero_add := by simp [SignedDuration.eq_of_val_eq, SignedDuration.add_def, zero_add]
  nsmul_zero' := by simp [nsmul_rec]
  nsmul_succ' := by simp [nsmul_rec]
  add_comm := by simp [SignedDuration.eq_of_val_eq, SignedDuration.add_def, add_comm]

instance : Equiv Int (SignedDuration siPow) where
  toFun := SignedDuration.mk
  invFun := SignedDuration.val
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

instance : AddMonoidWithOne (SignedDuration siPow) where
  __ := inferInstanceAs (AddCommMonoid (SignedDuration siPow))
  natCast n := SignedDuration.mk (Int.ofNat n)
  natCast_zero := rfl
  natCast_succ _ := rfl

private theorem SignedDuration.sub_eq_add_neg (a b : SignedDuration siPow) : a - b = a + -b := by
  simp [
    SignedDuration.sub_def, SignedDuration.add_def, SignedDuration.neg_def,
    HSub.hSub, Sub.sub, Int.sub
  ]

private theorem SignedDuration.add_left_neg (a : SignedDuration siPow) : -a + a = 0 := by
  apply SignedDuration.eq_of_val_eq
  simp [SignedDuration.sub_def, SignedDuration.add_def, SignedDuration.neg_def]

instance : AddGroupWithOne (SignedDuration siPow) where
  __ := inferInstanceAs (AddMonoidWithOne (SignedDuration siPow))
  gsmul_zero' := by simp [gsmul_rec, nsmul_rec]
  gsmul_succ' := by simp [gsmul_rec, nsmul_rec, -Int.ofNat_eq_cast]
  gsmul_neg' := by simp [gsmul_rec, nsmul_rec, -Int.ofNat_eq_cast]
  sub_eq_add_neg := SignedDuration.sub_eq_add_neg
  add_left_neg := SignedDuration.add_left_neg
  intCast := SignedDuration.mk
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

end base

namespace SecondPrecision
@[reducible] def SignedDuration := _root_.SignedDuration 0

instance : AddGroupWithOne (SecondPrecision.SignedDuration) := inferInstance

end SecondPrecision

namespace NanoPrecision
@[reducible] def SignedDuration := _root_.SignedDuration (-9)
instance : AddGroupWithOne (NanoPrecision.SignedDuration) := inferInstance
end NanoPrecision


namespace MilliPrecision
def SignedDuration := _root_.SignedDuration (-3)
end MilliPrecision

def SignedDuration.convertLossless 
  {fine coarse : Int} 
  (d : SignedDuration coarse) 
  (h : fine <= coarse := by decide) : 
  SignedDuration fine :=
    match coarse - fine, Int.sub_nonneg_of_le h with
    | Int.ofNat n, _ => ⟨d.val * (10 ^ n)⟩
    | Int.negSucc n, h_zero_le => 
      False.elim ((not_lt_of_ge h_zero_le) (Int.neg_succ_lt_zero n))

instance {n m : Int} (h : m <= n := by decide) : 
  Coe (SignedDuration n) (SignedDuration m) where
  coe d := SignedDuration.convertLossless d h


/-
These rounding conventions are placeholders for now, we will revisit them.
-/
/-
Lossy conversion using the `E` rounding convention; always rounding toward 0
-/
def SignedDuration.eConvertLossy 
  {fine coarse : Int} 
  (d : SignedDuration fine) 
  (h : fine <= coarse := by decide) : SignedDuration coarse :=
    match coarse - fine, Int.sub_nonneg_of_le h with
    | Int.ofNat n, _ => ⟨d.val / (10 ^ n)⟩
    | Int.negSucc n, h_zero_le => 
      False.elim ((not_lt_of_ge h_zero_le) (Int.neg_succ_lt_zero n))

/-
Lossy conversion using the `F` rounding convention
-/
def SignedDuration.fConvertLossy 
  {fine coarse : Int} 
  (d : SignedDuration fine) 
  (h : fine <= coarse := by decide) : SignedDuration coarse :=
    match coarse - fine, Int.sub_nonneg_of_le h with
    | Int.ofNat n, _ => ⟨d.val.fdiv (10 ^ n)⟩
    | Int.negSucc n, h_zero_le => 
      False.elim ((not_lt_of_ge h_zero_le) (Int.neg_succ_lt_zero n))


/-
Now implement signed duration on e.g. 64 bit signed integers at the second precision.
-/
namespace SecondPrecision
structure SignedDuration64 where
  val : Int64

def SignedDuration64.max : SignedDuration64 := ⟨Int64.max⟩
def SignedDuration64.min : SignedDuration64 := ⟨Int64.min⟩

def SignedDuration64.toSignedDuration (d : SignedDuration64) : SignedDuration :=
  ⟨d.val.toInt⟩

def SignedDuration64.fromSignedDuration (d : SignedDuration) : Option SignedDuration64 :=
  if d.val < SignedDuration64.min.val.toInt || d.val > SignedDuration64.max.val.toInt
  then none
  else some <| SignedDuration64.mk (Int64.ofInt d.val)
end SecondPrecision

-- 42 SI seconds
def secs : SignedDuration 0 := ⟨42⟩ 

def megaSecs : SignedDuration 6 := ⟨42⟩

-- 42 seconds to milliseconds
def millis : SignedDuration (-3) := secs.convertLossless
#eval millis

-- Convert the milliseconds back to seconds (lossy)
def millisAsSeconds : SignedDuration 0 := millis.eConvertLossy
#eval millisAsSeconds

-- 42 megaseconds to milliseconds
def millisOfMega : SignedDuration (-3) := megaSecs.convertLossless
#eval millisOfMega

-- Convert back to megaseconds
#eval (millisOfMega.fConvertLossy : SignedDuration 6)

def t1 : SecondPrecision.SignedDuration := ⟨10⟩
def t2 : NanoPrecision.SignedDuration := ⟨-2⟩

def t3 : NanoPrecision.SignedDuration := ⟨-2⟩
def t4 : NanoPrecision.SignedDuration := t1.convertLossless

structure NaiveDateTime (siPow : {z : Int // z <= 0}) where
  val : Int
deriving DecidableEq, Ord, Hashable, Repr, Lean.ToJson, Lean.FromJson
