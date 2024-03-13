import Timelib.Util
import Timelib.SignedInt
import Mathlib.Init.Order.Defs
import Mathlib.Data.List.Lex

namespace Timelib

/--
This currently accepts just an `Int` as the precision, which is more versatile,
but because `DateTime` elements demand a `NegSiPow`, there ends up being some coercion
which doesn't always play nicely with typeclass resolution which is based on unification.

The assumption is that in practice, users will not frequently be mixing precisions, and
when they do, they can live with adding a coercion if they want to use notation.
-/
structure SignedDuration (siPow : Int) where
  val : Int
deriving DecidableEq, Ord, Hashable, Repr

namespace SignedDuration
section base
variable {siPow : Int}
def isNeg (d : SignedDuration siPow) : Bool := d.val < 0
def isNonNeg (d : SignedDuration siPow) : Bool := ¬d.isNeg
def abs (d : SignedDuration siPow) : SignedDuration siPow := ⟨d.val.natAbs⟩

instance : Neg (SignedDuration siPow) where
  neg d := ⟨-d.val⟩

theorem neg_def (d : SignedDuration siPow) : -d = ⟨-d.val⟩ := by rfl

instance : Add (SignedDuration siPow) where
  add a b := ⟨a.val + b.val⟩

theorem add_def (a b : SignedDuration siPow) : a + b = ⟨a.val + b.val⟩ := rfl

instance : Sub (SignedDuration siPow) where
  sub a b := ⟨a.val - b.val⟩

theorem sub_def (a b :  SignedDuration siPow) : a - b = ⟨a.val - b.val⟩ := rfl

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

theorem le_def {d₁ d₂ : SignedDuration siPow} : (d₁ <= d₂) = (d₁.val <= d₂.val) := rfl
theorem lt_def {d₁ d₂ : SignedDuration siPow} : (d₁ < d₂) = (d₁.val < d₂.val) := rfl

theorem val_eq_of_eq : {d1 d2 : SignedDuration siPow} → d1 = d2 → d1.val = d2.val
| ⟨_⟩, _, rfl => rfl

theorem eq_of_val_eq : {d1 d2 : SignedDuration siPow} → d1.val = d2.val → d1 = d2
| ⟨_⟩, _, rfl => rfl

theorem eq_def {d₁ d₂ : SignedDuration siPow} :
  (d₁ = d₂) ↔ (d₁.val = d₂.val)
:= ⟨val_eq_of_eq, eq_of_val_eq⟩

instance (a b : SignedDuration siPow) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : SignedDuration siPow) : Decidable (a <= b) := inferInstanceAs (Decidable (a.val <= b.val))

instance instLinearOrder :
  LinearOrder (SignedDuration siPow)
where
  le_refl (a) := le_refl a.val
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply SignedDuration.eq_of_val_eq
    rw [SignedDuration.le_def] at h2 h1
    exact le_antisymm h1 h2
  le_total := by
    intro a b
    rw [@SignedDuration.le_def siPow a b]
    rw [@SignedDuration.le_def siPow b a]
    exact Int.le_total a.val b.val
  compare := by
    intros a b
    exact cmp a b
  compare_eq_compareOfLessAndEq := by
    simp only [compare, compareOfLessAndEq, List.LT']
    simp [cmp]
    refine' fun a b ↦ _
    simp [cmpUsing]
    split
    · rfl
    case inr not_a_lt_b =>
      split
      case inl b_lt_a =>
        split
        case inl a_eq_b =>
          simp [a_eq_b, SignedDuration.lt_def] at b_lt_a
        case inr not_a_eq_b => rfl
      case inr not_b_lt_a =>
        simp [SignedDuration.eq_def]
        simp [SignedDuration.lt_def] at *
        simp [Int.le_antisymm not_b_lt_a not_a_lt_b]
  decidableLE := inferInstance

theorem monotone {d₁ d₂ : SignedDuration siPow} : d₁.val <= d₂.val → d₁ <= d₂
  | h => (le_def) ▸ h

instance (n : Nat) : OfNat (SignedDuration siPow) n where
  ofNat := ⟨n⟩

@[simp] theorem zero_def : (0 : SignedDuration siPow).val = (0 : Int) := by rfl

instance instAddCommSemigroup : AddCommSemigroup (SignedDuration siPow) where
  add_assoc a b c := by
    simp [SignedDuration.add_def, AddSemigroup.add_assoc]
  add_comm a b := by
    simp [SignedDuration.add_def]
    exact AddCommSemigroup.add_comm (G := Int) _ _

instance instIsLeftCancelAdd : IsLeftCancelAdd (SignedDuration siPow) where
  add_left_cancel a b c h0 := by
    have h2 := SignedDuration.val_eq_of_eq h0
    simp only [SignedDuration.val] at h2
    exact SignedDuration.eq_of_val_eq
      (@Int.add_left_cancel a.val b.val c.val (h2))

instance instIsRightCancelAdd : IsRightCancelAdd (SignedDuration siPow) where
  add_right_cancel a b c := by
    have h0 := @add_right_cancel Int _ _ a.val b.val c.val
    intro h1
    have h2 := SignedDuration.val_eq_of_eq h1
    simp only [SignedDuration.add_def, SignedDuration.val] at h2
    specialize h0 h2
    exact SignedDuration.eq_of_val_eq h0

instance instAddCommMonoid : AddCommMonoid (SignedDuration siPow) where
  add_zero := by
    simp [SignedDuration.eq_of_val_eq, SignedDuration.add_def, add_zero]
  zero_add := by
    simp [SignedDuration.eq_of_val_eq, SignedDuration.add_def, zero_add]
  nsmul := nsmulRec
  add_comm := by
    simp [SignedDuration.eq_of_val_eq, SignedDuration.add_def, add_comm]

instance instEquivIntSelf : Equiv Int (SignedDuration siPow) where
  toFun := SignedDuration.mk
  invFun := SignedDuration.val
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

instance instAddMonoidWithOne : AddMonoidWithOne (SignedDuration siPow) where
  __ := inferInstanceAs (AddCommMonoid (SignedDuration siPow))
  natCast n := SignedDuration.mk (Int.ofNat n)
  natCast_zero := rfl
  natCast_succ _ := rfl


private theorem sub_eq_add_neg (a b : SignedDuration siPow) : a - b = a + -b := by
  simp [
    sub_def, add_def, neg_def,
    HSub.hSub, Sub.sub, Int.sub
  ]

private theorem add_left_neg (a : SignedDuration siPow) : -a + a = 0 := by
  apply eq_of_val_eq
  simp [sub_def, add_def, neg_def]

instance instAddGroupWithOne : AddGroupWithOne (SignedDuration siPow) where
  __ := inferInstanceAs (AddMonoidWithOne (SignedDuration siPow))
  zsmul_zero' _a := rfl
  zsmul_succ' _n _a := rfl
  zsmul_neg' _n _a := rfl
  zsmul := zsmulRec
  sub_eq_add_neg := sub_eq_add_neg
  add_left_neg := add_left_neg
  intCast := mk
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

end base

def convertLossless
  {fine coarse : Int}
  (d : SignedDuration coarse)
  (h : fine <= coarse := by decide) :
  SignedDuration fine :=
    match coarse - fine, Int.sub_nonneg_of_le h with
    | Int.ofNat n, _ => ⟨d.val * (10 ^ n)⟩
    | Int.negSucc _, h_zero_le =>
      False.elim ((not_lt_of_ge h_zero_le) (Int.neg_of_sign_eq_neg_one rfl)) --(Int.neg_succ_lt_zero n))


/--
Lossy conversion using the `e` rounding convention; always rounding toward 0
-/
def eConvertLossy
  {fine coarse : Int}
  (d : SignedDuration fine)
  (h : fine <= coarse := by decide) : SignedDuration coarse :=
    match coarse - fine, Int.sub_nonneg_of_le h with
    | Int.ofNat n, _ => ⟨d.val.ediv (10 ^ n)⟩
    | Int.negSucc _, h_zero_le =>
      False.elim ((not_lt_of_ge h_zero_le) (Int.neg_of_sign_eq_neg_one rfl))

/--
Lossy conversion using the `f` rounding convention
-/
def fConvertLossy
  {fine coarse : Int}
  (d : SignedDuration fine)
  (h : fine <= coarse := by decide) : SignedDuration coarse :=
    match coarse - fine, Int.sub_nonneg_of_le h with
    | Int.ofNat n, _ => ⟨d.val.fdiv (10 ^ n)⟩
    | Int.negSucc _, h_zero_le =>
      False.elim ((not_lt_of_ge h_zero_le) (Int.neg_of_sign_eq_neg_one rfl))

/-
I think this is pretty rarely going to work as expected, so this is an experiment.
There are more complex strategies that can be tried with different versions of `Coe`
-/
instance {n : Int} : Coe (SignedDuration n) (SignedDuration (n - 1)) where
  coe d := SignedDuration.convertLossless d (Int.sub_le_self n (Int.ofNat_zero_le _))

instance {n : Int} {m : Nat} : Coe (SignedDuration n) (SignedDuration (n - m)) where
  coe d := SignedDuration.convertLossless d (Int.sub_le_self n (Int.ofNat_zero_le _))

namespace hiddenCoeExample
def megaSecs_ : SignedDuration 6 := ⟨42⟩
example : SignedDuration 5 := instCoeSignedDurationHSubIntInstHSubInstSubIntOfNat.coe megaSecs_
end hiddenCoeExample

namespace SecondPrecision
@[reducible] def SignedDuration := Timelib.SignedDuration 0

--instance : AddGroupWithOne (SecondPrecision.SignedDuration) := inferInstance

end SecondPrecision

namespace NanoPrecision
@[reducible] def SignedDuration := Timelib.SignedDuration (-9)
--instance : AddGroupWithOne (NanoPrecision.SignedDuration) := inferInstance
end NanoPrecision


namespace MilliPrecision
def SignedDuration := Timelib.SignedDuration (-3)
end MilliPrecision

end SignedDuration

structure SignedDuration64 (siPow : Int) where
  val : Int64

namespace SignedDuration64
section int64
variable {siPow : Int}
def max : SignedDuration64 siPow := ⟨Int64.max⟩
def min : SignedDuration64 siPow := ⟨Int64.min⟩

def toSignedDuration (d : SignedDuration64 siPow) : SignedDuration siPow :=
  ⟨d.val.toInt⟩

def fromSignedDuration (d : SignedDuration siPow) : Option (SignedDuration64 siPow) :=
  if Int64.min.toInt <= d.val && d.val <= Int64.max.toInt
  then some (⟨Int64.ofInt d.val⟩)
  else none

/-
We want to eventualy say that (x : SignedDuration siPow) is in some sense equivalent to (x : SignedDuration64 siPow)
-/
--theorem iso1 (d : SignedDuration siPow) : d.val >= Int64.min.toInt && d.val <= Int64.max.toInt → (SignedDuration64.fromSignedDuration d).map SignedDuration64.toSignedDuration = some d := by
--  intro h
--  simp [toSignedDuration, fromSignedDuration, h]
--  -- need `Int64.toInt comp Int64.ofInt is iso
--  trace_state
--  sorry
--
--theorem iso0 (d : SignedDuration64 siPow) : fromSignedDuration (d.toSignedDuration) = some d := by
--  simp [toSignedDuration, fromSignedDuration]
--  sorry

instance : Neg (SignedDuration64 siPow) where
  neg d := ⟨-d.val⟩

theorem neg_def (d : SignedDuration64 siPow) : -d = ⟨-d.val⟩ := by rfl

instance instAddSignedDuration64 : Add (SignedDuration64 siPow) where
  add a b := ⟨a.val + b.val⟩

theorem add_def (a b : SignedDuration64 siPow) : a + b = ⟨a.val + b.val⟩ := rfl

def overflowingAdd (a b : SignedDuration64 siPow) : (Bool × SignedDuration64 siPow) :=
  let sum := a + b
  (Int64.max <= sum.val, sum)


def checkedAdd (a b : SignedDuration64 siPow) : Option (SignedDuration64 siPow) :=
  match a.overflowingAdd b with
  | (true, _) => none
  | (false, sum) => some (sum)

instance : Sub (SignedDuration64 siPow) where
  sub a b := ⟨a.val - b.val⟩

end int64
end SignedDuration64
