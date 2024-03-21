import Timelib.Util
import Timelib.SignedInt
import Mathlib.Init.Order.Defs
import Mathlib.Data.List.Lex
import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.Logic.Nontrivial.Defs

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
deriving DecidableEq, Hashable, Repr


namespace SignedDuration
section base
variable {siPow : Int}

instance instInhabited : Inhabited (SignedDuration siPow) where
  default := ⟨0⟩

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

instance instMulSelf : Mul (SignedDuration siPow) where
  mul a b := ⟨a.val * b.val⟩

theorem mul_def (a b :  SignedDuration siPow) : a * b = ⟨a.val * b.val⟩ := rfl

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

instance : Ord (SignedDuration siPow) where
  compare a b := compareOfLessAndEq a b

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
    simp only [cmp]
    refine' fun a b ↦ _
    simp only [cmpUsing]
    split
    · rfl
    case inr not_a_lt_b =>
      split
      case inl b_lt_a =>
        split
        case inl a_eq_b =>
          simp only [a_eq_b, lt_def, lt_self_iff_false] at b_lt_a
        case inr not_a_eq_b => rfl
      case inr not_b_lt_a =>
        simp only [eq_def]
        simp only [lt_def, not_lt] at *
        simp only [Int.le_antisymm not_b_lt_a not_a_lt_b, ↓reduceIte]
  decidableLE := inferInstance

theorem monotone {d₁ d₂ : SignedDuration siPow} : d₁.val <= d₂.val → d₁ <= d₂
  | h => (le_def) ▸ h

instance (n : Nat) : OfNat (SignedDuration siPow) n where
  ofNat := ⟨n⟩

theorem zero_def_ : (0 : SignedDuration siPow) = ⟨(0 : Int)⟩ := by rfl
theorem one_def_ : (1 : SignedDuration siPow) = ⟨(1 : Int)⟩ := by rfl

@[simp] theorem zero_val_def : (0 : SignedDuration siPow).val = (0 : Int) := by rfl
@[simp] theorem one_val_def : (1 : SignedDuration siPow).val = (1 : Int) := by rfl

instance instAddCommSemigroup : AddCommSemigroup (SignedDuration siPow) where
  add_assoc a b c := by
    simp only [add_def, AddSemigroup.add_assoc]
  add_comm a b := by
    simp only [add_def, mk.injEq]
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
    simp only [add_def, zero_val_def, add_zero, forall_const]
  zero_add := by
    simp only [add_def, zero_val_def, zero_add, forall_const]
  nsmul := nsmulRec
  add_comm := by
    simp only [add_def, add_comm, forall_const]

instance instEquivIntSelf : Equiv Int (SignedDuration siPow) where
  toFun := SignedDuration.mk
  invFun := SignedDuration.val
  left_inv := by simp only [Function.LeftInverse, forall_const]
  right_inv := by simp only [Function.RightInverse, Function.LeftInverse, forall_const]

instance instAddMonoidWithOne : AddMonoidWithOne (SignedDuration siPow) where
  __ := inferInstanceAs (AddCommMonoid (SignedDuration siPow))
  natCast n := SignedDuration.mk (Int.ofNat n)
  natCast_zero := rfl
  natCast_succ _ := rfl

instance : Nontrivial (SignedDuration siPow) where
  exists_pair_ne := Exists.intro 0 <| Exists.intro 1 <| by
    simp only [zero_def_, one_def_, ne_eq, mk.injEq, zero_ne_one, not_false_eq_true]

-- CanonicallyOrderedCommSemiring
instance : CommSemiring (SignedDuration siPow) where
  mul_comm := by simp only [mul_def, mk.injEq]; exact fun a b => Int.mul_comm a.val b.val
  left_distrib := by simp only [add_def, mul_def, mk.injEq]; exact fun a b c => Int.mul_add a.val b.val c.val
  right_distrib := by simp only [add_def, mul_def, mk.injEq]; exact fun a b c => Int.add_mul a.val b.val c.val
  one_mul _ := by simp [mul_def]
  mul_one := by simp only [mul_def, one_val_def, mul_one, forall_const]
  mul_assoc := by simp only [mul_def, mk.injEq]; exact fun a b c => Int.mul_assoc a.val b.val c.val
  zero_mul _ := by
    apply eq_of_val_eq; simp only [mul_def, zero_val_def, zero_mul]
  mul_zero _ := by
    apply eq_of_val_eq; simp only [mul_def, zero_val_def, mul_zero]

instance : LinearOrderedSemiring (SignedDuration siPow) where
  __ := instLinearOrder
  zero_le_one := right_eq_inf.mp rfl
  add_le_add_left := by
    simp only [le_def, add_def, add_le_add_iff_left, forall_const, imp_self]
  le_of_add_le_add_left := by
    simp only [add_def, le_def, add_le_add_iff_left, imp_self, forall_const]
  mul_lt_mul_of_pos_left := by
    simp only [lt_def, zero_def_, mul_def]; exact fun _ _ _ => Int.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := by
    simp only [lt_def, zero_def_, mul_def]; exact fun _ _ _ => Int.mul_lt_mul_of_pos_right



private theorem sub_eq_add_neg (a b : SignedDuration siPow) : a - b = a + -b := by
  simp only [HSub.hSub, Sub.sub, Int.sub, neg_def, add_def]

private theorem add_left_neg (a : SignedDuration siPow) : -a + a = 0 := by
  apply eq_of_val_eq
  simp [sub_def, add_def, neg_def]

instance instAddGroupWithOne : AddGroupWithOne (SignedDuration siPow) where
  --__ := inferInstanceAs (AddMonoidWithOne (SignedDuration siPow))
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
  (_ : fine <= coarse := by decide) :
  SignedDuration fine :=
    ⟨d.val * (10 ^ (coarse - fine).natAbs)⟩

/--
Lossy conversion using the `e` rounding convention
-/
def eConvertLossy
  {fine coarse : Int}
  (d : SignedDuration fine)
  (_ : fine <= coarse := by decide) : SignedDuration coarse :=
   ⟨d.val.ediv (10 ^ (coarse - fine).natAbs)⟩

/--
Lossy conversion using the `f` rounding convention
-/
def fConvertLossy
  {fine coarse : Int}
  (d : SignedDuration fine)
  (_ : fine <= coarse := by decide) : SignedDuration coarse :=
   ⟨d.val.fdiv (10 ^ (coarse - fine).natAbs)⟩

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


namespace SignedDuration
def le_het {p1 p2 : Int} (d1 : SignedDuration p1) (d2 : SignedDuration p2) : Prop :=
  (d1.convertLossless (min_le_left _ _) : SignedDuration (min p1 p2)).val
  <= (d2.convertLossless (min_le_right _ _) : SignedDuration (min p1 p2)).val

def lt_het {p1 p2 : Int} (d1 : SignedDuration p1) (d2 : SignedDuration p2) : Prop :=
  (d1.convertLossless (min_le_left _ _) : SignedDuration (min p1 p2)).val
  < (d2.convertLossless (min_le_right _ _) : SignedDuration (min p1 p2)).val

theorem le_het_iff {p : Int} (d1 d2 : SignedDuration p) : le_het d1 d2 ↔ d1 <= d2 := by
  simp only [le_het, convertLossless, min_self, sub_self, Int.natAbs_zero, pow_zero, mul_one,
    le_def]

theorem lt_het_iff {p : Int} (d1 d2 : SignedDuration p) : lt_het d1 d2 ↔ d1 < d2 := by
  simp only [lt_het, convertLossless, min_self, sub_self, Int.natAbs_zero, pow_zero, mul_one,
    lt_def]

instance instDecidableLEHet {p1 p2 : Int} (d1 : SignedDuration p1) (d2 : SignedDuration p2) :
  Decidable (le_het d1 d2)
:= inferInstanceAs <| Decidable <|
  (d1.convertLossless (min_le_left _ _) : SignedDuration (min p1 p2)).val
  <= (d2.convertLossless (min_le_right _ _) : SignedDuration (min p1 p2)).val

instance instDecidableLTHet {p1 p2 : Int} (d1 : SignedDuration p1) (d2 : SignedDuration p2) :
  Decidable (lt_het d1 d2)
:= inferInstanceAs <| Decidable <|
  (d1.convertLossless (min_le_left _ _) : SignedDuration (min p1 p2)).val
  < (d2.convertLossless (min_le_right _ _) : SignedDuration (min p1 p2)).val

section le_trans_cases

variable
  {p1 p2 p3 : Int}
  (d1 : SignedDuration p1)
  (d2 : SignedDuration p2)
  (d3 : SignedDuration p3)


theorem le_add_of_le {a b : Int} {c : Nat} (d : Nat) :
  a <= b * (10 : Int) ^ c →
  a * (10 : Int) ^ d <= b * ((10 : Int) ^ (c + d)) := by
  intro h0
  have h1 : a * 10 ^ d <= b * 10 ^ c * 10 ^ d := Int.mul_le_mul_of_nonneg_right h0 (pow_nonneg (Int.zero_le_ofNat _) _)
  have h2 := pow_add (10 : Int) c d
  have h3 := mul_assoc b (10 ^ c) (10 ^ d)
  rwa [h2, ← h3]

theorem add_le_of_le {a b : Int} {c: Nat} (d : Nat) :
  a * (10 : Int) ^ c <= b →
  a * ((10 : Int) ^ (c + d)) <= b * (10 : Int) ^ d := by
  intro h0
  have h1 : a * 10 ^ c * 10 ^ d <= b * 10 ^ d := Int.mul_le_mul_of_nonneg_right h0 (pow_nonneg (Int.zero_le_ofNat _) _)
  have h2 := pow_add (10 : Int) c d
  have h3 := mul_assoc a (10 ^ c) (10 ^ d)
  rwa [h2, ← h3]

theorem pow_eq (d1 : Int) :
  p2 <= p1 → p3 <= p2 →
  d1 * 10 ^ Int.natAbs (↑p1 - ↑p2) * 10 ^ Int.natAbs (↑p2 - ↑p3) = d1 * 10 ^ Int.natAbs (↑p1 - ↑p3) := by
  intro h21 h32
  have h1 := tsub_add_tsub_cancel h21 h32
  have h2 := Int.natAbs_add_nonneg (Int.sub_nonneg_of_le h21) (Int.sub_nonneg_of_le h32)
  have h3 := pow_add (10 : Int) (Int.natAbs <| p1 - p2) (Int.natAbs <| p2 - p3)
  rw [← h1, h2, h3, mul_assoc]
  done

theorem case1 :
  p1 <= p2 → p2 <= p3 →
  d1.val ≤ d2.val * 10 ^ Int.natAbs (↑p2 - ↑p1) →
    d2.val ≤ d3.val * 10 ^ Int.natAbs (↑p3 - ↑p2) →
      d1.val ≤ d3.val * 10 ^ Int.natAbs (↑p3 - ↑p1) :=
    fun ab bc hh1 hh2 =>
    have hA := le_add_of_le (Int.natAbs <| ↑p2 - ↑p1) hh2
    have hB := Int.natAbs_add_nonneg (Int.sub_nonneg_of_le bc)  (Int.sub_nonneg_of_le ab)
    have hC := tsub_add_tsub_cancel bc ab
    le_trans hh1 (hC ▸ hB ▸ hA)

theorem case2 :
  p1 <= p3 → p3 <= p2 →
  d1.val ≤ d2.val * 10 ^ Int.natAbs (↑p2 - ↑p1) →
    d2.val * 10 ^ Int.natAbs (↑p2 - ↑p3) ≤ d3.val →
      d1.val ≤ d3.val * 10 ^ Int.natAbs (↑p3 - ↑p1) := by
    intro h13 h32 hh1 hh2
    have hA := add_le_of_le (Int.natAbs <| ↑p3 - ↑p1) hh2
    have hB := Int.natAbs_add_nonneg (Int.sub_nonneg_of_le h32) (Int.sub_nonneg_of_le h13)
    have hC := tsub_add_tsub_cancel h32 h13
    exact le_trans hh1 (hC ▸ hB ▸ hA)

theorem case3 :
  p2 <= p1 → p1 <= p3 →
    d1.val * 10 ^ Int.natAbs (↑p1 - ↑p2) ≤ d2.val →
      d2.val ≤ d3.val * 10 ^ Int.natAbs (↑p3 - ↑p2) →
        d1.val ≤ d3.val * 10 ^ Int.natAbs (↑p3 - ↑p1) := by
  intro h21 h13 hh1 hh2
  have hSuffices :
    d3.val * 10 ^ (Int.natAbs <| ↑p3 - ↑p2) =
      d3.val * 10 ^ Int.natAbs (↑p3 - ↑p1) * 10 ^ Int.natAbs (↑p1 - ↑p2) := by
    have h5 := Int.natAbs_add_nonneg (Int.sub_nonneg_of_le h13) (Int.sub_nonneg_of_le h21)
    have h6 := tsub_add_tsub_cancel (a := p3) (b := p1) (c := p2) h13 h21
    have h7 := pow_add (a := (10: Int))  (m := Int.natAbs <| p3 - p1) (n := Int.natAbs <| p1 - p2)
    rw [← h6, h5, h7, mul_assoc d3.val]
  exact
    Int.le_of_mul_le_mul_right
      (le_trans hh1 (hSuffices ▸ hh2))
      (by simp only [gt_iff_lt, Nat.ofNat_pos, pow_pos])

theorem case4 :
  p2 ≤ p3 → p3 ≤ p1 →
    d1.val * 10 ^ Int.natAbs (↑p1 - ↑p2) ≤ d2.val →
      d2.val ≤ d3.val * 10 ^ Int.natAbs (↑p3 - ↑p2) →
        d1.val * 10 ^ Int.natAbs (↑p1 - ↑p3) ≤ d3.val := by
  intro bc ca h1 h2
  have hSuffices :
    d1.val * 10 ^ Int.natAbs (↑p1 - ↑p2) =
      d1.val * 10 ^ Int.natAbs (↑p1 - ↑p3) * 10 ^ Int.natAbs (↑p3 - ↑p2) := by
      have h5 := Int.natAbs_add_nonneg (Int.sub_nonneg_of_le ca) (Int.sub_nonneg_of_le bc)
      have h6 := tsub_add_tsub_cancel (a := p1) (b := p3) (c := p2) ca bc
      have h7 := pow_add (a := (10: Int))  (m := Int.natAbs <| p1 - p3) (n := Int.natAbs <| p3 - p2)
      rw [← h6, h5, h7, mul_assoc d1.val]
  exact
    Int.le_of_mul_le_mul_right
      (a := 10 ^ Int.natAbs (↑p3 - ↑p2))
      (le_trans (hSuffices ▸ h1) h2)
      (by simp only [gt_iff_lt, Nat.ofNat_pos, pow_pos])

theorem case5 :
  p3 ≤ p2 → p2 ≤ p1 →
    d1.val * 10 ^ Int.natAbs (↑p1 - ↑p2) ≤ d2.val →
      d2.val * 10 ^ Int.natAbs (↑p2 - ↑p3) ≤ d3.val →
        d1.val * 10 ^ Int.natAbs (↑p1 - ↑p3) ≤ d3.val := by
  intro cb ba h1 h2
  refine le_trans ?hx h2
  have hh3 :=
    mul_le_mul_of_nonneg_right
    (a := 10 ^ Int.natAbs (↑p2 - ↑p3))
    (b := d1.val * 10 ^ Int.natAbs (↑p1 - ↑p2))
    (c := d2.val)
    h1
    (pow_nonneg (Int.zero_le_ofNat _) _)
  have hh4 : d1.val * 10 ^ Int.natAbs (↑p1 - ↑p2) * 10 ^ Int.natAbs (↑p2 - ↑p3) = d1.val * 10 ^ Int.natAbs (↑p1 - ↑p3) :=
    pow_eq d1.val ba cb
  exact hh4 ▸ hh3

theorem case6 :
  p3 ≤ p1 → p1 ≤ p2 →
    d1.val ≤ d2.val * 10 ^ Int.natAbs (↑p2 - ↑p1) →
      d2.val * 10 ^ Int.natAbs (↑p2 - ↑p3) ≤ d3.val →
        d1.val * 10 ^ Int.natAbs (↑p1 - ↑p3) ≤ d3.val:= by
  intro ca ab h1 h2
  refine le_trans ?hx h2
  have hh3 :=
    mul_le_mul_of_nonneg_right
    (a := 10 ^ Int.natAbs (↑p1 - ↑p3))
    (b := d1.val)
    (c := d2.val * 10 ^ Int.natAbs (↑p2 - ↑p1))
    h1
    (pow_nonneg (Int.zero_le_ofNat _) _)
  have hh4 : d2.val * 10 ^ Int.natAbs (↑p2 - ↑p1) * 10 ^ Int.natAbs (↑p1 - ↑p3) = d2.val * 10 ^ Int.natAbs (↑p2 - ↑p3) :=
    pow_eq d2.val ab ca
  exact hh4 ▸ hh3

end le_trans_cases

theorem le3_dnf (a b c : Int) :
  (a <= b ∧ b <= c)
  ∨ (a <= c ∧ c <= b)
  ∨ (b <= a ∧ a <= c)
  ∨ (b <= c ∧ c <= a)
  ∨ (c <= b ∧ b <= a)
  ∨ (c <= a ∧ a <= b) := by
  rcases (And.intro (le_total a b) (And.intro (le_total b c) (le_total a c)))
  with ⟨hab | hba, hbc | hcb, hac | hca⟩
  . exact .inl ⟨hab, hbc⟩
  . exact .inr (.inr (.inr (.inr (.inr ⟨hca, hab⟩))))
  . exact .inr (.inl ⟨hac, hcb⟩)
  . exact .inr (.inr (.inr (.inr (.inr ⟨hca, hab⟩))))
  . exact .inr (.inr (.inl ⟨hba, hac⟩))
  . exact .inr (.inr (.inr (.inl ⟨hbc, hca⟩)))
  . exact .inr (.inr (.inl ⟨hba, hac⟩))
  . exact .inr (.inr (.inr (.inr (.inl ⟨hcb, hba⟩))))
  done

theorem le_het_trans {p1 p2 p3: Int} (d1 : SignedDuration p1) (d2 : SignedDuration p2) (d3 : SignedDuration p3)
  : le_het d1 d2 → le_het d2 d3 → le_het d1 d3 := by
  simp [le_het, SignedDuration.convertLossless]
  rcases (le3_dnf p1 p2 p3)
  with ⟨ab, bc⟩ | ⟨ac, cb⟩ | ⟨ba, ac⟩ | ⟨bc, ca⟩ | ⟨cb, ba⟩ | ⟨ca, ab⟩
  .
    have _ := case1 d1 d2 d3 ab bc
    simpa [min_eq_left ab, sub_self, Int.natAbs_zero, pow_zero, mul_one, min_eq_left bc,
      min_eq_left_iff.mpr (le_trans ab bc)]
    done
  .
    have _ := case2 d1 d2 d3 ac cb
    simpa only [min_eq_left_iff.mpr (le_trans ac cb), sub_self, Int.natAbs_zero, pow_zero, mul_one,
      min_eq_right cb, min_eq_left ac]
  .
    have _ := case3 d1 d2 d3 ba ac
    simpa only [min_eq_right ba, sub_self, Int.natAbs_zero, pow_zero, mul_one,
      min_eq_left_iff.mpr (le_trans ba ac), min_eq_left ac]
  .
    have _ := case4 d1 d2 d3 bc ca
    simpa only [min_eq_right_iff.mpr (le_trans bc ca), sub_self, Int.natAbs_zero, pow_zero, mul_one,
      min_eq_left bc, min_eq_right ca]
  .
    have _ := case5 d1 d2 d3 cb ba
    simpa only [min_eq_right ba, sub_self, Int.natAbs_zero, pow_zero, mul_one, min_eq_right cb,
      min_eq_right_iff.mpr (le_trans cb ba)]
  .
    have _ := case6 d1 d2 d3 ca ab
    simpa only [min_eq_left ab, sub_self, Int.natAbs_zero, pow_zero, mul_one,
      min_eq_right_iff.mpr (le_trans ca ab), min_eq_right ca]

theorem lt_het_iff_le_het_not_le_het {p1 p2 : Int} (d1 : SignedDuration p1) (d2 : SignedDuration p2)
  : lt_het d1 d2 ↔ le_het d1 d2 ∧ ¬(le_het d2 d1) := by
  simp only [le_het, lt_het, convertLossless]
  cases le_total p1 p2 with
  | inl h =>
    refine Iff.intro ?mp ?mpr
    case mp =>
      simp only [min_eq_left h, sub_self, Int.natAbs_zero, pow_zero, mul_one, min_eq_right h,
        not_le]
      exact fun hlt => ⟨(le_of_lt hlt), hlt⟩
    case mpr =>
      simp only [min_eq_left h, sub_self, Int.natAbs_zero, pow_zero, mul_one, min_eq_right h,
        not_le, and_imp, imp_self, implies_true]
  | inr h =>
    refine Iff.intro ?mp ?mpr
    case mp =>
      simp only [min_eq_right h, sub_self, Int.natAbs_zero, pow_zero, mul_one, min_eq_left h,
        not_le]
      exact fun hlt => ⟨(le_of_lt hlt), hlt⟩
    case mpr =>
      simp only [min_eq_right h, sub_self, Int.natAbs_zero, pow_zero, mul_one, min_eq_left h,
        not_le, and_imp, imp_self, implies_true]

end SignedDuration

structure HSignedDuration where
  siPow: Int
  val: SignedDuration siPow
