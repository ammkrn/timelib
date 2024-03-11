import Mathlib.Data.Nat.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Int.Order
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.String.Defs
import Mathlib.Data.String.Lemmas
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic

/- The number of nanoseconds in one second -/
abbrev oneSecondNanos : Nat := 1000000000

/-- The number of nanoseconds in one minute -/
abbrev oneMinuteNanos : Nat := 60000000000

/-- The number of nanoseconds in one hour -/
abbrev oneHourNanos : Nat := 3600000000000

/-- The number of nanoseconds in one day -/
abbrev oneDayNanos : Nat := 86400000000000

/-- The number of nanoseconds in one 7-day week -/
abbrev oneWeekNanos : Nat := 604800000000000

/-- The number of nanoseconds in one 365-day year -/
abbrev oneYearNanos : Nat := 31536000000000000



structure SignedDuration where
  val : Int
deriving DecidableEq, Ord, Repr



namespace SignedDuration



def isNeg (d : SignedDuration) : Bool :=
  d.val < 0
def isNonNeg (d : SignedDuration) : Bool :=
  ¬d.isNeg
def abs (d : SignedDuration) : SignedDuration :=
  mk (d.val.natAbs)

instance instNeg : Neg SignedDuration where
  neg d := ⟨-d.val⟩

theorem neg_def (d : SignedDuration) : -d = ⟨-d.val⟩ := by rfl

instance instAdd : Add SignedDuration where
  add a b := ⟨a.val + b.val⟩

theorem add_def (a b : SignedDuration) : a + b = ⟨a.val + b.val⟩ := rfl

instance instSub : Sub SignedDuration where
  sub a b := ⟨a.val - b.val⟩

theorem sub_def (a b : SignedDuration) : a - b = ⟨a.val - b.val⟩ := rfl

instance instHMulSelfNatSelf : HMul SignedDuration Nat SignedDuration where
  hMul d n := ⟨d.val * n⟩

instance instHModSelfIntSelf : HMod SignedDuration Int SignedDuration where
  hMod a n := ⟨a.val % n⟩

instance instHDivSelfNatSelf : HDiv SignedDuration Nat SignedDuration where
  hDiv a b := ⟨a.val / b⟩

instance instHPowSelfNatSelf : HPow SignedDuration Nat SignedDuration where
  hPow a b := ⟨a.val ^ b⟩



instance instLT : LT SignedDuration where
  lt := InvImage Int.lt SignedDuration.val

instance instLE : LE SignedDuration where
  le := InvImage Int.le SignedDuration.val

instance instDecidableLT (a b : SignedDuration) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.val < b.val))
instance instDecidableLE (a b : SignedDuration) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.val ≤ b.val))

theorem le_def {d₁ d₂ : SignedDuration} :
  (d₁ ≤ d₂) = (d₁.val ≤ d₂.val)
:= rfl
theorem lt_def {d₁ d₂ : SignedDuration} :
  (d₁ < d₂) = (d₁.val < d₂.val)
:= rfl



theorem val_eq_of_eq :
  ∀ {d1 d2 : SignedDuration}, d1 = d2 → d1.val = d2.val
| ⟨_⟩, _, rfl => rfl

theorem eq_of_val_eq :
  ∀ {d1 d2 : SignedDuration}, d1.val = d2.val → d1 = d2
| ⟨_⟩, _, rfl => rfl

theorem eq_def {d₁ d₂ : SignedDuration} :
  (d₁ = d₂) ↔ (d₁.val = d₂.val)
:= ⟨val_eq_of_eq, eq_of_val_eq⟩



instance instLinearOrder :
  LinearOrder SignedDuration
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
    rw [@SignedDuration.le_def a b]
    rw [@SignedDuration.le_def b a]
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



theorem monotone {d₁ d₂ : SignedDuration} :
  d₁.val ≤ d₂.val -> d₁ ≤ d₂
:= fun h => le_def ▸ h

@[reducible] def toNanos (d : SignedDuration) : Int :=
  d.val
@[reducible] def toSeconds (d : SignedDuration) : Int :=
  d.val / oneSecondNanos
@[reducible] def toMinutes (d : SignedDuration) : Int :=
  d.val / oneMinuteNanos
@[reducible] def toHours (d : SignedDuration) : Int :=
  d.val / oneHourNanos
@[reducible] def toDays (d : SignedDuration) : Int :=
  d.val / oneDayNanos
@[reducible] def toWeeks (d : SignedDuration) : Int :=
  d.val / oneWeekNanos
@[reducible] def toNonLeapYears (d : SignedDuration) : Int :=
  d.val / (365 * oneDayNanos)

@[reducible] def fromNanos (n : Int) : SignedDuration :=
  ⟨n⟩
@[reducible] def fromSeconds (n : Int) : SignedDuration :=
  ⟨n * oneSecondNanos⟩
@[reducible] def fromMinutes (n : Int) : SignedDuration :=
  ⟨n * oneMinuteNanos⟩
@[reducible] def fromHours (n : Int) : SignedDuration :=
  ⟨n * oneHourNanos⟩
@[reducible] def fromWeeks (n : Int) : SignedDuration :=
  ⟨n * oneWeekNanos⟩
@[reducible] def fromDays (n : Int) : SignedDuration :=
  ⟨n * oneDayNanos⟩
@[reducible] def fromNonLeapYears (n : Int) : SignedDuration :=
  ⟨n * oneYearNanos⟩

instance instOfNat (n : Nat) : OfNat SignedDuration n where
  ofNat := ⟨n⟩

@[simp] theorem zero_def : (0 : SignedDuration).val = (0 : Int) := by rfl

instance instToString : ToString SignedDuration where
  toString d :=
    let pfx := if d.isNonNeg then "" else "-"
    let d := d.abs
    let secs := String.leftpad 2 '0' s!"{d.toSeconds}"
    let nanos := String.leftpad 9 '0' s!"{d.toNanos % Int.ofNat oneSecondNanos}"
    s!"{pfx}P{secs}.{nanos}S"

instance instAddCommSemigroup : AddCommSemigroup SignedDuration where
  add_assoc a b c := by
    simp [SignedDuration.add_def, AddSemigroup.add_assoc]
  add_comm a b := by
    simp [SignedDuration.add_def]
    exact AddCommSemigroup.add_comm (G := Int) _ _

instance instIsLeftCancelAdd : IsLeftCancelAdd SignedDuration where
  add_left_cancel a b c h0 := by
    have h2 := SignedDuration.val_eq_of_eq h0
    simp only [SignedDuration.val] at h2
    exact SignedDuration.eq_of_val_eq
      (@Int.add_left_cancel a.val b.val c.val (h2))

instance instIsRightCancelAdd : IsRightCancelAdd SignedDuration where
  add_right_cancel a b c := by
    have h0 := @add_right_cancel Int _ _ a.val b.val c.val
    intro h1
    have h2 := SignedDuration.val_eq_of_eq h1
    simp only [SignedDuration.add_def, SignedDuration.val] at h2
    specialize h0 h2
    exact SignedDuration.eq_of_val_eq h0

instance instAddCommMonoid : AddCommMonoid SignedDuration where
  add_zero := by
    simp [SignedDuration.eq_of_val_eq, SignedDuration.add_def, add_zero]
  zero_add := by
    simp [SignedDuration.eq_of_val_eq, SignedDuration.add_def, zero_add]
  nsmul_zero := by simp [nsmulRec]
  nsmul_succ := by simp [nsmulRec]
  add_comm := by
    simp [SignedDuration.eq_of_val_eq, SignedDuration.add_def, add_comm]

instance instEquivIntSelf : Equiv Int SignedDuration where
  toFun := SignedDuration.mk
  invFun := SignedDuration.val
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

instance instAddMonoidWithOne : AddMonoidWithOne SignedDuration where
  __ := inferInstanceAs (AddCommMonoid SignedDuration)
  natCast n := SignedDuration.mk (Int.ofNat n)
  natCast_zero := rfl
  natCast_succ _ := rfl

private theorem sub_eq_add_neg (a b : SignedDuration) :
  a - b = a + -b
:= by
  simp [sub_def, add_def, neg_def, HSub.hSub, Sub.sub, Int.sub]

private theorem add_left_neg (a : SignedDuration) :
  -a + a = 0
:= by
  apply eq_of_val_eq
  simp [sub_def, add_def, neg_def]

instance instAddGroupWithOne : AddGroupWithOne SignedDuration where
  __ := inferInstanceAs (AddMonoidWithOne (SignedDuration))
  zsmul_zero' _a := rfl
  zsmul_succ' _n _a := rfl
  zsmul_neg' _n _a := rfl
  sub_eq_add_neg := sub_eq_add_neg
  add_left_neg := add_left_neg
  intCast := mk
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl
