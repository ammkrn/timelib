import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Int.Order
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.String.Defs
import Mathlib.Data.String.Lemmas
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Equiv.Basic

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

def SignedDuration.isNeg (d : SignedDuration) : Bool := d.val < 0
def SignedDuration.isNonNeg (d : SignedDuration) : Bool := ¬d.isNeg
def SignedDuration.abs (d : SignedDuration) : SignedDuration := SignedDuration.mk (d.val.natAbs)

instance : Neg SignedDuration where
  neg d := ⟨-d.val⟩ 

theorem SignedDuration.neg_def (d : SignedDuration) : -d = ⟨-d.val⟩ := by rfl

instance : Add SignedDuration where
  add a b := ⟨a.val + b.val⟩ 

theorem SignedDuration.add_def (a b : SignedDuration) : a + b = ⟨a.val + b.val⟩ := rfl

instance : Sub SignedDuration where
  sub a b := ⟨a.val - b.val⟩ 

theorem SignedDuration.sub_def (a b : SignedDuration) : a - b = ⟨a.val - b.val⟩ := rfl

instance : HMul SignedDuration Nat SignedDuration where
  hMul d n := ⟨d.val * n⟩ 

instance : HMod SignedDuration Int SignedDuration where
  hMod a n := ⟨a.val % n⟩ 

instance : HDiv SignedDuration Nat SignedDuration where
  hDiv a b := ⟨a.val / b⟩ 

instance : HPow SignedDuration Nat SignedDuration where
  hPow a b := ⟨a.val ^ b⟩ 

instance : LT SignedDuration where
  lt := InvImage Int.lt SignedDuration.val

instance : LE SignedDuration where
  le := InvImage Int.le SignedDuration.val

theorem SignedDuration.le_def {d₁ d₂ : SignedDuration} : (d₁ <= d₂) = (d₁.val <= d₂.val) := rfl
theorem SignedDuration.lt_def {d₁ d₂ : SignedDuration} : (d₁ < d₂) = (d₁.val < d₂.val) := rfl

theorem SignedDuration.val_eq_of_eq : ∀ {d1 d2 : SignedDuration} (h : d1 = d2), d1.val = d2.val
| ⟨_⟩, _, rfl => rfl

theorem SignedDuration.eq_of_val_eq : ∀ {d1 d2 : SignedDuration} (h : d1.val = d2.val), d1 = d2
| ⟨_⟩, _, rfl => rfl

instance (a b : SignedDuration) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : SignedDuration) : Decidable (a <= b) := inferInstanceAs (Decidable (a.val <= b.val))

instance : LinearOrder SignedDuration where
  le_refl (a) := le_refl a.val
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply SignedDuration.eq_of_val_eq
    rw [SignedDuration.le_def] at h2 h1
    exact le_antisymm h1 h2
  le_total := by simp [SignedDuration.le_def, le_total]
  decidable_le := inferInstance

theorem SignedDuration.monotone {d₁ d₂ : SignedDuration} : d₁.val <= d₂.val -> d₁ <= d₂ := 
  fun h => (SignedDuration.le_def) ▸ h
  
@[reducible] def SignedDuration.toNanos (d : SignedDuration) : Int := d.val
@[reducible] def SignedDuration.toSeconds (d : SignedDuration) : Int := d.val / oneSecondNanos
@[reducible] def SignedDuration.toMinutes (d : SignedDuration) : Int := d.val / oneMinuteNanos
@[reducible] def SignedDuration.toHours (d : SignedDuration) : Int := d.val / oneHourNanos
@[reducible] def SignedDuration.toDays (d : SignedDuration) : Int := d.val / oneDayNanos
@[reducible] def SignedDuration.toWeeks (d : SignedDuration) : Int := d.val / oneWeekNanos
@[reducible] def SignedDuration.toNonLeapYears (d : SignedDuration) : Int := d.val / (365 * oneDayNanos)

@[reducible] def SignedDuration.fromNanos (n : Int) : SignedDuration := ⟨n⟩ 
@[reducible] def SignedDuration.fromSeconds (n : Int) : SignedDuration := ⟨n * oneSecondNanos⟩
@[reducible] def SignedDuration.fromMinutes (n : Int) : SignedDuration := ⟨n * oneMinuteNanos⟩ 
@[reducible] def SignedDuration.fromHours (n : Int) : SignedDuration := ⟨n * oneHourNanos⟩ 
@[reducible] def SignedDuration.fromWeeks (n : Int) : SignedDuration := ⟨n * oneWeekNanos⟩
@[reducible] def SignedDuration.fromDays (n : Int) : SignedDuration := ⟨n * oneDayNanos⟩ 
@[reducible] def SignedDuration.fromNonLeapYears (n : Int) : SignedDuration := ⟨n * oneYearNanos⟩

instance (n : Nat) : OfNat SignedDuration n where
  ofNat := ⟨n⟩ 

@[simp] theorem SignedDuration.zero_def : (0 : SignedDuration).val = (0 : Int) := by rfl

instance : Neg SignedDuration where
  neg d := ⟨-d.val⟩

instance : ToString SignedDuration where
  toString d := 
    let pfx := if d.isNonNeg then "" else "-"
    let d := d.abs
    let secs := String.leftpad 2 '0' s!"{d.toSeconds}"
    let nanos := String.leftpad 9 '0' s!"{d.toNanos % Int.ofNat oneSecondNanos}"
    s!"{pfx}P{secs}.{nanos}S"

instance : AddCommSemigroup SignedDuration := {
  add_assoc := fun a b c => by simp [SignedDuration.add_def, AddSemigroup.add_assoc]
  add_comm := fun a b => by simp [SignedDuration.add_def]; exact AddCommSemigroup.add_comm (A := Int) _ _
}

instance : IsAddLeftCancel SignedDuration where
  add_left_cancel := fun a b c h0 => by
    have h2 := SignedDuration.val_eq_of_eq h0
    simp only [SignedDuration.val] at h2
    exact SignedDuration.eq_of_val_eq (@Int.add_left_cancel a.val b.val c.val (h2))
  
instance : IsAddRightCancel SignedDuration where
  add_right_cancel := fun a b c => by
    have h0 := @add_right_cancel Int _ _ a.val b.val c.val
    intro h1
    have h2 := SignedDuration.val_eq_of_eq h1
    simp only [SignedDuration.add_def, SignedDuration.val] at h2
    specialize h0 h2
    exact SignedDuration.eq_of_val_eq h0

instance : AddCommMonoid SignedDuration where
  add_zero := by simp [SignedDuration.eq_of_val_eq, SignedDuration.add_def, add_zero]
  zero_add := by simp [SignedDuration.eq_of_val_eq, SignedDuration.add_def, zero_add]
  nsmul_zero' := by simp [nsmul_rec]
  nsmul_succ' := by simp [nsmul_rec]
  add_comm := by simp [SignedDuration.eq_of_val_eq, SignedDuration.add_def, add_comm]

instance : Equiv Int SignedDuration where
  toFun := SignedDuration.mk
  invFun := SignedDuration.val
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

instance : AddMonoidWithOne SignedDuration where
  __ := inferInstanceAs (AddCommMonoid SignedDuration)
  natCast n := SignedDuration.mk (Int.ofNat n)
  natCast_zero := rfl
  natCast_succ _ := rfl

private theorem SignedDuration.sub_eq_add_neg (a b : SignedDuration) : a - b = a + -b := by
  simp [
    SignedDuration.sub_def, SignedDuration.add_def, SignedDuration.neg_def,
    HSub.hSub, Sub.sub, Int.sub
  ]

private theorem SignedDuration.add_left_neg (a : SignedDuration) : -a + a = 0 := by
  apply SignedDuration.eq_of_val_eq
  simp [SignedDuration.sub_def, SignedDuration.add_def, SignedDuration.neg_def]

instance : AddGroupWithOne SignedDuration where
  __ := inferInstanceAs (AddMonoidWithOne (SignedDuration))
  gsmul_zero' := by simp [gsmul_rec, nsmul_rec]
  gsmul_succ' := by simp [gsmul_rec, nsmul_rec, -Int.ofNat_eq_cast]
  gsmul_neg' := by simp [gsmul_rec, nsmul_rec, -Int.ofNat_eq_cast]
  sub_eq_add_neg := SignedDuration.sub_eq_add_neg
  add_left_neg := SignedDuration.add_left_neg
  intCast := SignedDuration.mk
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl