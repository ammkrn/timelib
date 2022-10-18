import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.String.Defs
import Mathlib.Data.String.Lemmas
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Equiv.Basic
import Timelib.NanoPrecision.Duration.SignedDuration

/-- 
A unsigned duration in nanoseconds, implemented as a `Nat`. 

Arithmetic behaves as on `Nat`.
-/
structure UnsignedDuration where
  val : Nat
deriving DecidableEq, Ord, Repr

instance : Coe UnsignedDuration SignedDuration where
  coe u := ⟨u.val⟩

instance : Add UnsignedDuration where
  add a b := ⟨a.val + b.val⟩ 

@[simp]
theorem UnsignedDuration.add_def (a b : UnsignedDuration) : a + b = ⟨a.val + b.val⟩ := rfl

instance : Sub UnsignedDuration where
  sub a b := ⟨a.val - b.val⟩ 

@[simp] 
theorem UnsignedDuration.sub_def (a b : UnsignedDuration) : a - b = ⟨a.val - b.val⟩ := rfl

instance : HMul UnsignedDuration Nat UnsignedDuration where
  hMul d n := ⟨d.val * n⟩ 

instance : HMod UnsignedDuration Nat UnsignedDuration where
  hMod a n := ⟨a.val % n⟩ 

instance : HDiv UnsignedDuration Nat UnsignedDuration where
  hDiv a b := ⟨a.val / b⟩ 

instance : HPow UnsignedDuration Nat UnsignedDuration where
  hPow a b := ⟨a.val ^ b⟩ 

instance : LT UnsignedDuration where
  lt := InvImage Nat.lt UnsignedDuration.val

instance : LE UnsignedDuration where
  le := InvImage Nat.le UnsignedDuration.val

theorem UnsignedDuration.le_def {d₁ d₂ : UnsignedDuration} : (d₁ <= d₂) = (d₁.val <= d₂.val) := rfl
theorem UnsignedDuration.lt_def {d₁ d₂ : UnsignedDuration} : (d₁ < d₂) = (d₁.val < d₂.val) := rfl

theorem UnsignedDuration.val_eq_of_eq : ∀ {d1 d2 : UnsignedDuration} (h : d1 = d2), d1.val = d2.val
| ⟨_⟩, _, rfl => rfl

theorem UnsignedDuration.eq_of_val_eq : ∀ {d1 d2 : UnsignedDuration} (h : d1.val = d2.val), d1 = d2
| ⟨_⟩, _, rfl => rfl

instance (a b : UnsignedDuration) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : UnsignedDuration) : Decidable (a <= b) := inferInstanceAs (Decidable (a.val <= b.val))

instance : LinearOrder UnsignedDuration where
  le_refl (a) := le_refl a.val
  le_trans (a b c) := Nat.le_trans
  lt_iff_le_not_le (a b) := Nat.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply UnsignedDuration.eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp [UnsignedDuration.le_def, le_total]
  decidable_le := inferInstance

theorem UnsignedDuration.monotone {d₁ d₂ : UnsignedDuration} : d₁.val <= d₂.val -> d₁ <= d₂ := 
  fun h => (UnsignedDuration.le_def) ▸ h
  
@[reducible] def UnsignedDuration.toNanos (d : UnsignedDuration) : Nat := d.val
@[reducible] def UnsignedDuration.toSeconds (d : UnsignedDuration) : Nat := d.val / oneSecondNanos
@[reducible] def UnsignedDuration.toMinutes (d : UnsignedDuration) : Nat := d.val / oneMinuteNanos
@[reducible] def UnsignedDuration.toHours (d : UnsignedDuration) : Nat := d.val / oneHourNanos
@[reducible] def UnsignedDuration.toDays (d : UnsignedDuration) : Nat := d.val / oneDayNanos
@[reducible] def UnsignedDuration.toWeeks (d : UnsignedDuration) : Nat := d.val / oneWeekNanos
@[reducible] def UnsignedDuration.toNonLeapYears (d : UnsignedDuration) : Nat := d.val / (365 * oneDayNanos)

@[reducible] def UnsignedDuration.fromNanos (n : Nat) : UnsignedDuration := ⟨n⟩ 
@[reducible] def UnsignedDuration.fromSeconds (n : Nat) : UnsignedDuration := ⟨n * oneSecondNanos⟩
@[reducible] def UnsignedDuration.fromMinutes (n : Nat) : UnsignedDuration := ⟨n * oneMinuteNanos⟩ 
@[reducible] def UnsignedDuration.fromHours (n : Nat) : UnsignedDuration := ⟨n * oneHourNanos⟩ 
@[reducible] def UnsignedDuration.fromWeeks (n : Nat) : UnsignedDuration := ⟨n * oneWeekNanos⟩
@[reducible] def UnsignedDuration.fromDays (n : Nat) : UnsignedDuration := ⟨n * oneDayNanos⟩ 
@[reducible] def UnsignedDuration.fromNonLeapYears (n : Nat) : UnsignedDuration := ⟨n * oneYearNanos⟩

instance (n : Nat) : OfNat UnsignedDuration n where
  ofNat := ⟨n⟩ 

@[simp] theorem UnsignedDuration.zero_def : (0 : UnsignedDuration).val = (0 : Nat) := by rfl

instance : ToString UnsignedDuration where
  toString d := 
    let secs := String.leftpad 2 '0' s!"{d.toSeconds}"
    let nanos := String.leftpad 9 '0' s!"{d.toNanos % oneSecondNanos}"
    s!"P{secs}.{nanos}S"

instance : AddCommSemigroup UnsignedDuration := {
  add_assoc := fun a b c => by simp [UnsignedDuration.add_def, AddSemigroup.add_assoc]
  add_comm := fun a b => by simp [UnsignedDuration.add_def]; exact AddCommSemigroup.add_comm (A := Nat) _ _
}

instance : IsAddLeftCancel UnsignedDuration where
  add_left_cancel := fun a b c => by
    simp [UnsignedDuration.add_def] 
    have h0 := @Nat.add_left_cancel a.val b.val c.val
    intro h1
    specialize h0 h1
    exact UnsignedDuration.eq_of_val_eq h0
  
instance : IsAddRightCancel UnsignedDuration where
  add_right_cancel := fun a b c => by
    simp [UnsignedDuration.add_def] 
    have h0 := @Nat.add_right_cancel b.val a.val c.val
    intro h1
    specialize h0 h1
    exact UnsignedDuration.eq_of_val_eq h0

instance : AddCommMonoid UnsignedDuration where
  add_zero := by simp [UnsignedDuration.eq_of_val_eq, UnsignedDuration.add_def, add_zero]
  zero_add := by simp [UnsignedDuration.eq_of_val_eq, UnsignedDuration.add_def, zero_add]
  nsmul_zero' := by simp [nsmul_rec]
  nsmul_succ' := by simp [nsmul_rec]
  add_comm := by simp [UnsignedDuration.eq_of_val_eq, UnsignedDuration.add_def, add_comm]

instance : Equiv Nat UnsignedDuration where
  toFun := UnsignedDuration.mk
  invFun := UnsignedDuration.val
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
