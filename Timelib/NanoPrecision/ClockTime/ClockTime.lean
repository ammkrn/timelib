import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.Equiv.Basic
import Mathlib.Init.Function
import Mathlib.Data.Fin.Basic
import Timelib.Util
import Timelib.NanoPrecision.TimeZone.Basic
import Timelib.NanoPrecision.Duration.SignedDuration
import Timelib.NanoPrecision.Duration.UnsignedDuration
import Timelib.NanoPrecision.ClockTime.NaiveClockTime

structure ClockTime (A : TimeZone) where
  naive : NaiveClockTime
deriving DecidableEq, Repr

section ClockTimeStuff

variable {A : TimeZone} (t : ClockTime A)

instance : Inhabited <| ClockTime A := ⟨0, Nat.zero_lt_succ _⟩

theorem ClockTime.eq_of_val_eq : ∀ {t₁ t₂ : ClockTime A} (h : t₁.naive = t₂.naive), t₁ = t₂
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- Addition of a `SignedDuration` to a `ClockTime`; wraps into the next clock cycle. -/
instance : HAdd (ClockTime A) SignedDuration (ClockTime A) where
  hAdd t d := ⟨t.naive + d⟩

instance : HAdd SignedDuration (ClockTime A) (ClockTime A) where
  hAdd t d := d + t

theorem ClockTime.hAdd_signed_def (dur : SignedDuration) : t + dur = ⟨t.naive + dur⟩ := rfl
  
theorem ClockTime.hAdd_comm (t : ClockTime A) (d : SignedDuration) : t + d = d + t := rfl
theorem ClockTime.hAdd_assoc (t : ClockTime A) (d₁ d₂ : SignedDuration) : (t + d₁) + d₂ = t + (d₁ + d₂ ):= sorry

/-- 
Subtraction of a `SignedDuration` from a `ClockTime`; the implementation follows 
that of `Fin n`, wrapping into the previous clock cycle on underflow 
-/
instance : HSub (ClockTime A) SignedDuration (ClockTime A) where
  hSub t d := ⟨t.naive - d⟩


theorem ClockTime.hSub_signed_def (dur : SignedDuration) : t - dur = ⟨t.naive - dur⟩ := rfl


def ClockTime.toLocalNaive (t : ClockTime A) : NaiveClockTime := t.naive + A.offset

theorem ClockTime.apply_unapply : t + A.offset - A.offset = t := by
  simp [ClockTime.hAdd_signed_def, ClockTime.hSub_signed_def, NaiveClockTime.hAdd_signed_def, NaiveClockTime.hSub_signed_def, sub_eq_add_neg, add_assoc]

theorem ClockTime.unapply_apply : t - A.offset + A.offset = t := by
  simp [ClockTime.hAdd_signed_def, ClockTime.hSub_signed_def, NaiveClockTime.hAdd_signed_def, NaiveClockTime.hSub_signed_def, sub_eq_add_neg, add_assoc]

/- 
The nanosecond component of a `ClockTime`. To convert the `ClockTime` to
nanoseconds, use `ClockTime.asNanos`. 
-/
def ClockTime.nanoComponent (t : ClockTime A) : Nat := t.toLocalNaive.nanoComponent
def ClockTime.secondComponent (t : ClockTime A) : Nat := t.toLocalNaive.secondComponent
def ClockTime.minuteComponent (t : ClockTime A) : Nat := t.toLocalNaive.minuteComponent
def ClockTime.hourComponent (t : ClockTime A) : Nat := t.toLocalNaive.hourComponent

def ClockTime.fromNeutralSignedDuration (d : SignedDuration) : ClockTime A := ⟨NaiveClockTime.fromSignedDuration d⟩

def ClockTime.fromNeutralHmsn (h : Nat) (m : Nat) (s : Nat) (n : Nat) : ClockTime A := 
  ClockTime.fromNeutralSignedDuration ⟨(h * oneHourNanos) + (m * oneMinuteNanos) + (s * oneSecondNanos) + n⟩

def ClockTime.fromLocalHmsn (h : Nat) (m : Nat) (s : Nat) (n : Nat) : ClockTime A := 
  let dur : SignedDuration := ⟨(h * oneHourNanos) + (m * oneMinuteNanos) + (s * oneSecondNanos) + n⟩
  ⟨NaiveClockTime.fromSignedDuration (dur - A.offset)⟩

instance : LT (ClockTime A) where
  lt := InvImage (instLTNaiveClockTime.lt) ClockTime.naive

instance : LE (ClockTime A) where
  le := InvImage (instLENaiveClockTime.le) ClockTime.naive

@[simp] theorem ClockTime.le_def (d₁ d₂ : ClockTime Z) : (d₁ <= d₂) = (d₁.naive <= d₂.naive) := rfl
@[simp] theorem ClockTime.lt_def (d₁ d₂ : ClockTime Z) : (d₁ < d₂) = (d₁.naive < d₂.naive) := rfl

instance instDecidableLEClockTime (a b : ClockTime A) : Decidable (a <= b) := inferInstanceAs (Decidable (a.naive <= b.naive))
instance instDecidableLTClockTime (a b : ClockTime A) : Decidable (a < b) := inferInstanceAs (Decidable (a.naive < b.naive))

instance {Z : TimeZone} : Equiv (Fin oneDayNanos) (ClockTime Z) where
  toFun := fun fin => ClockTime.mk (NaiveClockTime.mk fin)
  invFun := fun t => t.naive.nanos
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

instance : LinearOrder (ClockTime Z) where
  le_refl (a) := le_refl a.naive
  le_trans (a b c) := Nat.le_trans
  lt_iff_le_not_le (a b) := Nat.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply ClockTime.eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp [ClockTime.le_def, le_total]
  decidable_le := inferInstance

instance : ToString (ClockTime A) where
  toString t := 
    let withTimeZone := t.toLocalNaive
    let h := String.leftpad 2 '0' (ToString.toString $ withTimeZone.hourComponent)
    let m := String.leftpad 2 '0' (ToString.toString $ withTimeZone.minuteComponent)
    let s := String.leftpad 2 '0' (ToString.toString $ withTimeZone.secondComponent)
    let n := String.leftpad 9 '0' (ToString.toString $ withTimeZone.nanoComponent)
  s!"{h}:{m}:{s}.{n}{A.abbreviation}" 

end ClockTimeStuff 
