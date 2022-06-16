import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.Equiv.Basic
import Mathlib.Init.Function
import Mathlib.Data.Fin.Basic
import Timelib.Util
import Timelib.NanoPrecision.Duration.SignedDuration
import Timelib.NanoPrecision.Duration.UnsignedDuration

structure NaiveClockTime where
  nanos : Fin oneDayNanos
deriving DecidableEq, Repr

section NaiveClockTimeStuff

variable (t : NaiveClockTime)

instance : Inhabited <| NaiveClockTime := ⟨0, Nat.zero_lt_succ _⟩

theorem NaiveClockTime.eq_of_val_eq : ∀ {t₁ t₂ : NaiveClockTime} (h : t₁.nanos = t₂.nanos), t₁ = t₂
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- Addition of a `Duration` to a `NaiveClockTime`; wraps into the next clock cycle. -/
instance : HAdd NaiveClockTime SignedDuration NaiveClockTime where
  hAdd t d := ⟨t.nanos + Fin.ofInt'' d.val⟩

instance : HAdd SignedDuration NaiveClockTime NaiveClockTime where
  hAdd t d := d + t

theorem NaiveClockTime.hAdd_signed_def (dur : SignedDuration) : t + dur = ⟨t.nanos + Fin.ofInt'' dur.val⟩ := rfl

theorem NaiveClockTime.hAdd_comm (t : NaiveClockTime) (d : SignedDuration) : t + d = d + t := rfl
theorem NaiveClockTime.hAdd_assoc (t : NaiveClockTime) (d₁ d₂ : SignedDuration) : (t + d₁) + d₂ = t + (d₁ + d₂ ):= sorry

/-- 
Subtraction of a `Duration` from a `NaiveClockTime`; the implementation follows 
that of `Fin n`, wrapping into the previous clock cycle on underflow 
-/
instance : HSub NaiveClockTime SignedDuration NaiveClockTime where
  hSub t d := ⟨t.nanos - Fin.ofInt'' d.val⟩

theorem NaiveClockTime.hSub_signed_def (dur : SignedDuration) : t - dur = ⟨t.nanos - Fin.ofInt'' dur.val⟩ := rfl

def NaiveClockTime.nanoComponent (t : NaiveClockTime) : Nat := t.nanos.val % oneSecondNanos
def NaiveClockTime.secondComponent (t : NaiveClockTime) : Nat := (t.nanos.val % oneMinuteNanos) / oneSecondNanos
def NaiveClockTime.minuteComponent (t : NaiveClockTime) : Nat := (t.nanos.val % oneHourNanos) / oneMinuteNanos
def NaiveClockTime.hourComponent (t : NaiveClockTime) : Nat := t.nanos.val / oneHourNanos
def NaiveClockTime.asNanos   : Nat := t.nanos
def NaiveClockTime.asSeconds : Nat := t.nanos / oneSecondNanos
def NaiveClockTime.asMinutes : Nat := t.nanos / oneMinuteNanos
def NaiveClockTime.asHours   : Nat := t.nanos / oneHourNanos

def NaiveClockTime.fromSignedDuration (duration : SignedDuration) : NaiveClockTime := 
  ⟨(Fin.ofInt'' duration.val) % oneDayNanos⟩

def NaiveClockTime.fromHmsn (h : Nat) (m : Nat) (s : Nat) (n : Nat) : NaiveClockTime := 
  NaiveClockTime.fromSignedDuration ⟨(h * oneHourNanos) + (m * oneMinuteNanos) + (s * oneSecondNanos) + n⟩

instance : LT NaiveClockTime where
  lt := InvImage instLTFin.lt NaiveClockTime.nanos

instance : LE NaiveClockTime where
  le := InvImage instLEFin.le NaiveClockTime.nanos

@[simp] theorem NaiveClockTime.le_def (d₁ d₂ : NaiveClockTime) : (d₁ <= d₂) = (d₁.nanos <= d₂.nanos) := rfl
@[simp] theorem NaiveClockTime.lt_def (d₁ d₂ : NaiveClockTime) : (d₁ < d₂) = (d₁.nanos < d₂.nanos) := rfl

instance instDecidableLENaiveClockTime (a b : NaiveClockTime) : Decidable (a <= b) := inferInstanceAs (Decidable (a.nanos <= b.nanos))
instance instDecidableLTNaiveClockTime (a b : NaiveClockTime) : Decidable (a < b) := inferInstanceAs (Decidable (a.nanos < b.nanos))

instance : Equiv (Fin oneDayNanos) NaiveClockTime where
  toFun := NaiveClockTime.mk
  invFun := NaiveClockTime.nanos
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

instance : LinearOrder NaiveClockTime where
  le_refl (a) := le_refl a.nanos
  le_trans (a b c) := Nat.le_trans
  lt_iff_le_not_le (a b) := Nat.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply NaiveClockTime.eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp [NaiveClockTime.le_def, le_total]
  decidable_le := inferInstance

instance : ToString NaiveClockTime where
  toString t := 
    let h := String.leftpad 2 '0' (ToString.toString $ t.hourComponent)
    let m := String.leftpad 2 '0' (ToString.toString $ t.minuteComponent)
    let s := String.leftpad 2 '0' (ToString.toString $ t.secondComponent)
    let n := String.leftpad 9 '0' (ToString.toString $ t.nanoComponent)
  s!"{h}:{m}:{s}.{n}"

end NaiveClockTimeStuff 

