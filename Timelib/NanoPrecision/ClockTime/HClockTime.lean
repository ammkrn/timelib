import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.String.Defs
import Mathlib.Data.String.Lemmas
import Mathlib.Data.Equiv.Basic
import Mathlib.Init.Function
import Timelib.Util
import Timelib.NanoPrecision.TimeZone.Basic
import Timelib.NanoPrecision.Duration.UnsignedDuration
import Timelib.NanoPrecision.Duration.SignedDuration
import Timelib.NanoPrecision.ClockTime.ClockTime

structure HClockTime where
  timeZone : TimeZone
  clockTime : ClockTime timeZone

def HClockTime.EquivSigma : Equiv HClockTime (Sigma ClockTime) := {
  toFun := fun oct => ⟨oct.timeZone, oct.clockTime⟩ 
  invFun := fun sig => ⟨sig.fst, sig.snd⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
}

section HClockTimeStuff

variable (t : HClockTime)

@[reducible]
def HClockTime.simultaneous : HClockTime → HClockTime → Prop
| ⟨_, ⟨naive_t₁⟩⟩, ⟨_, ⟨naive_t₂⟩⟩ => naive_t₁ = naive_t₂

def HClockTime.simultaneous.equivalence : Equivalence HClockTime.simultaneous :=  {
  refl := fun d => rfl
  symm := fun h => h.symm
  trans := fun h h' => Eq.trans h h'
}

instance instHClockTimeSetoid : Setoid HClockTime := ⟨HClockTime.simultaneous, HClockTime.simultaneous.equivalence⟩

instance : Inhabited <| HClockTime := ⟨TimeZone.UTC, Inhabited.default⟩

def HClockTime.nanoComponent : Nat := t.clockTime.nanoComponent
def HClockTime.secondComponent : Nat := t.clockTime.secondComponent
def HClockTime.minuteComponent : Nat := t.clockTime.minuteComponent
def HClockTime.hourComponent : Nat := t.clockTime.hourComponent

/-- 
Addition of a `Duration` to a `ClockTime`; wraps into the next clock cycle. 
-/
instance : HAdd HClockTime SignedDuration HClockTime where
  hAdd t d := { t with clockTime := t.clockTime + d }

theorem HClockTime.hAdd_signed_def (dur : SignedDuration) : t + dur = { t with clockTime := t.clockTime + dur } := rfl

/-- 
Subtraction of a `SignedDuration` from a `ClockTime`; the implementation follows 
that of `Fin oneDayNanos`, wrapping into the previous clock cycle on underflow 
-/
instance : HSub HClockTime SignedDuration HClockTime where
  hSub t d := { t with clockTime := t.clockTime - d }

theorem HClockTime.hSub_signed_def (dur : SignedDuration) : t - dur = { t with clockTime := t.clockTime - dur } := rfl

theorem HClockTime.apply_unapply : t + t.timeZone.offset - t.timeZone.offset = t := by
  simp [HClockTime.hAdd_signed_def, HClockTime.hSub_signed_def]
  rw [HClockTime.mk.injEq]
  exact And.intro rfl (heq_of_eq (ClockTime.apply_unapply t.clockTime))

theorem HClockTime.unapply_apply : t - t.timeZone.offset + t.timeZone.offset = t := by
  simp [HClockTime.hAdd_signed_def, HClockTime.hSub_signed_def]
  rw [HClockTime.mk.injEq]
  exact And.intro rfl (heq_of_eq (ClockTime.unapply_apply t.clockTime))

/--
LT compares the underlying naive/TAI time.
-/
instance : LT HClockTime where
  lt := InvImage instLTNaiveClockTime.lt (fun t => t.clockTime.naive)

/--
LE compares the underlying naive/TAI time.
-/
instance : LE HClockTime where
  le := InvImage instLENaiveClockTime.le (fun t => t.clockTime.naive)

theorem HClockTime.le_def (d₁ d₂ : HClockTime) : (d₁ <= d₂) = (d₁.clockTime.naive <= d₂.clockTime.naive) := rfl
theorem HClockTime.lt_def (d₁ d₂ : HClockTime) : (d₁ < d₂) = (d₁.clockTime.naive < d₂.clockTime.naive) := rfl

instance instDecidableLTHClockTime (a b : HClockTime) : Decidable (a < b) := inferInstanceAs (Decidable (a.clockTime.naive < b.clockTime.naive))
instance instDecidableLEHClockTime (a b : HClockTime) : Decidable (a <= b) := inferInstanceAs (Decidable (a.clockTime.naive <= b.clockTime.naive))

/--
HClockTime is only a Preorder since it does not respect antisymmetry. 
t₁ <= t₂ ∧ t₂ <= t₁ does not imply t₁ = t₂ since they may have different timezones.
-/
instance : Preorder HClockTime where
  le_refl (a) := le_refl a.clockTime.naive
  le_trans (a b c) := Nat.le_trans
  lt_iff_le_not_le (a b) := Nat.lt_iff_le_not_le

end HClockTimeStuff
