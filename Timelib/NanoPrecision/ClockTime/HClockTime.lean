import Mathlib.Tactic.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Data.String.Defs
import Mathlib.Data.String.Lemmas
import Mathlib.Logic.Equiv.Basic
import Mathlib.Init.Function
import Timelib.Util
import Timelib.NanoPrecision.TimeZone.Basic
import Timelib.NanoPrecision.Duration.UnsignedDuration
import Timelib.NanoPrecision.Duration.SignedDuration
import Timelib.NanoPrecision.ClockTime.ClockTime



structure HClockTime where
  timeZone : TimeZone
  clockTime : ClockTime timeZone



namespace HClockTime



def EquivSigma : Equiv HClockTime (Sigma ClockTime) where
  toFun oct := ⟨oct.timeZone, oct.clockTime⟩
  invFun sig := ⟨sig.fst, sig.snd⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]



@[reducible]
def simultaneous : HClockTime → HClockTime → Prop
| ⟨_, ⟨naive_t₁⟩⟩, ⟨_, ⟨naive_t₂⟩⟩ => naive_t₁ = naive_t₂

def simultaneous.equivalence : Equivalence HClockTime.simultaneous where
  refl _d := rfl
  symm h := h.symm
  trans h h' := Eq.trans h h'



instance instSetoid : Setoid HClockTime :=
  ⟨HClockTime.simultaneous, HClockTime.simultaneous.equivalence⟩

instance instInhabited : Inhabited <| HClockTime :=
  ⟨TimeZone.UTC, default⟩



section
  variable (t : HClockTime)

  def nanoComponent   : Nat := t.clockTime.nanoComponent
  def secondComponent : Nat := t.clockTime.secondComponent
  def minuteComponent : Nat := t.clockTime.minuteComponent
  def hourComponent   : Nat := t.clockTime.hourComponent
end



/--
Addition of a `Duration` to a `ClockTime`; wraps into the next clock cycle.
-/
instance instHAddSelfSignedDurationSelf :
  HAdd HClockTime SignedDuration HClockTime
where
  hAdd t d := { t with clockTime := t.clockTime + d }

/-- Subtraction of a `SignedDuration` from a `ClockTime`; the implementation
follows that of `Fin oneDayNanos`, wrapping into the previous clock cycle on
underflow. -/
instance instHSubSelfSignedDurationSelf :
  HSub HClockTime SignedDuration HClockTime
where
  hSub t d := { t with clockTime := t.clockTime - d }

section
  variable (t : HClockTime) (d : SignedDuration)

  theorem hAdd_signed_def : t + d = { t with clockTime := t.clockTime + d } :=
    rfl

  theorem hSub_signed_def : t - d = { t with clockTime := t.clockTime - d } :=
    rfl

  theorem apply_unapply : t + t.timeZone.offset - t.timeZone.offset = t := by
    simp [HClockTime.hAdd_signed_def, HClockTime.hSub_signed_def]
    rw [HClockTime.mk.injEq]
    exact And.intro rfl (heq_of_eq $ ClockTime.apply_unapply t.clockTime)

  theorem unapply_apply : t - t.timeZone.offset + t.timeZone.offset = t := by
    simp [HClockTime.hAdd_signed_def, HClockTime.hSub_signed_def]
    rw [HClockTime.mk.injEq]
    exact And.intro rfl (heq_of_eq $ ClockTime.unapply_apply t.clockTime)
end

/-- LT compares the underlying naive/TAI time. -/
instance instLT : LT HClockTime where
  lt := InvImage NaiveClockTime.instLT.lt (fun t => t.clockTime.naive)

/-- LE compares the underlying naive/TAI time. -/
instance instLE : LE HClockTime where
  le := InvImage NaiveClockTime.instLE.le (fun t => t.clockTime.naive)

theorem HClockTime.le_def (d₁ d₂ : HClockTime) :
  (d₁ <= d₂) = (d₁.clockTime.naive <= d₂.clockTime.naive)
:= rfl
theorem HClockTime.lt_def (d₁ d₂ : HClockTime) :
  (d₁ < d₂) = (d₁.clockTime.naive < d₂.clockTime.naive)
:= rfl

instance instDecidableLT (a b : HClockTime) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.clockTime.naive < b.clockTime.naive))
instance instDecidableLE (a b : HClockTime) : Decidable (a <= b) :=
  inferInstanceAs (Decidable (a.clockTime.naive <= b.clockTime.naive))

/-- HClockTime is only a Preorder since it does not respect antisymmetry:
`t₁ <= t₂ ∧ t₂ <= t₁` does not imply `t₁ = t₂` since they may have different
timezones.
-/
instance instPreorder : Preorder HClockTime where
  le_refl a := le_refl a.clockTime.naive
  le_trans _a _b _c := Nat.le_trans
  lt_iff_le_not_le _a _b := Nat.lt_iff_le_not_le
