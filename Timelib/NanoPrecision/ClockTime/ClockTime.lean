import Mathlib.Data.Nat.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Logic.Equiv.Basic
import Mathlib.Init.Function
import Mathlib.Data.Fin.Basic
import Timelib.Util
import Timelib.NanoPrecision.TimeZone.Basic
import Timelib.NanoPrecision.Duration.SignedDuration
import Timelib.NanoPrecision.Duration.UnsignedDuration
import Timelib.NanoPrecision.ClockTime.NaiveClockTime
import Lean.Data.Json



structure ClockTime (A : TimeZone) where
  naive : NaiveClockTime
deriving DecidableEq, Hashable, Repr, Lean.ToJson, Lean.FromJson



namespace ClockTime



instance instOrd : Ord (ClockTime A) where
  compare a b := compare a.naive b.naive

protected def default : ClockTime A :=
  ⟨default⟩

instance instInhabited : Inhabited <| ClockTime A :=
  ⟨⟨default⟩⟩



theorem eq_of_val_eq : ∀ {t₁ t₂ : ClockTime A},
  t₁.naive = t₂.naive → t₁ = t₂
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem val_eq_of_eq : ∀ {t₁ t₂ : ClockTime A},
  t₁ = t₂ → t₁.naive = t₂.naive
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem eq_def : ∀ {t₁ t₂ : ClockTime A},
  t₁ = t₂ ↔ t₁.naive = t₂.naive
:= ⟨val_eq_of_eq, eq_of_val_eq⟩



/-- Addition of a `SignedDuration` to a `ClockTime`; wraps into the next clock
cycle. -/
instance instHAddSelfSignedDurationSelf :
  HAdd (ClockTime A) SignedDuration (ClockTime A)
where
  hAdd t d := ⟨t.naive + d⟩

instance instHAddSignedDurationSelfSelf :
  HAdd SignedDuration (ClockTime A) (ClockTime A)
where
  hAdd t d := d + t

section hAdd_lemmas
  variable
    (t : ClockTime A)
    (d d₁ d₂ : SignedDuration)

  theorem hAdd_signed_def : t + d = ⟨t.naive + d⟩ :=
    rfl
  theorem hAdd_comm : t + d = d + t :=
    rfl
  theorem hAdd_assoc : (t + d₁) + d₂ = t + (d₁ + d₂ ) :=
    sorry
end hAdd_lemmas



/-- Subtraction of a `SignedDuration` from a `ClockTime`. The implementation
follows that of `Fin n`, wrapping into the previous clock cycle on underflow.
-/
instance instHSubSelfSignedDurationSelf :
  HSub (ClockTime A) SignedDuration (ClockTime A)
where
  hSub t d := ⟨t.naive - d⟩


theorem hSub_signed_def (t : ClockTime A) (d : SignedDuration) :
  t - d = ⟨t.naive - d⟩
:= rfl


def toLocalNaive (t : ClockTime A) : NaiveClockTime :=
  t.naive + A.offset



section
  variable {A : TimeZone} (t : ClockTime A)

  theorem apply_unapply {A : TimeZone} : t + A.offset - A.offset = t := by
    simp [
      hAdd_signed_def, hSub_signed_def,
      NaiveClockTime.hAdd_signed_def, NaiveClockTime.hSub_signed_def,
      sub_eq_add_neg, add_assoc
    ]

  theorem unapply_apply {A : TimeZone} : t - A.offset + A.offset = t := by
    simp [
      hAdd_signed_def, hSub_signed_def,
      NaiveClockTime.hAdd_signed_def, NaiveClockTime.hSub_signed_def,
      sub_eq_add_neg, add_assoc
    ]
end



section
  variable (t : ClockTime A)

  /- The nanosecond component of a `ClockTime`. To convert a `ClockTime` to
  nanoseconds, use `ClockTime.asNanos`.
  -/
  def nanoComponent : Nat :=
    t.toLocalNaive.nanoComponent
  def secondComponent : Nat :=
    t.toLocalNaive.secondComponent
  def minuteComponent : Nat :=
    t.toLocalNaive.minuteComponent
  def hourComponent : Nat :=
    t.toLocalNaive.hourComponent

  def asNanos : Nat :=
    t.toLocalNaive.asNanos
  def asSeconds : Nat :=
    t.toLocalNaive.asSeconds
  def asMinutes : Nat :=
    t.toLocalNaive.asMinutes
  def asHours : Nat :=
    t.toLocalNaive.asHours
end



def fromNeutralSignedDuration (d : SignedDuration) : ClockTime A :=
  ⟨NaiveClockTime.fromSignedDuration d⟩

def fromNeutralHmsn (h : Nat) (m : Nat) (s : Nat) (n : Nat) : ClockTime A :=
  ⟨(h * oneHourNanos) + (m * oneMinuteNanos) + (s * oneSecondNanos) + n⟩
  |> fromNeutralSignedDuration

def fromLocalHmsn (h : Nat) (m : Nat) (s : Nat) (n : Nat) : ClockTime A :=
  let dur : SignedDuration :=
    ⟨(h * oneHourNanos) + (m * oneMinuteNanos) + (s * oneSecondNanos) + n⟩
  ⟨NaiveClockTime.fromSignedDuration (dur - A.offset)⟩



instance instLT : LT (ClockTime A) where
  lt := InvImage (NaiveClockTime.instLT.lt) naive

instance instLE : LE (ClockTime A) where
  le := InvImage (NaiveClockTime.instLE.le) naive

@[simp] theorem le_def (d₁ d₂ : ClockTime Z) :
  (d₁ <= d₂) = (d₁.naive <= d₂.naive)
:= rfl

@[simp] theorem lt_def (d₁ d₂ : ClockTime Z) :
  (d₁ < d₂) = (d₁.naive < d₂.naive)
:= rfl

section
  variable (a b : ClockTime A)

  instance instDecidableLE : Decidable (a <= b) :=
    inferInstanceAs (Decidable (a.naive <= b.naive))

  instance instDecidableLT : Decidable (a < b) :=
    inferInstanceAs (Decidable (a.naive < b.naive))
end



instance instEquivFinSelf : Equiv (Fin oneDayNanos) (ClockTime Z) where
  toFun fin := ClockTime.mk (NaiveClockTime.mk fin)
  invFun t :=  t.naive.nanos
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

instance instLinearOrder : LinearOrder (ClockTime Z) where
  le_refl (a) := le_refl a.naive
  le_trans (a b c) := Nat.le_trans
  lt_iff_le_not_le (a b) := Nat.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply ClockTime.eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp [ClockTime.le_def, le_total]
  decidableLE := inferInstance
  compare_eq_compareOfLessAndEq := by
    simp [compare, compareOfLessAndEq, lt_def, eq_def, NaiveClockTime.eq_def']

instance instToString : ToString (ClockTime A) where
  toString t :=
    let t := t.toLocalNaive
    let h := t.hourComponent   |> toString |> String.leftpad 2 '0'
    let m := t.minuteComponent |> toString |> String.leftpad 2 '0'
    let s := t.secondComponent |> toString |> String.leftpad 2 '0'
    let n := t.nanoComponent   |> toString |> String.leftpad 9 '0'
    s!"{h}:{m}:{s}.{n}{A.abbreviation}"
