import Mathlib.Data.Nat.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Logic.Equiv.Basic
import Mathlib.Init.Function
import Mathlib.Data.Fin.Basic
import Timelib.Util
import Timelib.NanoPrecision.Duration.SignedDuration
import Timelib.NanoPrecision.Duration.UnsignedDuration
import Lean.Data.Json



structure NaiveClockTime where
  nanos : Fin oneDayNanos
deriving DecidableEq, Hashable, Repr, Lean.ToJson, Lean.FromJson



namespace NaiveClockTime



instance instOrd : Ord NaiveClockTime where
  compare l r := compare l.nanos r.nanos

instance instInhabited : Inhabited NaiveClockTime :=
  ⟨0, Nat.zero_lt_succ _⟩



theorem eq_of_val_eq : ∀ {t₁ t₂ : NaiveClockTime},
  t₁.nanos = t₂.nanos → t₁ = t₂
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem eq_of_val_eq' : ∀ {t₁ t₂ : NaiveClockTime},
  t₁.nanos.val = t₂.nanos.val → t₁ = t₂
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem val_eq_of_eq : ∀ {t₁ t₂ : NaiveClockTime},
  t₁ = t₂ → t₁.nanos = t₂.nanos
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem val_eq_of_eq' : ∀ {t₁ t₂ : NaiveClockTime},
  t₁ = t₂ → t₁.nanos.val = t₂.nanos.val
| ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

theorem eq_def : ∀ {t₁ t₂ : NaiveClockTime},
  t₁ = t₂ ↔ t₁.nanos = t₂.nanos
:= ⟨val_eq_of_eq, eq_of_val_eq⟩

theorem eq_def' : ∀ {t₁ t₂ : NaiveClockTime},
  t₁ = t₂ ↔ t₁.nanos.val = t₂.nanos.val
:= ⟨val_eq_of_eq', eq_of_val_eq'⟩



/-- Addition of a `Duration` to a `NaiveClockTime`; wraps into the next clock
cycle. -/
instance instHAddSelfSignedDurationSelf :
  HAdd NaiveClockTime SignedDuration NaiveClockTime
where
  hAdd t d := ⟨t.nanos + Fin.ofInt'' d.val⟩

instance instHAddSignedDurationSelfSelf :
  HAdd SignedDuration NaiveClockTime NaiveClockTime
where
  hAdd t d := d + t

section hAdd_lemmas
  variable
    (t : NaiveClockTime)
    (d d₁ d₂ : SignedDuration)

  theorem hAdd_signed_def : t + d = ⟨t.nanos + Fin.ofInt'' d.val⟩ :=
    rfl
  theorem hAdd_comm : t + d = d + t :=
    rfl
  theorem hAdd_assoc : (t + d₁) + d₂ = t + (d₁ + d₂ ) :=
    sorry
end hAdd_lemmas



/-- Subtraction of a `Duration` from a `NaiveClockTime`; the implementation
follows that of `Fin n`, wrapping into the previous clock cycle on underflow.
-/
instance instHSubSelfSignedDurationSelf :
  HSub NaiveClockTime SignedDuration NaiveClockTime
where
  hSub t d := ⟨t.nanos - Fin.ofInt'' d.val⟩

theorem hSub_signed_def (t : NaiveClockTime) (d : SignedDuration) :
  t - d = ⟨t.nanos - Fin.ofInt'' d.val⟩
:= rfl



section
  variable (t : NaiveClockTime)

  def nanoComponent : Nat :=
    t.nanos.val % oneSecondNanos
  def secondComponent : Nat :=
    (t.nanos.val % oneMinuteNanos) / oneSecondNanos
  def minuteComponent : Nat :=
    (t.nanos.val % oneHourNanos) / oneMinuteNanos
  def hourComponent : Nat :=
    t.nanos.val / oneHourNanos

  def asNanos : Nat :=
    t.nanos
  def asSeconds : Nat :=
    t.nanos / oneSecondNanos
  def asMinutes : Nat :=
    t.nanos / oneMinuteNanos
  def asHours : Nat :=
    t.nanos / oneHourNanos
end

def fromSignedDuration (duration : SignedDuration) : NaiveClockTime :=
  ⟨(@Fin.ofInt'' oneDayNanos _ duration.val) % oneDayNanos⟩

def fromHmsn (h : Nat) (m : Nat) (s : Nat) (n : Nat) : NaiveClockTime :=
  ⟨(h * oneHourNanos) + (m * oneMinuteNanos) + (s * oneSecondNanos) + n⟩
  |> NaiveClockTime.fromSignedDuration




instance instLT : LT NaiveClockTime where
  lt l r := l.nanos < r.nanos

instance instLE : LE NaiveClockTime where
  le l r := l.nanos ≤ r.nanos

@[simp] theorem le_def (d₁ d₂ : NaiveClockTime) :
  (d₁ <= d₂) = (d₁.nanos <= d₂.nanos)
:= rfl

@[simp] theorem lt_def (d₁ d₂ : NaiveClockTime) :
  (d₁ < d₂) = (d₁.nanos < d₂.nanos)
:= rfl

section dec_le_lt
  variable (a b : NaiveClockTime)

  instance instDecidableLE : Decidable (a <= b) :=
    inferInstanceAs (Decidable (a.nanos <= b.nanos))

  instance instDecidableLT : Decidable (a < b) :=
    inferInstanceAs (Decidable (a.nanos < b.nanos))
end dec_le_lt



instance instEquivFinSelf : Equiv (Fin oneDayNanos) NaiveClockTime where
  toFun := mk
  invFun := nanos
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]

instance instLinearOrder : LinearOrder NaiveClockTime where
  le_refl (a) := le_refl a.nanos
  le_trans (a b c) := Nat.le_trans
  lt_iff_le_not_le (a b) := Nat.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp [le_total]
  decidableLE := inferInstance
  compare_eq_compareOfLessAndEq := by
    simp [compare, compareOfLessAndEq, eq_def']


instance instToString : ToString NaiveClockTime where
  toString t :=
    let h := t.hourComponent   |> toString |> String.leftpad 2 '0'
    let m := t.minuteComponent |> toString |> String.leftpad 2 '0'
    let s := t.secondComponent |> toString |> String.leftpad 2 '0'
    let n := t.nanoComponent   |> toString |> String.leftpad 9 '0'
    s!"{h}:{m}:{s}.{n}"
