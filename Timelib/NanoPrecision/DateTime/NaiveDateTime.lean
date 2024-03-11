import Mathlib.Data.Nat.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Basic
import Mathlib.Data.String.Defs
import Mathlib.Data.String.Lemmas
import Mathlib.Logic.Equiv.Basic
import Timelib.Util
import Timelib.Date.ScalarDate
import Timelib.Date.Convert
import Timelib.NanoPrecision.Duration.SignedDuration
import Timelib.NanoPrecision.Duration.UnsignedDuration
import Timelib.NanoPrecision.ClockTime.NaiveClockTime
import Lean.Data.Json

/--
If nonnegative, the number of nanoseconds since the epoch (midnight of 0001/Jan/01)
If negative, the number of nanoseconds until the epoch (midnight of 0001/Jan/01)
-/
structure NaiveDateTime where
  nanos : Int
deriving DecidableEq, Hashable, Repr, Lean.ToJson, Lean.FromJson



namespace NaiveDateTime



instance instInhabited : Inhabited NaiveDateTime where
  default := ⟨0⟩

instance instOrd : Ord NaiveDateTime where
  compare l r := compare l.nanos r.nanos

/-
Using `Int.fdiv`, because we have a positive denominator, and we want to round
down if `dt.nanos` is negative, up if it's nonnegative.
-/
def toScalarDate (dt : NaiveDateTime) : ScalarDate :=
  ⟨(dt.nanos.fdiv oneDayNanos) + 1⟩

def dayOfWeek (dt : NaiveDateTime) : Int :=
  dt.toScalarDate.dayOfWeek

/-- The `DateTime` as of midnight (00:00:00 uninterpreted) on the ymd. We
subtract one to account for the fact that `Date` is one day ahead of the
zero-based `NaiveDateTime`.
-/
def fromYmd
  (y : Year)
  (m : Month)
  (d : Nat)
  (hd : 1 <= d ∧ d <= m.numDays y := by decide)
: NaiveDateTime :=
  ⟨oneDayNanos * ((Ymd.mk y m d hd.left hd.right).toScalarDate.day - 1)⟩

def fromYmdsn
  (y : Year)
  (m : Month)
  (d : Nat)
  (s : Nat)
  (n : Nat)
  (hd : 1 <= d ∧ d <= m.numDays y := by decide)
: NaiveDateTime :=
  ⟨(fromYmd y m d hd).nanos + (oneSecondNanos * s) + n⟩

instance instEquivIntSelf : Equiv Int NaiveDateTime where
  toFun := mk
  invFun := nanos
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.LeftInverse, Function.RightInverse]

theorem eq_of_val_eq : ∀ {d1 d2 : NaiveDateTime},
  d1.nanos = d2.nanos → d1 = d2
| ⟨_⟩, _, rfl => rfl

theorem val_eq_of_eq : ∀ {d1 d2 : NaiveDateTime},
  d1 = d2 → d1.nanos = d2.nanos
| ⟨_⟩, _, rfl => rfl

theorem eq_def : ∀ {d1 d2 : NaiveDateTime},
  d1 = d2 ↔ d1.nanos = d2.nanos
:= ⟨val_eq_of_eq, eq_of_val_eq⟩

theorem val_ne_of_ne : ∀ {d1 d2 : NaiveDateTime},
  d1 ≠ d2 → d1.nanos ≠ d2.nanos
| ⟨x⟩, ⟨y⟩, h => by intro hh; apply h; exact congrArg mk hh

instance instLT : LT NaiveDateTime where
  lt := InvImage Int.lt nanos

instance instLE : LE NaiveDateTime where
  le := InvImage Int.le nanos

@[simp] theorem le_def (d₁ d₂ : NaiveDateTime) :
  (d₁ <= d₂) = (d₁.nanos <= d₂.nanos)
:= rfl

@[simp] theorem lt_def (d₁ d₂ : NaiveDateTime) :
  (d₁ < d₂) = (d₁.nanos < d₂.nanos)
:= rfl

instance instDecidableLENaiveDateTime (d₁ d₂ : NaiveDateTime) :
  Decidable (d₁ <= d₂)
:= inferInstanceAs (Decidable <| d₁.nanos <= d₂.nanos)

instance instDecidableLTNaiveDateTime (d₁ d₂ : NaiveDateTime) :
  Decidable (d₁ < d₂)
:= inferInstanceAs (Decidable <| d₁.nanos < d₂.nanos)

instance instLinearOrder : LinearOrder NaiveDateTime where
  le_refl (a) := le_refl a.nanos
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp [le_def, le_total]
  decidableLE := inferInstance
  compare_eq_compareOfLessAndEq := by
    simp [compare, compareOfLessAndEq, lt_def, eq_def]

def seconds (d : NaiveDateTime) : Int := d.nanos / oneSecondNanos

def fromNanos : Int → NaiveDateTime := mk

def toYmd (d : NaiveDateTime) : Ymd := d.toScalarDate.toYmd

def year (d : NaiveDateTime) : Year := d.toScalarDate.year

instance instToString : ToString NaiveDateTime where
  toString dt :=
    let ⟨y, m, d, _, _⟩ := dt.toYmd
    let t : String :=
      Fin.ofInt'' (dt.nanos % (↑oneDayNanos))
      |> NaiveClockTime.mk
      |> ToString.toString
    s!"{y}/{m.toNat}/{d}; {t}"

@[reducible]
def dateEq : NaiveDateTime → NaiveDateTime → Prop
| n₁, n₂ => n₁.toScalarDate = n₂.toScalarDate

def dateEq.Equivalence : Equivalence dateEq := {
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h h' => Eq.trans h h'
}

instance instNaiveDateTimeSetoid : Setoid NaiveDateTime :=
  ⟨dateEq, dateEq.Equivalence⟩

instance instDecidable_dateEq (d₁ d₂ : NaiveDateTime) :
  Decidable <| d₁.dateEq d₂
:= inferInstance

instance instOfNat {n : Nat} : OfNat NaiveDateTime n where
  ofNat := ⟨n⟩

instance instHAddSelfSignedDurationSelf :
  HAdd NaiveDateTime SignedDuration NaiveDateTime
where
  hAdd da du := ⟨da.nanos + du.val⟩

instance instHAddSignedDurationSelfSelf :
  HAdd SignedDuration NaiveDateTime NaiveDateTime
where
  hAdd du da := da + du

theorem hAdd_signed_def (d : NaiveDateTime) (dur : SignedDuration) :
  d + dur = ⟨d.nanos + dur.val⟩
:= rfl
theorem hAdd_signed_def_rev (d : NaiveDateTime) (dur : SignedDuration) :
  dur + d = ⟨d.nanos + dur.val⟩
:= rfl

instance instHSubSelfSignedDurationSelf :
  HSub NaiveDateTime SignedDuration NaiveDateTime
where
  hSub t dur := t + -dur

theorem hSub_signed_def (d : NaiveDateTime) (dur : SignedDuration) :
  d - dur = d + -dur
:= rfl

theorem hAdd_signed_sub_cancel (t : NaiveDateTime) (d : SignedDuration) :
  t + d - d = t
:= by
  apply eq_of_val_eq
  simp [hSub_signed_def, hAdd_signed_def]
  apply Int.add_neg_cancel_right

theorem hAdd_signed_sub_add_cancel (t : NaiveDateTime) (d : SignedDuration) :
  t - d + d = t
:= by
  simp [hSub_signed_def, hAdd_signed_def]
  exact eq_of_val_eq (Int.sub_add_cancel t.nanos d.val)

theorem hAdd_signed_comm (t : NaiveDateTime) (d : SignedDuration) :
  t + d = d + t
:= by
  simp [hAdd_signed_def, hAdd_signed_def_rev]

instance instHAddSelfUnsignedDurationSelf :
  HAdd NaiveDateTime UnsignedDuration NaiveDateTime
where
  hAdd da du := ⟨da.nanos + du.val⟩

instance instHAddUnsignedDurationSelfSelf :
  HAdd UnsignedDuration NaiveDateTime NaiveDateTime
where
  hAdd du da := da + du

theorem hAdd_unsigned_def (d : NaiveDateTime) (dur : UnsignedDuration) :
  d + dur = ⟨d.nanos + dur.val⟩
:= rfl

instance instHSubSelfUnsignedDurationSelf :
  HSub NaiveDateTime UnsignedDuration NaiveDateTime
where
  hSub da du := ⟨da.nanos - du.val⟩

theorem hSub_unsigned_def (d : NaiveDateTime) (dur : UnsignedDuration) :
  d - dur = ⟨d.nanos - dur.val⟩
:= rfl

theorem hAdd_unsigned_sub_cancel (t : NaiveDateTime) (d : UnsignedDuration) :
  t + d - d = t
:= hAdd_signed_sub_cancel t d

theorem hAdd_unsigned_sub_add_cancel
  (t : NaiveDateTime) (d : UnsignedDuration)
: t - d + d = t
:= hAdd_signed_sub_add_cancel t d

theorem hAdd_unsigned_comm (t : NaiveDateTime) (d : UnsignedDuration) :
  t + d = d + t
:= hAdd_signed_comm t d

/--
Set the clock time of the current day to `tgt`.
-/
@[reducible]
def setClockTime (t : NaiveDateTime) (clockTime : NaiveClockTime) :
  NaiveDateTime
:=
  let days := (t.nanos.fdiv oneDayNanos) * oneDayNanos
  ⟨days + clockTime.nanos.val⟩
