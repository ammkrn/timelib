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

/--
If nonnegative, the number of nanoseconds since the epoch (midnight of 0001/Jan/01)
If negative, the number of nanoseconds until the epoch (midnight of 0001/Jan/01)
-/
structure TaiDateTime where
  nanos : Int
deriving DecidableEq, Ord, Repr

instance : Inhabited TaiDateTime where
  default := ⟨0⟩

/-
Using `Int.fdiv`, because we have a positive denominator, and we want to round
down if `dt.nanos` is negative, up if it's nonnegative.
-/
def TaiDateTime.toScalarDate (dt : TaiDateTime) : ScalarDate := ⟨(dt.nanos.fdiv oneDayNanos) + 1⟩

def TaiDateTime.dayOfWeek (dt : TaiDateTime) : Int := dt.toScalarDate.dayOfWeek

/--
The `DateTime` as of midnight (00:00:00 uninterpreted) on the ymd.
We subtract one to account for the fact that `Date` is one day ahead of the zero-based `TaiDateTime`.
-/
def TaiDateTime.fromYmd
  (y : Year)
  (m : Month)
  (d : Nat)
  (hd : 1 <= d ∧ d <= m.numDays y := by decide) : TaiDateTime :=
    ⟨oneDayNanos * ((Ymd.mk y m d hd.left hd.right).toScalarDate.day - 1)⟩

def TaiDateTime.fromYmdsn
  (y : Year)
  (m : Month)
  (d : Nat)
  (s : Nat)
  (n : Nat)
  (hd : 1 <= d ∧ d <= m.numDays y := by decide) : TaiDateTime :=
    ⟨(TaiDateTime.fromYmd y m d hd).nanos + (oneSecondNanos * s) + n⟩

instance : Equiv Int TaiDateTime where
  toFun := TaiDateTime.mk
  invFun := TaiDateTime.nanos
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.LeftInverse, Function.RightInverse]

theorem TaiDateTime.eq_of_val_eq : ∀ {d1 d2 : TaiDateTime} (h : d1.nanos = d2.nanos), d1 = d2
| ⟨_⟩, _, rfl => rfl

theorem TaiDateTime.val_ne_of_ne : ∀ {d1 d2 : TaiDateTime} (h : d1 ≠ d2), d1.nanos ≠ d2.nanos
| ⟨x⟩, ⟨y⟩, h => by intro hh; apply h; exact congrArg TaiDateTime.mk hh

instance : LT TaiDateTime where
  lt := InvImage Int.lt TaiDateTime.nanos

instance : LE TaiDateTime where
  le := InvImage Int.le TaiDateTime.nanos

@[simp] theorem TaiDateTime.le_def (d₁ d₂ : TaiDateTime) : (d₁ <= d₂) = (d₁.nanos <= d₂.nanos) := rfl
@[simp] theorem TaiDateTime.lt_def (d₁ d₂ : TaiDateTime) : (d₁ < d₂) = (d₁.nanos < d₂.nanos) := rfl

instance instDecidableLETaiDateTime (d₁ d₂ : TaiDateTime) : Decidable (d₁ <= d₂) := inferInstanceAs (Decidable <| d₁.nanos <= d₂.nanos)
instance instDecidableLTTaiDateTime (d₁ d₂ : TaiDateTime) : Decidable (d₁ < d₂) := inferInstanceAs (Decidable <| d₁.nanos < d₂.nanos)

instance : LinearOrder TaiDateTime where
  le_refl (a) := le_refl a.nanos
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply TaiDateTime.eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp [TaiDateTime.le_def, le_total]
  decidableLE := inferInstance

def TaiDateTime.seconds (d : TaiDateTime) : Int := d.nanos / oneSecondNanos

def TaiDateTime.fromNanos : Int → TaiDateTime := TaiDateTime.mk

def TaiDateTime.toYmd (d : TaiDateTime) : Ymd := d.toScalarDate.toYmd

def TaiDateTime.year (d : TaiDateTime) : Year := d.toScalarDate.year

instance : ToString TaiDateTime where
  toString dt :=
    let ⟨y, m, d, _, _⟩ := dt.toYmd
    let t : String := ToString.toString <| NaiveClockTime.mk (Fin.ofInt'' (dt.nanos % (↑oneDayNanos)))
    s!"{y}/{m.toNat}/{d}; {t}"

@[reducible]
def TaiDateTime.dateEq : TaiDateTime → TaiDateTime → Prop
| n₁, n₂ => n₁.toScalarDate = n₂.toScalarDate

def TaiDateTime.dateEq.Equivalence : Equivalence TaiDateTime.dateEq := {
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h h' => Eq.trans h h'
}

instance instTaiDateTimeSetoid : Setoid TaiDateTime :=
  ⟨TaiDateTime.dateEq, TaiDateTime.dateEq.Equivalence⟩

instance (d₁ d₂ : TaiDateTime) : Decidable <| d₁.dateEq d₂ := inferInstance

instance {n : Nat} : OfNat TaiDateTime n where
  ofNat := ⟨n⟩

instance : HAdd TaiDateTime SignedDuration TaiDateTime where
  hAdd da du := ⟨da.nanos + du.val⟩

instance : HAdd SignedDuration TaiDateTime TaiDateTime where
  hAdd du da := da + du

theorem TaiDateTime.hAdd_signed_def (d : TaiDateTime) (dur : SignedDuration) : d + dur = ⟨d.nanos + dur.val⟩ := rfl
theorem TaiDateTime.hAdd_signed_def_rev (d : TaiDateTime) (dur : SignedDuration) : dur + d = ⟨d.nanos + dur.val⟩ := rfl

instance : HSub TaiDateTime SignedDuration TaiDateTime where
  hSub t dur := t + -dur

theorem TaiDateTime.hSub_signed_def (d : TaiDateTime) (dur : SignedDuration) : d - dur = d + -dur := rfl

theorem TaiDateTime.hAdd_signed_sub_cancel (t : TaiDateTime) (d : SignedDuration) : t + d - d = t := by
  apply TaiDateTime.eq_of_val_eq
  simp [TaiDateTime.hSub_signed_def, TaiDateTime.hAdd_signed_def]
  apply Int.add_neg_cancel_right

theorem TaiDateTime.hAdd_signed_sub_add_cancel (t : TaiDateTime) (d : SignedDuration) : t - d + d = t := by
  simp [TaiDateTime.hSub_signed_def, TaiDateTime.hAdd_signed_def]
  exact TaiDateTime.eq_of_val_eq (Int.sub_add_cancel t.nanos d.val)

theorem TaiDateTime.hAdd_signed_comm (t : TaiDateTime) (d : SignedDuration) : t + d = d + t := by
  simp [TaiDateTime.hAdd_signed_def, TaiDateTime.hAdd_signed_def_rev]

instance : HAdd TaiDateTime UnsignedDuration TaiDateTime where
  hAdd da du := ⟨da.nanos + du.val⟩

instance : HAdd UnsignedDuration TaiDateTime TaiDateTime where
  hAdd du da := da + du

theorem TaiDateTime.hAdd_unsigned_def (d : TaiDateTime) (dur : UnsignedDuration) : d + dur = ⟨d.nanos + dur.val⟩ := rfl

instance : HSub TaiDateTime UnsignedDuration TaiDateTime where
  hSub da du := ⟨da.nanos - du.val⟩

theorem TaiDateTime.hSub_unsigned_def (d : TaiDateTime) (dur : UnsignedDuration) : d - dur = ⟨d.nanos - dur.val⟩ := rfl

theorem TaiDateTime.hAdd_unsigned_sub_cancel (t : TaiDateTime) (d : UnsignedDuration) : t + d - d = t := TaiDateTime.hAdd_signed_sub_cancel t d

theorem TaiDateTime.hAdd_unsigned_sub_add_cancel (t : TaiDateTime) (d : UnsignedDuration) : t - d + d = t := TaiDateTime.hAdd_signed_sub_add_cancel t d

theorem TaiDateTime.hAdd_unsigned_comm (t : TaiDateTime) (d : UnsignedDuration) : t + d = d + t := TaiDateTime.hAdd_signed_comm t d

/--
Set the clock time of the current day to `tgt`.
-/
@[reducible]
def TaiDateTime.setClockTime (t : TaiDateTime) (clockTime : NaiveClockTime) : TaiDateTime :=
  let days := (t.nanos.fdiv oneDayNanos) * oneDayNanos
  ⟨days + clockTime.nanos.val⟩
