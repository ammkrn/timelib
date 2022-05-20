import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Basic
import Mathlib.Data.String.Defs
import Mathlib.Data.String.Lemmas
import Mathlib.Data.Equiv.Basic
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
structure NaiveDateTime where
  nanos : Int
deriving DecidableEq, Ord, Repr

/-
Using `Int.fdiv`, because we have a positive denominator, and we want to round 
down if `dt.nanos` is negative, up if it's nonnegative.
-/
def NaiveDateTime.toScalarDate (dt : NaiveDateTime) : ScalarDate := ⟨(dt.nanos.fdiv oneDayNanos) + 1⟩

def NaiveDateTime.dayOfWeek (dt : NaiveDateTime) : Int := dt.toScalarDate.dayOfWeek

/--
The `DateTime` as of midnight (00:00:00 uninterpreted) on the ymd. 
We subtract one to account for the fact that `Date` is one day ahead of the zero-based `NaiveDateTime`.
-/
def NaiveDateTime.fromYmd 
  (y : Year)
  (m : Month)
  (d : Nat)
  (hd : 1 <= d ∧ d <= m.numDays y := by decide) : NaiveDateTime := 
    ⟨oneDayNanos * ((Ymd.mk y m d hd.left hd.right).toScalarDate.day - 1)⟩ 

def NaiveDateTime.fromYmdsn 
  (y : Year) 
  (m : Month) 
  (d : Nat) 
  (s : Nat)
  (n : Nat)
  (hd : 1 <= d ∧ d <= m.numDays y := by decide) : NaiveDateTime := 
    ⟨(NaiveDateTime.fromYmd y m d hd).nanos + (oneSecondNanos * s) + n⟩ 

instance : Equiv Int NaiveDateTime where
  toFun := NaiveDateTime.mk
  invFun := NaiveDateTime.nanos
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.LeftInverse, Function.RightInverse]

theorem NaiveDateTime.eq_of_val_eq : ∀ {d1 d2 : NaiveDateTime} (h : d1.nanos = d2.nanos), d1 = d2
| ⟨_⟩, _, rfl => rfl

theorem NaiveDateTime.val_ne_of_ne : ∀ {d1 d2 : NaiveDateTime} (h : d1 ≠ d2), d1.nanos ≠ d2.nanos
| ⟨x⟩, ⟨y⟩, h => by intro hh; apply h; exact congrArg NaiveDateTime.mk hh

instance : LT NaiveDateTime where
  lt := InvImage Int.lt NaiveDateTime.nanos

instance : LE NaiveDateTime where
  le := InvImage Int.le NaiveDateTime.nanos
  
@[simp] theorem NaiveDateTime.le_def (d₁ d₂ : NaiveDateTime) : (d₁ <= d₂) = (d₁.nanos <= d₂.nanos) := rfl
@[simp] theorem NaiveDateTime.lt_def (d₁ d₂ : NaiveDateTime) : (d₁ < d₂) = (d₁.nanos < d₂.nanos) := rfl

instance instDecidableLENaiveDateTime (d₁ d₂ : NaiveDateTime) : Decidable (d₁ <= d₂) := inferInstanceAs (Decidable <| d₁.nanos <= d₂.nanos)
instance instDecidableLTNaiveDateTime (d₁ d₂ : NaiveDateTime) : Decidable (d₁ < d₂) := inferInstanceAs (Decidable <| d₁.nanos < d₂.nanos)

instance : LinearOrder NaiveDateTime where
  le_refl (a) := le_refl a.nanos
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply NaiveDateTime.eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp [NaiveDateTime.le_def, le_total]
  decidable_le := inferInstance

def NaiveDateTime.seconds (d : NaiveDateTime) : Int := d.nanos / oneSecondNanos

def NaiveDateTime.fromNanos : Int → NaiveDateTime := NaiveDateTime.mk

def NaiveDateTime.toYmd (d : NaiveDateTime) : Ymd := d.toScalarDate.toYmd

instance : ToString NaiveDateTime where
  toString dt :=
    let ⟨y, m, d, _, _⟩ := dt.toYmd
    let t : String := ToString.toString <| NaiveClockTime.mk (Fin.ofInt'' dt.nanos)
    s!"{y}/{m.toNat}/{d}; {t}"

@[reducible]
def NaiveDateTime.dateEq : NaiveDateTime → NaiveDateTime → Prop
| n₁, n₂ => n₁.toScalarDate = n₂.toScalarDate

def NaiveDateTime.dateEq.Equivalence : Equivalence NaiveDateTime.dateEq := {
  refl := fun d => rfl
  symm := fun h => h.symm
  trans := fun h h' => Eq.trans h h'
}

instance instNaiveDateTimeSetoid : Setoid NaiveDateTime := 
  ⟨NaiveDateTime.dateEq, NaiveDateTime.dateEq.Equivalence⟩

instance (d₁ d₂ : NaiveDateTime) : Decidable <| d₁.dateEq d₂ := inferInstance

instance {n : Nat} : OfNat NaiveDateTime n where
  ofNat := ⟨n⟩

instance : HAdd NaiveDateTime SignedDuration NaiveDateTime where
  hAdd da du := ⟨da.nanos + du.val⟩

instance : HAdd SignedDuration NaiveDateTime NaiveDateTime where
  hAdd du da := da + du

theorem NaiveDateTime.hAdd_signed_def (d : NaiveDateTime) (dur : SignedDuration) : d + dur = ⟨d.nanos + dur.val⟩ := rfl
theorem NaiveDateTime.hAdd_signed_def_rev (d : NaiveDateTime) (dur : SignedDuration) : dur + d = ⟨d.nanos + dur.val⟩ := rfl

instance : HSub NaiveDateTime SignedDuration NaiveDateTime where
  hSub t dur := t + -dur

theorem NaiveDateTime.hSub_signed_def (d : NaiveDateTime) (dur : SignedDuration) : d - dur = d + -dur := rfl

theorem NaiveDateTime.hAdd_signed_sub_cancel (t : NaiveDateTime) (d : SignedDuration) : t + d - d = t := by
  apply NaiveDateTime.eq_of_val_eq
  simp [NaiveDateTime.hSub_signed_def, NaiveDateTime.hAdd_signed_def]
  apply Int.add_neg_cancel_right

theorem NaiveDateTime.hAdd_signed_sub_add_cancel (t : NaiveDateTime) (d : SignedDuration) : t - d + d = t := by
  simp [NaiveDateTime.hSub_signed_def, NaiveDateTime.hAdd_signed_def]
  exact NaiveDateTime.eq_of_val_eq (Int.sub_add_cancel t.nanos d.val)

theorem NaiveDateTime.hAdd_signed_comm (t : NaiveDateTime) (d : SignedDuration) : t + d = d + t := by
  simp [NaiveDateTime.hAdd_signed_def, NaiveDateTime.hAdd_signed_def_rev]

instance : HAdd NaiveDateTime UnsignedDuration NaiveDateTime where
  hAdd da du := ⟨da.nanos + du.val⟩

instance : HAdd UnsignedDuration NaiveDateTime NaiveDateTime where
  hAdd du da := da + du

theorem NaiveDateTime.hAdd_unsigned_def (d : NaiveDateTime) (dur : UnsignedDuration) : d + dur = ⟨d.nanos + dur.val⟩ := rfl

instance : HSub NaiveDateTime UnsignedDuration NaiveDateTime where
  hSub da du := ⟨da.nanos - du.val⟩

theorem NaiveDateTime.hSub_unsigned_def (d : NaiveDateTime) (dur : UnsignedDuration) : d - dur = ⟨d.nanos - dur.val⟩ := rfl

theorem NaiveDateTime.hAdd_unsigned_sub_cancel (t : NaiveDateTime) (d : UnsignedDuration) : t + d - d = t := NaiveDateTime.hAdd_signed_sub_cancel t d

theorem NaiveDateTime.hAdd_unsigned_sub_add_cancel (t : NaiveDateTime) (d : UnsignedDuration) : t - d + d = t := NaiveDateTime.hAdd_signed_sub_add_cancel t d

theorem NaiveDateTime.hAdd_unsigned_comm (t : NaiveDateTime) (d : UnsignedDuration) : t + d = d + t := NaiveDateTime.hAdd_signed_comm t d
