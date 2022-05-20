import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Basic
import Mathlib.Data.String.Defs
import Mathlib.Data.String.Lemmas
import Mathlib.Data.Equiv.Basic
import Timelib.Util
import Timelib.NanoPrecision.Duration.SignedDuration
import Timelib.NanoPrecision.Duration.UnsignedDuration
import Timelib.NanoPrecision.DateTime.NaiveDateTime
import Timelib.NanoPrecision.TimeZone.Basic

structure Offset extends TimeZone where
  identifier : String
  utcToTaiAmt : NaiveDateTime → SignedDuration
  taiToUtcAmt : NaiveDateTime → SignedDuration

def Offset.taiToUtc (ω : Offset) (t : NaiveDateTime) := t + (ω.taiToUtcAmt t) 
def Offset.utcToTai (ω : Offset) (t : NaiveDateTime) := t + (ω.utcToTaiAmt t) 
def Offset.fullLocalOffset (ω : Offset) (t : NaiveDateTime) := (ω.taiToUtcAmt t) + ω.toTimeZone.offset

class LawfulOffset (ω : Offset) where
  applyRemoveIso : ∀ (parsed : NaiveDateTime), ω.taiToUtc (ω.utcToTai parsed) = parsed
  removeApplyIso : ∀ (tai : NaiveDateTime), ω.utcToTai (ω.taiToUtc tai) = tai

structure DateTime (ω : Offset) where
  naive : NaiveDateTime

section DateTimeStuff

variable {ω π : Offset}

/--
The underlying naive date time with the time zone and appropriate leap seconds applied.
-/
@[simp, reducible] 
abbrev DateTime.fullLocalOffset (t : DateTime ω) : SignedDuration := ω.fullLocalOffset t.naive

def DateTime.localDateTime (t : DateTime ω) : NaiveDateTime := t.naive + t.fullLocalOffset

/-- 
Use cases for this are probably rare, so make sure you know what you're getting.

`compareLocalTimes` compares the literal calendar/wall clock datetimes from two time 
stamps, without any regard for what underlying time they represent.
-/
def DateTime.compareLocal (t₁ : DateTime ω) (t₂ : DateTime π) : Ordering :=
  Ord.compare t₁.localDateTime t₂.localDateTime

def DateTime.localScalarDate (t : DateTime ω) : ScalarDate := t.localDateTime.toScalarDate
def DateTime.localYmd (t : DateTime ω) : Ymd := t.localDateTime.toYmd

theorem DateTime.eq_of_val_eq : ∀ {d₁ d₂ : DateTime ω} (h : d₁.naive = d₂.naive), d₁ = d₂
| ⟨_⟩, _, rfl => rfl

theorem DateTime.val_ne_of_ne : ∀ {d₁ d₂ : DateTime ω} (h : d₁ ≠ d₂), d₁.naive ≠ d₂.naive
| ⟨x⟩, ⟨y⟩, h => by intro hh; apply h; exact congrArg DateTime.mk hh

/-- Compares the underlying naive/TAI DateTime -/
instance : LT (DateTime ω) where
  lt := InvImage (instLTNaiveDateTime.lt) DateTime.naive

/-- Compares the underlying naive/TAI DateTime -/
instance : LE (DateTime ω) where
  le := InvImage (instLENaiveDateTime.le) DateTime.naive
  
@[simp] theorem DateTime.le_def (d₁ d₂ : DateTime ω) : (d₁ <= d₂) = (d₁.naive <= d₂.naive) := rfl
@[simp] theorem DateTime.lt_def (d₁ d₂ : DateTime ω) : (d₁ < d₂) = (d₁.naive < d₂.naive) := rfl

instance instDecidableLEDateTime (d₁ d₂ : DateTime ω) : Decidable (d₁ <= d₂) := inferInstanceAs (Decidable (d₁.naive <= d₂.naive))
instance instDecidableLTDateTime (d₁ d₂ : DateTime ω) : Decidable (d₁ < d₂) := inferInstanceAs (Decidable <| d₁.naive < d₂.naive)

instance : LinearOrder (DateTime ω) where
  le_refl (a) := le_refl a.naive
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    rw [DateTime.le_def] at h1 h2
    exact DateTime.eq_of_val_eq (le_antisymm h1 h2)
  le_total := by simp [DateTime.le_def, le_total]
  decidable_le := inferInstance

instance : HAdd (DateTime ω) SignedDuration (DateTime ω) where
  hAdd da du := ⟨da.naive + du⟩

instance : HAdd SignedDuration (DateTime ω) (DateTime ω)  where
  hAdd du da := da + du

theorem DateTime.hAdd_signed_def (d : DateTime ω) (dur : SignedDuration) : d + dur = ⟨d.naive + dur⟩ := rfl
theorem DateTime.hAdd_signed_def_rev (d : DateTime ω) (dur : SignedDuration) : dur + d = ⟨dur + d.naive⟩ := rfl

instance : HSub (DateTime ω) SignedDuration (DateTime ω) where
  hSub d dur := d + -dur

theorem DateTime.hSub_signed_def (d : DateTime ω) (dur : SignedDuration) : d - dur = d + -dur := rfl

instance : HAdd (DateTime ω) UnsignedDuration (DateTime ω) where
  hAdd da du := ⟨da.naive + du⟩

instance : HAdd UnsignedDuration (DateTime ω) (DateTime ω)  where
  hAdd du da := da + du

theorem DateTime.hAdd_def_unsigned (d : DateTime ω) (dur : UnsignedDuration) : d + dur = ⟨d.naive + dur⟩ := rfl

instance : HSub (DateTime ω) UnsignedDuration (DateTime ω) where
  hSub d dur := d - (dur : SignedDuration)

theorem DateTime.hSub_def_unsigned (d : DateTime ω) (dur : UnsignedDuration) : d - dur = d + -(dur : SignedDuration) := rfl

theorem DateTime.hAdd_signed_assoc (d : DateTime ω) (dur₁ dur₂ : SignedDuration) : d + dur₁ + dur₂ = d + (dur₁ + dur₂) := by
  simp [DateTime.hAdd_signed_def, NaiveDateTime.hAdd_signed_def]
  exact Int.add_assoc _ _ _

theorem DateTime.hAdd_signed_comm (d : DateTime ω) (dur : SignedDuration) : d + dur = dur + d := by
  simp [DateTime.hAdd_signed_def, NaiveDateTime.hAdd_signed_def, DateTime.hAdd_signed_def_rev, NaiveDateTime.hAdd_signed_def_rev]

end DateTimeStuff
