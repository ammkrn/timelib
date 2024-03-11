import Mathlib.Data.Nat.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Basic
import Mathlib.Data.String.Defs
import Mathlib.Data.String.Lemmas
import Mathlib.Logic.Equiv.Basic
import Timelib.Util
import Timelib.NanoPrecision.Duration.SignedDuration
import Timelib.NanoPrecision.Duration.UnsignedDuration
import Timelib.NanoPrecision.DateTime.NaiveDateTime
import Timelib.NanoPrecision.TimeZone.Basic
import Lean.Data.Json

/-
I think you want a TAI type for the marker aspect if nothing else.
-/
structure Offset extends TimeZone where
  identifier : String
  leapSecondsToApply : NaiveDateTime → SignedDuration
  leapSecondsToRemove : NaiveDateTime → SignedDuration

abbrev Offset.timeZoneOffset (ω : Offset) := ω.toTimeZone.offset
abbrev Offset.taiToUtc (ω : Offset) (t : NaiveDateTime) := t + (ω.leapSecondsToApply t)
abbrev Offset.utcToTai (ω : Offset) (t : NaiveDateTime) := t + (ω.leapSecondsToRemove t)

/--
An `Offset` is lawful if the functions returning leap seconds to remove
and apply are isomorphic.
-/
class LawfulOffset (ω : Offset) where
  applyRemoveIso : ω.taiToUtc ∘ ω.utcToTai = id
  removeApplyIso : ω.utcToTai ∘ ω.taiToUtc = id

/--
The integer numberof TAI nanoseconds, relative to a zero of Janauary 1, year 1 in the Gregorian calendar.
If positive, the underlying number of TAI nanoseconds greater than the dawn of 1/1/1.
If negative, the number of TAI nanoseconds less than the dawn of 1/1/1.
-/
structure DateTime (ω : Offset) where
  naive : NaiveDateTime
deriving DecidableEq, Repr, Hashable, Lean.FromJson, Lean.ToJson


instance {ω : Offset} : Inhabited (DateTime ω) where
  default := ⟨Inhabited.default⟩

/--
This is a safe conversion since the underlying time is tracked
using a `NaiveDateTime` that represents a TAI date/time.
-/
def DateTime.changeOffset {ω : Offset} (t : DateTime ω) (π : Offset) : DateTime π := ⟨t.naive⟩

section DateTimeStuff

variable {ω π : Offset}


theorem DateTime.eq_of_val_eq : ∀ {d₁ d₂ : DateTime ω} (_ : d₁.naive = d₂.naive), d₁ = d₂
| ⟨_⟩, _, rfl => rfl

theorem DateTime.val_ne_of_ne : ∀ {d₁ d₂ : DateTime ω} (_ : d₁ ≠ d₂), d₁.naive ≠ d₂.naive
| ⟨x⟩, ⟨y⟩, h => by intro hh; apply h; exact congrArg DateTime.mk hh

/-- Compares the underlying naive/TAI DateTime -/
instance : LT (DateTime ω) where
  lt := InvImage (NaiveDateTime.instLT.lt) DateTime.naive

/-- Compares the underlying naive/TAI DateTime -/
instance : LE (DateTime ω) where
  le := InvImage (NaiveDateTime.instLE.le) DateTime.naive

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
  decidableLE := inferInstance

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

@[default_instance]
instance : HSub (DateTime ω) UnsignedDuration (DateTime ω) where
  hSub d dur := d - (dur : SignedDuration)

theorem DateTime.hSub_def_unsigned (d : DateTime ω) (dur : UnsignedDuration) : d - dur = d + -(dur : SignedDuration) := rfl

theorem DateTime.hAdd_signed_assoc (d : DateTime ω) (dur₁ dur₂ : SignedDuration) : d + dur₁ + dur₂ = d + (dur₁ + dur₂) := by
  simp [DateTime.hAdd_signed_def, NaiveDateTime.hAdd_signed_def]
  exact Int.add_assoc _ _ _

theorem DateTime.hAdd_signed_comm (d : DateTime ω) (dur : SignedDuration) : d + dur = dur + d := by
  simp [DateTime.hAdd_signed_def, NaiveDateTime.hAdd_signed_def, DateTime.hAdd_signed_def_rev, NaiveDateTime.hAdd_signed_def_rev]

/--
Incorporate the relevant leap seconds and the timezone offset, creating
a `NaiveDateTime` that carries the local number of nanos.
-/
def DateTime.toLocalNaive (t : DateTime ω) : NaiveDateTime :=
  /- The utc time; the naive time + leap seconds -/
  let utc := t.naive + (ω.leapSecondsToApply t.naive)
  utc + ω.timeZoneOffset

/--
Convert a `NaiveDateTime` representing a
-/
--def DateTime.fromTai (t : TaiDateTime) : DateTime ω := ⟨t⟩
-- vv This definition sort of makes more sense
def DateTime.fromTai (t : NaiveDateTime) : DateTime ω := ⟨t⟩
/--
Convert a `NaiveDateTime` that is local (has leap seconds and timezone offset applied)
and convert it to a `DateTime`.
-/
def DateTime.fromLocalNaive (t : NaiveDateTime) : DateTime ω :=
  /- Remove the timezone offset to get utc -/
  let utc := t - ω.timeZoneOffset
  /- Add whatever the corresponding `leapSecondsToRemove` value is -/
  ⟨utc + ω.leapSecondsToRemove utc⟩

/--
-/
def DateTime.fromLocalYmdsn
  (y : Year)
  (m : Month)
  (d : Nat)
  (s : Nat)
  (n : Nat)
  (hd : 1 <= d ∧ d <= m.numDays y := by decide) : DateTime ω :=
  DateTime.fromLocalNaive (NaiveDateTime.fromYmdsn y m d s n hd)

/--
Set the local clock time without changing the date.

For example
t : DateTime ω := LOCAL 2022/6/12 @ 11:00:00.0
t.setLocalClockTime (3:00:00.0)
= LOCAL 2022/6/12 @ 3:00:00.0
-/
def DateTime.setLocalClockTime (t : DateTime ω) (c : NaiveClockTime) : DateTime ω :=
  DateTime.fromLocalNaive (t.toLocalNaive.setClockTime c)

/--
Use cases for this are probably rare, so make sure you know what you're getting.

`compareLocalTimes` compares the literal calendar/wall clock datetimes from two time
stamps, without any regard for what underlying time they represent.
-/
def DateTime.compareLocal (t₁ : DateTime ω) (t₂ : DateTime π) : Ordering :=
  Ord.compare t₁.toLocalNaive t₂.toLocalNaive

def DateTime.localScalarDate (t : DateTime ω) : ScalarDate := t.toLocalNaive.toScalarDate
def DateTime.localYmd (t : DateTime ω) : Ymd := t.toLocalNaive.toYmd
def DateTime.localYear (t : DateTime ω) : Year := t.localScalarDate.year

end DateTimeStuff

@[reducible]
def Offset.tai : Offset := {
  name := "International Atomic Time"
  abbreviation := "TAI"
  offset := 0
  identifier := ""
  leapSecondsToApply := fun _ => 0
  leapSecondsToRemove := fun _ => 0
}

instance : LawfulOffset Offset.tai where
  applyRemoveIso := by
    apply funext; simp [Offset.leapSecondsToApply, Offset.leapSecondsToRemove, NaiveDateTime.hAdd_signed_def]
  removeApplyIso := by
    apply funext; simp [Offset.leapSecondsToApply, Offset.leapSecondsToRemove, NaiveDateTime.hAdd_signed_def]

/--
The `leapSmear` offset should NOT be used as a way of representing TAI time, or another
time metric that ignores leap seconds (for that, see )
While leap smearing ostensibly looks the same as TAI, there's a specific connotation
in the type, which is that the oracle/reference being used IS actually accounting for some
agreed-upon number of leap seconds and incorporating them into the time-stamps.

LeapSmear has a specific connotation, particularly in that it shouldn't display
"60" as a number of seconds.
-/
@[reducible]
def Offset.leapSmear (tz : TimeZone) : Offset := {
  name := ""
  abbreviation := ""
  offset := tz.offset
  -- This identifier should be changed to the user's preference; users will want to use this to identify the
  -- oracle that's being used for the smear values.
  identifier := ""
  leapSecondsToApply := fun _ => 0
  leapSecondsToRemove := fun _ => 0
}

instance {tz : TimeZone} : LawfulOffset (Offset.leapSmear tz) where
  applyRemoveIso := by
    apply funext; simp [Offset.leapSecondsToApply, Offset.leapSecondsToRemove, NaiveDateTime.hAdd_signed_def]
  removeApplyIso := by
    apply funext; simp [Offset.leapSecondsToApply, Offset.leapSecondsToRemove, NaiveDateTime.hAdd_signed_def]

/-
This definition of TAI time is convenient because it allows for comparison with other elements of `DateTime ω`,
and preserves type safety relative to `NaiveDateTime`, which carries no assertion that it represents
a TAI date/time element.
-/
@[reducible]
def TaiDateTime := DateTime Offset.tai
