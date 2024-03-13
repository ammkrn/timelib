
import Timelib.DateTime.NaiveDateTime
import Timelib.Util
import Timelib.DateTime.TimeZone
import Timelib.DateTime.LeapSeconds

open Timelib

structure DateTime (precision : NegSiPow) (L : LeapSeconds) (Z : TimeZone) extends NaiveDateTime precision

instance (p : NegSiPow) {L : LeapSeconds} {Z : TimeZone} : Inhabited (DateTime p L Z) where
  default := ⟨Inhabited.default⟩

def DateTime.changeLeapSeconds
  {p : NegSiPow}
  {L : LeapSeconds}
  {Z : TimeZone}
  (L' : LeapSeconds)
  (d : DateTime p L Z) :
  DateTime p L' Z :=
  ⟨d.toNaiveDateTime⟩

def DateTime.changeTimeZone
  {p : NegSiPow}
  {L : LeapSeconds}
  {Z : TimeZone}
  (Z' : TimeZone)
  (d : DateTime p L Z) :
  DateTime p L Z' :=
  ⟨d.toNaiveDateTime⟩

section DateTime

variable {p : NegSiPow} {L L' : LeapSeconds} {Z : TimeZone}


theorem DateTime.eq_of_val_eq : ∀ {d₁ d₂ : DateTime p L Z} (_ : d₁.toNaiveDateTime = d₂.toNaiveDateTime), d₁ = d₂
| ⟨_⟩, _, rfl => rfl

theorem DateTime.val_ne_of_ne : ∀ {d₁ d₂ : DateTime p L Z} (_ : d₁ ≠ d₂), d₁.toNaiveDateTime ≠ d₂.toNaiveDateTime
| ⟨x⟩, ⟨y⟩, h => by intro hh; apply h; exact congrArg DateTime.mk hh

instance : LT (DateTime p L Z) where
  lt := InvImage (NaiveDateTime.instLT.lt) DateTime.toNaiveDateTime

instance : LE (DateTime p L Z) where
  le := InvImage (NaiveDateTime.instLE.le) DateTime.toNaiveDateTime

@[simp] theorem DateTime.le_def (d₁ d₂ : DateTime p L Z) : (d₁ <= d₂) = (d₁.toNaiveDateTime <= d₂.toNaiveDateTime) := rfl
@[simp] theorem DateTime.lt_def (d₁ d₂ : DateTime p L Z) : (d₁ < d₂) = (d₁.toNaiveDateTime < d₂.toNaiveDateTime) := rfl

instance instDecidableLEDateTime (d₁ d₂ : DateTime p L Z) : Decidable (d₁ <= d₂) := inferInstanceAs (Decidable (d₁.toNaiveDateTime <= d₂.toNaiveDateTime))
instance instDecidableLTDateTime (d₁ d₂ : DateTime p L Z) : Decidable (d₁ < d₂) := inferInstanceAs (Decidable <| d₁.toNaiveDateTime < d₂.toNaiveDateTime)

instance : LinearOrder (DateTime p L Z) where
  le_refl (a) := le_refl a.toNaiveDateTime
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    rw [DateTime.le_def] at h1 h2
    exact DateTime.eq_of_val_eq (le_antisymm h1 h2)
  le_total := by simp [DateTime.le_def, le_total]
  decidableLE := inferInstance

instance : HAdd (DateTime p L Z) (SignedDuration p) (DateTime p L Z) where
  hAdd da du := ⟨da.toNaiveDateTime + du⟩

instance : HAdd (SignedDuration p) (DateTime p L Z) (DateTime p L Z)  where
  hAdd du da := da + du

theorem DateTime.hAdd_signed_def (d : DateTime p L Z) (dur : (SignedDuration p)) : d + dur = ⟨d.toNaiveDateTime + dur⟩ := rfl
theorem DateTime.hAdd_signed_def_rev (d : DateTime p L Z) (dur : (SignedDuration p)) : dur + d = ⟨dur + d.toNaiveDateTime⟩ := rfl

instance : HSub (DateTime p L Z) (SignedDuration p) (DateTime p L Z) where
  hSub d dur := d + -dur

theorem DateTime.hSub_signed_def (d : DateTime p L Z) (dur : (SignedDuration p)) : d - dur = d + -dur := rfl

theorem DateTime.hAdd_signed_assoc (d : DateTime p L Z) (dur₁ dur₂ : (SignedDuration p)) : d + dur₁ + dur₂ = d + (dur₁ + dur₂) := by
  simp [DateTime.hAdd_signed_def, NaiveDateTime.hAdd_signed_def]
  exact Int.add_assoc _ _ _

theorem DateTime.hAdd_signed_comm (d : DateTime p L Z) (dur : (SignedDuration p)) : d + dur = dur + d := by
  simp [DateTime.hAdd_signed_def, NaiveDateTime.hAdd_signed_def, DateTime.hAdd_signed_def_rev, NaiveDateTime.hAdd_signed_def_rev]

def DateTime.normalizePrecision {p' : NegSiPow} : DateTime p L Z → DateTime p' L Z → ((DateTime (min p p') L Z) × (DateTime (min p p') L Z))
  | d₁, d₂ =>
  let naive₁ := d₁.toNaiveDateTime.convertLossless' (min p p')
  let naive₂ := d₂.toNaiveDateTime.convertLossless' (min p p')
  sorry

structure HDateTime where
  precision : NegSiPow
  leap : LeapSeconds
  zone : TimeZone
  val: DateTime precision leap zone

section HDateTime

variable (t : HDateTime)

@[reducible]
def HDateTime.simultaneous : HDateTime → HDateTime → Prop
| ⟨p₁, _, _, ⟨naive₁⟩⟩, ⟨p₂, _, _, ⟨naive₂⟩⟩ =>
  if h : p₁.val <= p₂.val
  then
    naive₁ = (naive₂.convertLossless h)
  else
    (naive₁.convertLossless (Int.le_of_lt (Int.lt_of_not_ge h))) = naive₂

/-
/--
LT compares the underlying naive DateTime.
-/
instance : LT HDateTime where
  lt := InvImage NaiveDateTime.instLT.lt (siPow := ) (fun t => t.val.toNaiveDateTime)

/--
LE compares the underlying naive DateTime
-/
instance : LE HDateTime where
  le := InvImage NaiveDateTime.instLE.le (fun t => t.dateTime.naive)

@[simp] theorem HDateTime.le_def (d₁ d₂ : HDateTime) : (d₁ <= d₂) = (d₁.dateTime.naive <= d₂.dateTime.naive) := rfl
@[simp] theorem HDateTime.lt_def (d₁ d₂ : HDateTime) : (d₁ < d₂) = (d₁.dateTime.naive < d₂.dateTime.naive) := rfl

instance instDecidableLTHDateTime (a b : HDateTime) : Decidable (a < b) := inferInstanceAs (Decidable (a.dateTime.naive < b.dateTime.naive))
instance instDecidableLEHDateTime (a b : HDateTime) : Decidable (a <= b) := inferInstanceAs (Decidable (a.dateTime.naive <= b.dateTime.naive))

/--
HDateTime is only a Preorder since it does not respect antisymmetry.
t₁ <= t₂ ∧ t₂ <= t₁ does not imply t₁ = t₂ since they may have different offets/timezones.
-/
instance : Preorder HDateTime where
  le_refl a := le_refl a.dateTime.naive
  le_trans _a _b _c := Int.le_trans
  lt_iff_le_not_le _a _b := Int.lt_iff_le_not_le

instance : HAdd HDateTime SignedDuration HDateTime where
  hAdd da du := ⟨da.offset, da.dateTime + du⟩

instance : HAdd SignedDuration HDateTime HDateTime  where
  hAdd du da := da + du

theorem HDateTime.hAdd_def (d : HDateTime) (dur : SignedDuration) : d + dur = ⟨d.offset, d.dateTime  + dur⟩ := rfl

instance : HSub HDateTime SignedDuration HDateTime where
  hSub da du := ⟨da.offset, da.dateTime + -du⟩

theorem HDateTime.hSub_def (d : HDateTime) (dur : SignedDuration) : d - dur = ⟨d.offset, d.dateTime + -dur⟩ := rfl

instance : HAdd HDateTime UnsignedDuration HDateTime where
  hAdd da du := ⟨da.offset, da.dateTime + du⟩

instance : HAdd UnsignedDuration HDateTime HDateTime  where
  hAdd du da := da + du

theorem HDateTime.hAdd_def_unsigned (d : HDateTime) (dur : UnsignedDuration) : d + dur = ⟨d.offset, d.dateTime + dur⟩ := rfl

instance : HSub HDateTime UnsignedDuration HDateTime where
  hSub da du := ⟨da.offset, da.dateTime - du⟩

theorem HDateTime.hSub_def_unsigned (d : HDateTime) (dur : UnsignedDuration) : d - dur = ⟨d.offset, d.dateTime - dur⟩ := rfl
-/
