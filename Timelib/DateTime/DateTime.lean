
import Timelib.DateTime.NaiveDateTime
import Timelib.Util
import Timelib.DateTime.TimeZone
import Timelib.DateTime.LeapSeconds

open Timelib

structure DateTime (precision : NegSiPow) (L : LeapSeconds) (Z : TimeZone)
  extends NaiveDateTime precision

instance (p : NegSiPow) {L : LeapSeconds} {Z : TimeZone} : Inhabited (DateTime p L Z) where
  default := ⟨Inhabited.default⟩

def DateTime.changeLeapSeconds
  {p : NegSiPow}
  {L : LeapSeconds}
  {Z : TimeZone}
  (d : DateTime p L Z)
  (L' : LeapSeconds) :
  DateTime p L' Z :=
  ⟨d.toNaiveDateTime⟩

def DateTime.changeTimeZone
  {p : NegSiPow}
  {L : LeapSeconds}
  {Z : TimeZone}
  (d : DateTime p L Z)
  (Z' : TimeZone):
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

def DateTime.simultaneous (d₁ d₂ : DateTime p L Z) : Prop :=
  d₁.toNaiveDateTime = d₂.toNaiveDateTime

def DateTime.convertLossless {p' : NegSiPow} (d : DateTime p L Z) (h : p' <= p := by decide) : DateTime p' L Z :=
  ⟨d.toNaiveDateTime.convertLossless h⟩

structure HDateTime where
  precision : NegSiPow
  leap : LeapSeconds
  zone : TimeZone
  val: DateTime precision leap zone

section HDateTime

variable (t : HDateTime) {dp : Int}


@[reducible]
def HDateTime.toNaiveLossless {p': NegSiPow} (d : HDateTime) (h : p' <= d.precision): NaiveDateTime p' :=
  d.val.toNaiveDateTime.convertLossless h

@[reducible]
def HDateTime.convertLossless {p': NegSiPow} (d : HDateTime) (h : p' <= d.precision) : { d' // (d' : HDateTime).precision = p' } :=
  let out := {
    precision := p'
    leap := d.leap
    zone := d.zone
    val := ⟨d.toNaiveLossless h⟩
  }
  ⟨out, by simp⟩

@[reducible]
def HDateTime.toNaiveLosslessMixed {p' : Int} (d : HDateTime) : NaiveDateTime (minLeft d.precision p') :=
  d.val.toNaiveDateTime.convertLossless (fine := minLeft d.precision p') (coarse := d.precision) (minLeft_le _ _)


@[reducible]
def HDateTime.simultaneous : HDateTime → HDateTime → Prop
| ⟨p₁, _, _, ⟨naive₁⟩⟩, ⟨p₂, _, _, ⟨naive₂⟩⟩ =>
  (naive₁.convertLossless (min_le_left p₁ p₂)) = (naive₂.convertLossless (min_le_right p₁ p₂))

/--
LT compares the underlying naive DateTime.
-/
instance : LT HDateTime where
  lt a b :=
    (a.toNaiveLossless (min_le_left a.precision b.precision))
    < (b.toNaiveLossless (min_le_right a.precision b.precision))

/--
LE compares the underlying naive DateTime
-/
instance : LE HDateTime where
  le a b :=
    (a.toNaiveLossless (min_le_left a.precision b.precision))
    <= (b.toNaiveLossless (min_le_right a.precision b.precision))


@[simp] theorem HDateTime.le_def (d₁ d₂ : HDateTime) :
  (d₁ <= d₂) = ((d₁.toNaiveLossless (min_le_left d₁.precision d₂.precision)) <= (d₂.toNaiveLossless (min_le_right d₁.precision d₂.precision))) := rfl

@[simp] theorem HDateTime.lt_def (d₁ d₂ : HDateTime) :
  (d₁ < d₂) =
  (d₁.toNaiveLossless (min_le_left d₁.precision d₂.precision)
  < (d₂.toNaiveLossless (min_le_right d₁.precision d₂.precision))) := rfl

instance instDecidableLTHDateTime (a b : HDateTime) : Decidable (a < b) :=
  inferInstanceAs <| Decidable <|
    a.toNaiveLossless (min_le_left a.precision b.precision) < b.toNaiveLossless (min_le_right a.precision b.precision)

instance instDecidableLEHDateTime (a b : HDateTime) : Decidable (a <= b) :=
  inferInstanceAs <| Decidable <|
    a.toNaiveLossless (min_le_left a.precision b.precision) <= b.toNaiveLossless (min_le_right a.precision b.precision)
