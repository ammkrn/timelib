
import Timelib.DateTime.NaiveDateTime
import Timelib.Util
import Timelib.DateTime.TimeZone
import Timelib.DateTime.LeapSeconds

namespace Timelib

structure DateTime (precision : Int) (L : LeapSeconds) (Z : TimeZone)
  extends NaiveDateTime precision

namespace DateTime

instance instDefault {p : Int} {isLe : p <= 0} {L : LeapSeconds} {Z : TimeZone} : Inhabited (DateTime p L Z) where
  default := ⟨Inhabited.default, isLe⟩

def changeLeapSeconds
  {p : Int}
  {L : LeapSeconds}
  {Z : TimeZone}
  (d : DateTime p L Z)
  (L' : LeapSeconds) :
  DateTime p L' Z :=
  ⟨d.toNaiveDateTime⟩

def changeTimeZone
  {p : Int}
  {L : LeapSeconds}
  {Z : TimeZone}
  (d : DateTime p L Z)
  (Z' : TimeZone):
  DateTime p L Z' :=
  ⟨d.toNaiveDateTime⟩

section DateTime_section

variable {p p2 p3 : Int} {L L' L2 L3 : LeapSeconds} {Z Z2 Z3 : TimeZone}

theorem eq_of_val_eq : ∀ {d₁ d₂ : DateTime p L Z} (_ : d₁.toNaiveDateTime = d₂.toNaiveDateTime), d₁ = d₂
| ⟨_⟩, _, rfl => rfl

theorem val_ne_of_ne : ∀ {d₁ d₂ : DateTime p L Z} (_ : d₁ ≠ d₂), d₁.toNaiveDateTime ≠ d₂.toNaiveDateTime
| ⟨x⟩, ⟨y⟩, h => by intro hh; apply h; exact congrArg DateTime.mk hh

instance : LT (DateTime p L Z) where
  lt := InvImage (NaiveDateTime.instLT.lt) DateTime.toNaiveDateTime

instance : LE (DateTime p L Z) where
  le := InvImage (NaiveDateTime.instLE.le) DateTime.toNaiveDateTime

@[simp] theorem le_def (d₁ d₂ : DateTime p L Z) : (d₁ <= d₂) = (d₁.toNaiveDateTime <= d₂.toNaiveDateTime) := rfl
@[simp] theorem lt_def (d₁ d₂ : DateTime p L Z) : (d₁ < d₂) = (d₁.toNaiveDateTime < d₂.toNaiveDateTime) := rfl

instance instDecidableLE (d₁ d₂ : DateTime p L Z) : Decidable (d₁ <= d₂) := inferInstanceAs (Decidable (d₁.toNaiveDateTime <= d₂.toNaiveDateTime))
instance instDecidableLT (d₁ d₂ : DateTime p L Z) : Decidable (d₁ < d₂) := inferInstanceAs (Decidable <| d₁.toNaiveDateTime < d₂.toNaiveDateTime)

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

theorem hAdd_signed_def (d : DateTime p L Z) (dur : SignedDuration p) : d + dur = ⟨d.toNaiveDateTime + dur⟩ := rfl
theorem hAdd_signed_comm (d : DateTime p L Z) (dur : SignedDuration p) : dur + d = d + dur := by
  simp only [instHAddSignedDurationDateTime]

instance : HSub (DateTime p L Z) (SignedDuration p) (DateTime p L Z) where
  hSub d dur := d + -dur

theorem hSub_signed_def (d : DateTime p L Z) (dur : (SignedDuration p)) : d - dur = d + -dur := rfl

theorem hAdd_signed_assoc (d : DateTime p L Z) (dur₁ dur₂ : (SignedDuration p)) : d + dur₁ + dur₂ = d + (dur₁ + dur₂) := by
  simp only [hAdd_signed_def, NaiveDateTime.hAdd_signed_def, mk.injEq, NaiveDateTime.mk.injEq]
  exact add_assoc d.toSignedDuration dur₁ dur₂


def simultaneous (d₁ d₂ : DateTime p L Z) : Prop :=
  d₁.toNaiveDateTime = d₂.toNaiveDateTime

def hetLe {p1 p2 : Int} (d1 : DateTime p1 L Z) (d2 : DateTime p2 L2 Z2) : Prop :=
  d1.toNaiveDateTime.le_het d2.toNaiveDateTime

def simultaneous_het (d₁ : DateTime p L Z)  (d₂ : DateTime p2 L2 Z2) : Prop :=
  d₁.hetLe d₂ ∧ d₂.hetLe d₁

def convertLossless {p' : Int} (d : DateTime p L Z) (h : p' <= p := by decide) : DateTime p' L Z :=
  ⟨d.toNaiveDateTime.convertLossless h⟩

theorem hetLe_iff {p : Int} (d1 : DateTime p L Z) (d2 : DateTime p L2 Z2) : hetLe d1 d2 ↔ d1.toNaiveDateTime <= d2.toNaiveDateTime :=
  NaiveDateTime.le_het_iff d1.toNaiveDateTime d2.toNaiveDateTime

def hetLt {p1 p2 : Int} (d1 : DateTime p1 L Z) (d2 : DateTime p2 L2 Z2) : Prop :=
  d1.toNaiveDateTime.lt_het d2.toNaiveDateTime

theorem hetLt_iff {p : Int} (d1 d2 : DateTime p L Z) : hetLt d1 d2 ↔ d1.toNaiveDateTime < d2.toNaiveDateTime :=
  NaiveDateTime.lt_het_iff d1.toNaiveDateTime d2.toNaiveDateTime

instance instDecidableLEHet {p1 p2 : Int} (d1 : DateTime p1 L Z) (d2 : DateTime p2 L2 Z2) :
  Decidable (hetLe d1 d2) := inferInstanceAs <| Decidable <| d1.toSignedDuration.le_het d2.toSignedDuration

instance instDecidableLTHet {p1 p2 : Int} (d1 : DateTime p1 L Z) (d2 : DateTime p2 L2 Z2) :
  Decidable (hetLt d1 d2)
:= inferInstanceAs <| Decidable <| d1.toSignedDuration.lt_het d2.toSignedDuration

theorem hetLe_trans {p1 p2 p3: Int} (d1 : DateTime p1 L Z) (d2 : DateTime p2 L2 Z2) (d3 : DateTime p3 L3 Z3)
  : hetLe d1 d2 → hetLe d2 d3 → hetLe d1 d3 :=
  NaiveDateTime.le_het_trans d1.toNaiveDateTime d2.toNaiveDateTime d3.toNaiveDateTime

theorem hetLt_iff_hetLe_not_hetLe {p1 p2 : Int} (d1 : DateTime p1 L Z) (d2 : DateTime p2 L2 Z2)
  : hetLt d1 d2 ↔ hetLe d1 d2 ∧ ¬(hetLe d2 d1) :=
  SignedDuration.lt_het_iff_le_het_not_le_het d1.toSignedDuration d2.toSignedDuration

def hetOccursBeforeStrict {p1 p2 : Int} (d1 : DateTime p1 L Z) (d2 : DateTime p2 L2 Z2) : Prop :=
  d1.hetLt d2

def hetWallClockLessThan {p1 p2 : Int} (d1 : DateTime p1 L Z) (d2 : DateTime p2 L2 Z2) : Prop :=
  d1.hetLt d2

end DateTime_section
end DateTime
