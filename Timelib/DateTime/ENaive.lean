
import Timelib.Duration.ESignedDuration
import Timelib.DateTime.Naive

namespace Timelib

/--
`NaiveDateTime` extended with a notion of positive infinity.
-/
@[ext]
structure ENaiveDateTime (siPow : Int) extends ESignedDuration siPow where
  /--
  `siPow` remains an integer for compatability with the duration API,
  but we do not allow `siPow` to be less than zero; it cannot be a lower resolution
  than "seconds", because that would allow date-times with an ambiguous date.
  -/
  siPowLe : siPow <= 0
deriving DecidableEq, Repr

namespace ENaiveDateTime

variable {siPow : Int}

instance (_ : siPow ≤ 0) : Inhabited (ENaiveDateTime siPow) where
  default := ⟨0, ‹_›⟩

instance : Coe (NaiveDateTime siPow) (ENaiveDateTime siPow) where
  coe t := ⟨t.toSignedDuration, t.isLe⟩

theorem eq_of_val_eq : ∀ {d1 d2 : ENaiveDateTime siPow},
  d1.toESignedDuration = d2.toESignedDuration → d1 = d2
| ⟨_, _⟩, _, rfl => rfl

theorem val_eq_of_eq : ∀ {d1 d2 : ENaiveDateTime siPow},
  d1 = d2 → d1.toESignedDuration = d2.toESignedDuration
| ⟨_, _⟩, _, rfl => rfl

theorem eq_def : ∀ {d1 d2 : ENaiveDateTime siPow},
  d1 = d2 ↔ d1.toESignedDuration = d2.toESignedDuration
:= ⟨val_eq_of_eq, eq_of_val_eq⟩

theorem val_ne_of_ne : ∀ {d1 d2 : ENaiveDateTime siPow},
  d1 ≠ d2 → d1.toESignedDuration ≠ d2.toESignedDuration
| ⟨_, _⟩, ⟨_, _⟩, hne, h => hne (congrFun (congrArg mk h) _)

instance instLT : LT (ENaiveDateTime siPow) where
  lt := fun a b => a.toESignedDuration < b.toESignedDuration

instance instLE : LE (ENaiveDateTime siPow) where
  le := fun a b => a.toESignedDuration <= b.toESignedDuration

@[simp] theorem le_def (d₁ d₂ : ENaiveDateTime siPow) :
  (d₁ <= d₂) = (d₁.toESignedDuration <= d₂.toESignedDuration)
:= rfl

@[simp] theorem lt_def (d₁ d₂ : ENaiveDateTime siPow) :
  (d₁ < d₂) = (d₁.toESignedDuration < d₂.toESignedDuration)
:= rfl

instance instDecidableLENaiveDateTime (d₁ d₂ : ENaiveDateTime siPow) :
  Decidable (d₁ <= d₂)
:= inferInstanceAs (Decidable <| d₁.toESignedDuration <= d₂.toESignedDuration)

instance instDecidableLTNaiveDateTime (d₁ d₂ : ENaiveDateTime siPow) :
  Decidable (d₁ < d₂)
:= inferInstanceAs (Decidable <| d₁.toESignedDuration < d₂.toESignedDuration)

instance instOrd : Ord (ENaiveDateTime siPow) where
  compare l r := compare l.toESignedDuration r.toESignedDuration

theorem compare_def (l r : ENaiveDateTime siPow) :
  compare l r = compare l.toESignedDuration r.toESignedDuration := rfl

def convertLossless
  {fine coarse : Int}
  (d : ENaiveDateTime coarse)
  (h : fine <= coarse := by decide) :
  ENaiveDateTime fine :=
    ⟨d.toESignedDuration.convertLossless h, Int.le_trans h d.siPowLe⟩

def eConvertLossy
  {fine coarse : Int}
  (d : ENaiveDateTime fine)
  (siPowLe : coarse ≤ 0 := by decide)
  (h : fine <= coarse := by decide) : ENaiveDateTime coarse :=
    ⟨d.toESignedDuration.eConvertLossy h, siPowLe⟩

def fConvertLossy
  {fine coarse : Int}
  (d : ENaiveDateTime fine)
  (siPowLe : coarse ≤ 0 := by decide)
  (h : fine <= coarse := by decide) : ENaiveDateTime coarse :=
    ⟨d.toESignedDuration.fConvertLossy h, siPowLe⟩


end ENaiveDateTime
