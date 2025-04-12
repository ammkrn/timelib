
import Timelib.DateTime.ENaive
import Timelib.DateTime.TimeZone
import Timelib.DateTime.LeapTable

namespace Timelib

/--
`NaiveDateTime` extended with a notion of positive infinity.
-/
@[ext]
structure EDateTime (siPow : Int) (L: List Row) (Z: TimeZone) extends ENaiveDateTime siPow where
  deriving DecidableEq, Repr

namespace EDateTime

variable {siPow : Int} {L: List Row} {Z: TimeZone}

instance instLT : LT (EDateTime siPow L Z) where
  lt := fun a b => a.toESignedDuration < b.toESignedDuration

instance instLE : LE (EDateTime siPow L Z) where
  le := fun a b => a.toESignedDuration <= b.toESignedDuration

@[simp] theorem le_def (d₁ d₂ : EDateTime siPow L Z) :
  (d₁ <= d₂) = (d₁.toESignedDuration <= d₂.toESignedDuration)
:= rfl

@[simp] theorem lt_def (d₁ d₂ : EDateTime siPow L Z) :
  (d₁ < d₂) = (d₁.toESignedDuration < d₂.toESignedDuration)
:= rfl

instance (d₁ d₂ : EDateTime siPow L Z) :
  Decidable (d₁ <= d₂)
:= inferInstanceAs (Decidable <| d₁.toESignedDuration <= d₂.toESignedDuration)

instance  (d₁ d₂ : EDateTime siPow L Z) :
  Decidable (d₁ < d₂)
:= inferInstanceAs (Decidable <| d₁.toESignedDuration < d₂.toESignedDuration)


end EDateTime
