
import Timelib.DateTime.Naive
import Timelib.Util
import Timelib.DateTime.TimeZone
import Timelib.DateTime.LeapTable

namespace Timelib

/--
A local date time; precisely specifies the SI units, leap table used, and applicable time zone.
The actual value stored is TAI, and the L/Z parameters are used to recover the local time
as needed.
-/
@[ext]
structure DateTime (siPow : Int) (L : List Row) (Z : TimeZone)
  extends NaiveDateTime siPow
deriving DecidableEq

namespace DateTime

variable {siPow : Int} {L : List Row} {Z : TimeZone}

instance : Repr (DateTime siPow L Z) where
  reprPrec x prec := reprPrec x.val prec

instance instLE : LE (DateTime siPow L Z) where
  le := fun a b => a.toNaiveDateTime <= b.toNaiveDateTime

instance instLT : LT (DateTime siPow L Z) where
  lt := fun a b => a.toNaiveDateTime < b.toNaiveDateTime

instance (d₁ d₂ : DateTime siPow L Z) :
  Decidable (d₁ ≤ d₂)
:= inferInstanceAs (Decidable <| d₁.toNaiveDateTime ≤ d₂.toNaiveDateTime)

instance (d₁ d₂ : DateTime siPow L Z) :
  Decidable (d₁ < d₂)
:= inferInstanceAs (Decidable <| d₁.toNaiveDateTime < d₂.toNaiveDateTime)
