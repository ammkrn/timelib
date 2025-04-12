import Timelib.DateTime.HENaive
import Timelib.Util
import Timelib.DateTime.TimeZone
import Timelib.DateTime.LeapTable

namespace Timelib

/--
H(eterogeneous)
E(extended)
DateTime

An Extended DateTime with all info bundled (precision, leap table, timezone)
-/
@[ext]
structure HEDateTime extends HENaiveDateTime where
  (L : List Row)
  (Z : TimeZone)
deriving DecidableEq

namespace HEDateTime

def toENaiveDateTime (d : HEDateTime) : ENaiveDateTime d.siPow := ⟨d.val, d.isLe⟩

instance : Repr HEDateTime where
  reprPrec x prec := reprPrec x.toENaiveDateTime prec

instance : ToString HEDateTime where
  toString x := toString x.val

instance instLE : LE HEDateTime where
  le l r := l.toHESignedDuration ≤ r.toHESignedDuration

instance instLT : LT HEDateTime where
  lt l r := l.toHESignedDuration < r.toHESignedDuration

instance  (d₁ d₂ : HEDateTime) :
  Decidable (d₁ <= d₂)
:= inferInstanceAs (Decidable <| d₁.toHESignedDuration <= d₂.toHESignedDuration)

instance  (d₁ d₂ : HEDateTime) :
  Decidable (d₁ < d₂)
:= inferInstanceAs (Decidable <| d₁.toHESignedDuration < d₂.toHESignedDuration)

end HEDateTime
