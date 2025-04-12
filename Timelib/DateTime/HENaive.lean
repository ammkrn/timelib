import Timelib.DateTime.ENaive
import Timelib.Duration.HESignedDuration

namespace Timelib

structure HENaiveDateTime extends HESignedDuration where
  isLe : toHESignedDuration.siPow <= 0
deriving DecidableEq, Hashable, Repr

namespace HENaiveDateTime

def toENaiveDateTime (d : HENaiveDateTime) : ENaiveDateTime d.siPow := ⟨d.val, d.isLe⟩

instance : Repr HENaiveDateTime where
  reprPrec x prec := reprPrec x.toENaiveDateTime prec

instance : ToString HENaiveDateTime where
  toString x := toString x.val

instance instLE : LE HENaiveDateTime where
  le l r := l.toHESignedDuration ≤ r.toHESignedDuration

instance instLT : LT HENaiveDateTime where
  lt l r := l.toHESignedDuration < r.toHESignedDuration

instance  (d₁ d₂ : HENaiveDateTime) :
  Decidable (d₁ <= d₂)
:= inferInstanceAs (Decidable <| d₁.toHESignedDuration <= d₂.toHESignedDuration)

instance  (d₁ d₂ : HENaiveDateTime) :
  Decidable (d₁ < d₂)
:= inferInstanceAs (Decidable <| d₁.toHESignedDuration < d₂.toHESignedDuration)
