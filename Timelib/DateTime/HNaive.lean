import Timelib.Duration.HSignedDuration
import Timelib.DateTime.Naive

namespace Timelib

/--
Signed duration bundling the `siPow`; can handle durations
of different resolution.
-/
structure HNaiveDateTime extends HSignedDuration where
  isLe : toHSignedDuration.siPow <= 0
deriving DecidableEq, Hashable, Repr

namespace HNaiveDateTime

def toNaiveDateTime (d : HNaiveDateTime) : NaiveDateTime d.siPow :=
    ⟨d.val, d.isLe⟩

def ofNaiveDateTime {siPow : Int} (d : NaiveDateTime siPow) : HNaiveDateTime :=
  ⟨⟨siPow, d.toSignedDuration⟩, d.isLe⟩

instance : Repr HNaiveDateTime where
  reprPrec x prec := reprPrec x.toNaiveDateTime prec

instance : ToString HNaiveDateTime where
  toString x := toString x.val

instance instLE : LE HNaiveDateTime where
  le l r := l.toHSignedDuration ≤ r.toHSignedDuration

instance instLT : LT HNaiveDateTime where
  lt l r := l.toHSignedDuration < r.toHSignedDuration

instance instDecidableLEHNaiveDateTime (d₁ d₂ : HNaiveDateTime) :
  Decidable (d₁ <= d₂)
:= inferInstanceAs (Decidable <| d₁.toHSignedDuration <= d₂.toHSignedDuration)

instance instDecidableLTNaiveDateTime (d₁ d₂ : HNaiveDateTime) :
  Decidable (d₁ < d₂)
:= inferInstanceAs (Decidable <| d₁.toHSignedDuration < d₂.toHSignedDuration)


end HNaiveDateTime
