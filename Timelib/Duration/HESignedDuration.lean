import Timelib.Duration.ESignedDuration

namespace Timelib

/--
Signed duration bundling the `siPow`; can handle durations
of different resolution.
-/
structure HESignedDuration where
  siPow: Int
  val: ESignedDuration siPow
deriving DecidableEq, Hashable

namespace HESignedDuration

instance : Repr HESignedDuration where
  reprPrec x prec := reprPrec x.val prec

instance (siPow : Int) : ToString (SignedDuration siPow) where
  toString x := toString x.val

instance (siPow : Int) : CoeOut (SignedDuration siPow) HESignedDuration where
  coe d := ⟨siPow, d⟩

instance instInhabited : Inhabited HESignedDuration where
  default := ⟨0, Inhabited.default⟩

instance instLE : LE HESignedDuration where
  le := fun ⟨_, l⟩ ⟨_, r⟩ => l.le_het r

instance instLT : LT HESignedDuration where
  lt := fun ⟨_, l⟩ ⟨_, r⟩ => l.lt_het r

instance (d₁ d₂ : HESignedDuration) :
  Decidable (d₁ <= d₂)
:= inferInstanceAs (Decidable <| d₁.val.le_het d₂.val)

instance (d₁ d₂ : HESignedDuration) :
  Decidable (d₁ < d₂)
:= inferInstanceAs (Decidable <| d₁.val.lt_het d₂.val)

end HESignedDuration
