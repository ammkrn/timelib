import Timelib.Duration.SignedDuration

open Timelib

/--
Signed duration bundling the `siPow`; can handle durations
of different resolution.

** This should probably just be
siPow : Int, val: Int to save space.

Unfortunately there's not a great way to do reuse that way.
-/
structure HSignedDuration where
  siPow: Int
  val: SignedDuration siPow
deriving DecidableEq, Hashable

namespace HSignedDuration

instance : Repr HSignedDuration where
  reprPrec x prec := reprPrec x.val prec

instance : ToString HSignedDuration where
  toString x := toString x.val

instance (siPow : Int) : CoeOut (SignedDuration siPow) HSignedDuration where
  coe d := ⟨siPow, d⟩

/--
This is NOT how the Inhabited instance works for `WithTop`, I'm not sure
if that changes anything downstream, but this certainly seems more intuitive
to have it as zero instead of infinity.
-/
instance instInhabited : Inhabited HSignedDuration where
  default := ⟨0, Inhabited.default⟩

instance instZero : Zero HSignedDuration where
  zero := Inhabited.default

instance instLE : LE HSignedDuration where
  le := fun ⟨_, l⟩ ⟨_, r⟩ => l.le_het r

instance instLT : LT HSignedDuration where
  lt := fun ⟨_, l⟩ ⟨_, r⟩ => l.lt_het r

instance (d₁ d₂ : HSignedDuration) :
  Decidable (d₁ <= d₂)
:= inferInstanceAs (Decidable <| d₁.val.le_het d₂.val)

instance (d₁ d₂ : HSignedDuration) :
  Decidable (d₁ < d₂)
:= inferInstanceAs (Decidable <| d₁.val.lt_het d₂.val)



end HSignedDuration
