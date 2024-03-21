import Timelib.Util
import Timelib.Duration.SignedDuration
import Timelib.SignedInt
import Mathlib.Init.Order.Defs
import Mathlib.Data.List.Lex
import Mathlib.Init.Data.Int.CompLemmas
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Order.WithBot
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Order.Sub.WithTop
import Mathlib.Algebra.Order.Ring.WithTop

namespace Timelib

structure ESignedDuration (z : Int) where
  val : WithTop <| SignedDuration z
deriving DecidableEq, Repr

namespace ESignedDuration
section ESignedDuration_section
variable {z : Int}

instance : Monoid (SignedDuration z) := inferInstance

instance : Monoid (WithTop (SignedDuration z)) := inferInstance

def convertLossless
  {fine coarse : Int}
  (d : ESignedDuration coarse)
  (isLe : fine <= coarse := by decide) :
  ESignedDuration fine :=
  ⟨WithTop.map (·.convertLossless isLe) d.val⟩

instance : Add (ESignedDuration z) where
  add a b := ⟨a.val + b.val⟩

end ESignedDuration_section

end ESignedDuration
