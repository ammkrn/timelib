import Timelib.Duration.SignedDuration

namespace Timelib

/--
"Extended" signed duration; signed duration with a notion of
(positive) infinity.
-/
structure ESignedDuration (siPow : Int) where
  val : Option (SignedDuration siPow)
deriving DecidableEq, Hashable

namespace ESignedDuration

instance (siPow : Int): ToString (ESignedDuration siPow) where
  toString :=
    fun
    | ⟨none⟩ => "∞"
    | ⟨some d⟩ => toString d

instance (z : Int): Repr (ESignedDuration z) where
  reprPrec d _ := toString d

section
variable {z : Int}


instance : Coe (SignedDuration z) (ESignedDuration z) where
  coe d := ⟨d⟩

/-
Note that this is NOT how the Inhabited instance works for Mathlib's `WithTop`
-/
instance instInhabited : Inhabited (ESignedDuration z) where
  default := ⟨some Inhabited.default⟩

instance instZero : Zero (ESignedDuration z) where
  zero := ⟨some Zero.zero⟩

instance instLT : LT (ESignedDuration z) where
  lt := fun ⟨a⟩ ⟨b⟩ => Option.lt (SignedDuration.instLT.lt) a b

theorem lt_def (a b : ESignedDuration z) : (a < b) = Option.lt (SignedDuration.instLT.lt) a.val b.val := by
  simp [instLT]

instance (a b : ESignedDuration z) : Decidable (a < b) := by
  simp only [instLT]; exact inferInstance

instance : LE (ESignedDuration z) where
  le a b := a = b ∨ a < b

theorem le_def (a b : ESignedDuration z) : (a <= b) = (a = b ∨ a < b) := by
  simp [instLE]

instance (a b : ESignedDuration z) : Decidable (a <= b) := by
  simp only [instLE]; exact inferInstance

instance : Ord (ESignedDuration z) where
  compare a b := compareOfLessAndEq a b

def convertLossless
  {fine coarse : Int}
  (d : ESignedDuration coarse)
  (isLe : fine <= coarse := by decide) :
  ESignedDuration fine :=
  ⟨Option.map (·.convertLossless isLe) d.val⟩
def eConvertLossy
  {fine coarse : Int}
  (d : ESignedDuration fine)
  (_ : fine <= coarse := by decide) : ESignedDuration coarse :=
  --⟨d.val.map (fun x => x.eConvertLossy ‹_›)⟩
  ⟨d.val.map (fun x => x.eConvertLossy ‹_›)⟩
/--
Lossy conversion using the `f` rounding convention
-/
def fConvertLossy
  {fine coarse : Int}
  (d : ESignedDuration fine)
  (_ : fine <= coarse := by decide) : ESignedDuration coarse :=
  --⟨d.val.map (fun x => x.fConvertLossy ‹_›)⟩
  ⟨d.val.map (fun x => x.fConvertLossy ‹_›)⟩

def le_het {p1 p2 : Int} (d1 : ESignedDuration p1) (d2 : ESignedDuration p2) : Prop :=
  (d1.convertLossless (Int.min_le_left _ _) : ESignedDuration (min p1 p2))
  <= (d2.convertLossless (Int.min_le_right _ _) : ESignedDuration (min p1 p2))

def lt_het {p1 p2 : Int} (d1 : ESignedDuration p1) (d2 : ESignedDuration p2) : Prop :=
  (d1.convertLossless (Int.min_le_left _ _) : ESignedDuration (min p1 p2))
  < (d2.convertLossless (Int.min_le_right _ _) : ESignedDuration (min p1 p2))

instance instDecidableLEHet {p1 p2 : Int} (d1 : ESignedDuration p1) (d2 : ESignedDuration p2) :
  Decidable (le_het d1 d2)
:= inferInstanceAs <| Decidable <|
  (d1.convertLossless (Int.min_le_left _ _) : ESignedDuration (min p1 p2))
  <= (d2.convertLossless (Int.min_le_right _ _) : ESignedDuration (min p1 p2))

instance instDecidableLTHet {p1 p2 : Int} (d1 : ESignedDuration p1) (d2 : ESignedDuration p2) :
  Decidable (lt_het d1 d2)
:= inferInstanceAs <| Decidable <|
  (d1.convertLossless (Int.min_le_left _ _) : ESignedDuration (min p1 p2))
  < (d2.convertLossless (Int.min_le_right _ _) : ESignedDuration (min p1 p2))

--instance : Add (ESignedDuration z) where

/-
PITA that you have to redefine the way the order works.
-/
--def isNeg (d : ESignedDuration siPow) : Bool := d.val < 0
--
--def isNonNeg (d : ESignedDuration siPow) : Bool := ¬d.isNeg
--
--def abs (d : ESignedDuration siPow) : SignedDuration siPow := ⟨d.val.natAbs⟩

--instance : Add (ESignedDuration z) where

instance : Sub (ESignedDuration z) where
  sub a b := ⟨(· - ·) <$> a.val <*> b.val⟩

end
end ESignedDuration
