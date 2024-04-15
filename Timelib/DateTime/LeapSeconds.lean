import Timelib.Util
import Timelib.DateTime.NaiveDateTime
import Timelib.Duration.SignedDuration



namespace Timelib

/-
leap/unleap table condition:
Largest `n` from (n, offset)* such that `n` <= t
-/

structure LeapSeconds where
  ident : String
  apply {p : Int} (tai : NaiveDateTime p) : SignedDuration p
  remove {p : Int} (zulu : NaiveDateTime p) : SignedDuration p

namespace LeapSeconds

class LawfulLeapSeconds (A : LeapSeconds) where
  applyIso {p : Int} (x : NaiveDateTime p) : x + (A.remove (A.apply x + x)) = x
  removeIso {p : Int} (x : NaiveDateTime p) : x + (A.apply (A.remove x + x)) = x

def Tai : LeapSeconds := {
  ident := "tai"
  apply := fun _ => 0
  remove := fun _ => 0
}

instance : LawfulLeapSeconds Tai := {
  applyIso := by simp only [Tai, NaiveDateTime.hAdd_signed_def, add_zero, forall_const,
    Subtype.forall, implies_true]
  removeIso := by simp only [Tai, NaiveDateTime.hAdd_signed_def, add_zero, forall_const,
    Subtype.forall, implies_true]
}
