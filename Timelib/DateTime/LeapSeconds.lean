
import Timelib.Util
import Timelib.DateTime.NaiveDateTime
import Timelib.Duration.SignedDuration

namespace Timelib

structure LeapSeconds where
  ident : String
  apply {p : NegSiPow} (tai : NaiveDateTime p) : SignedDuration p
  remove {p : NegSiPow} (zulu : NaiveDateTime p) : SignedDuration p

namespace LeapSeconds

class LawfulLeapSeconds (A : LeapSeconds) where
  applyIso {p : NegSiPow} (x : NaiveDateTime p) : x + (A.remove (A.apply x + x)) = x
  removeIso {p : NegSiPow} (x : NaiveDateTime p) : x + (A.apply (A.remove x + x)) = x

def Tai : LeapSeconds := {
  ident := "tai"
  apply := fun _ => 0
  remove := fun _ => 0
}

instance : LawfulLeapSeconds Tai := {
  applyIso := by simp [Tai, NaiveDateTime.hAdd_signed_def]
  removeIso := by simp [Tai, NaiveDateTime.hAdd_signed_def]
}
