
import Timelib.Util
import Timelib.DateTime.NaiveDateTime
import Timelib.Duration.SignedDuration

namespace Timelib

structure TimeZone where
  ident {p : NegSiPow} (zulu : NaiveDateTime p) : String
  fromZulu {p : NegSiPow} (zulu : NaiveDateTime p) : SignedDuration p
  toZulu {p : NegSiPow} (local_ : NaiveDateTime p) : SignedDuration p

namespace TimeZone

class LawfulTimeZone (A : TimeZone) where
  applyIso {p : NegSiPow} (tai : NaiveDateTime p) : tai + (A.fromZulu (A.toZulu tai + tai)) = tai
  removeIso {p : NegSiPow} (x : NaiveDateTime p) : x + (A.toZulu (A.fromZulu x + x)) = x


def Zulu : TimeZone := {
  ident := fun _ => "zulu"
  fromZulu := fun _ => 0
  toZulu := fun _ => 0
}

instance : LawfulTimeZone Zulu := {
  applyIso := by simp [Zulu, NaiveDateTime.hAdd_signed_def]
  removeIso := by simp [Zulu, NaiveDateTime.hAdd_signed_def]
}
