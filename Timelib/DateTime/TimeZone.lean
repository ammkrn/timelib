
import Timelib.Util
import Timelib.DateTime.NaiveDateTime
import Timelib.Duration.SignedDuration

namespace Timelib

structure TimeZone where
  ident {p : NegSiPow} (zulu : NaiveDateTime p) : String
  fromZulu {p : NegSiPow} (zulu : NaiveDateTime p) : SignedDuration p
  toZulu {p : NegSiPow} (local_ : NaiveDateTime p) : SignedDuration p
