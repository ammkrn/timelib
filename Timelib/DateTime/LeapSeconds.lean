
import Timelib.Util
import Timelib.DateTime.NaiveDateTime
import Timelib.Duration.SignedDuration

namespace Timelib

structure LeapSeconds where
  ident : String
  apply {p : NegSiPow} (tai : NaiveDateTime p) : SignedDuration p
  remove {p : NegSiPow} (zulu : NaiveDateTime p) : SignedDuration p
