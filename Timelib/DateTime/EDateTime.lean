import Timelib.DateTime.NaiveDateTime
import Timelib.DateTime.DateTime
import Timelib.Duration.SignedDuration
import Timelib.Duration.ESignedDuration
import Timelib.Util
import Timelib.DateTime.TimeZone
import Timelib.DateTime.LeapSeconds

namespace Timelib

structure ENaiveDateTime (p : Int) extends ESignedDuration p
deriving DecidableEq, Repr

namespace ENaiveDateTime

end ENaiveDateTime
