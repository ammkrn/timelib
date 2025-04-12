import Timelib.DateTime.Naive
import Timelib.Util
import Timelib.DateTime.TimeZone
import Timelib.DateTime.LeapTable
import Timelib.DateTime.HNaive

namespace Timelib

@[ext]
structure HDateTime extends HNaiveDateTime where
  (L : List Row)
  (Z : TimeZone)
deriving DecidableEq--, Hashable


namespace HDateTime

namespace HDateTime

instance : Repr HDateTime where
  reprPrec x prec := reprPrec x.val prec

instance : ToString HDateTime where
  toString x := toString x.val

instance instLE : LE HDateTime where
  le := fun l r => l.toHSignedDuration ≤ r.toHSignedDuration

instance instLT : LT HDateTime where
  lt := fun l r => l.toHSignedDuration < r.toHSignedDuration

end HDateTime
