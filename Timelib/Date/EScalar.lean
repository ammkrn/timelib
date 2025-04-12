import Timelib.Util
import Timelib.Date.Scalar

namespace Timelib

def EScalarDate := WInfinity ScalarDate

namespace EScalarDate

@[reducible]
def dayOfWeek (d : EScalarDate) : Option Int :=
  d.map ScalarDate.dayOfWeek

abbrev isSunday (d : EScalarDate) : Option Bool := d.map ScalarDate.isSunday
abbrev isMonday (d : EScalarDate) : Option Bool :=    d.map ScalarDate.isMonday
abbrev isTuesday (d : EScalarDate) : Option Bool :=   d.map ScalarDate.isTuesday
abbrev isWednesday (d : EScalarDate) : Option Bool := d.map ScalarDate.isWednesday
abbrev isThursday (d : EScalarDate) : Option Bool :=  d.map ScalarDate.isThursday
abbrev isFriday (d : EScalarDate) : Option Bool :=    d.map ScalarDate.isFriday
abbrev isSaturday (d : EScalarDate) : Option Bool :=  d.map ScalarDate.isSaturday

def addDays : EScalarDate → Nat → EScalarDate
| d, ds => d.map (fun x => x.addDays ds)

def subDays : EScalarDate → Nat → EScalarDate
| d, ds => d.map (fun x => x.subDays ds)
