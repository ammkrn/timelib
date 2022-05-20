import Timelib.Date.Year
import Timelib.Date.Month
import Timelib.Date.ScalarDate
import Timelib.Date.OrdinalDate
import Timelib.Date.Ymd
import Timelib.Date.Convert

def ScalarDate.firstOfTheMonth (year : Year) (m : Month) : ScalarDate :=
  Ymd.toScalarDate ⟨year, m, 1, le_refl _, Month.numDays_pos _ _⟩ 

def ScalarDate.lastOfTheMonth (year : Year) (m : Month) : ScalarDate :=
  Ymd.toScalarDate ⟨year, m, m.numDays year, Month.numDays_pos _ _, le_refl _⟩ 

def ScalarDate.newYear (year : Year) : ScalarDate := firstOfTheMonth 1 1

/--
The date of the first k-day (day of the week) on or before the passed date.
E.g. the first Monday on or before January 13, 2022 = January 10, 2022.
-/
def ScalarDate.kDayOnOrBefore (k : Nat) (h : k < 7 := by decide) : ScalarDate → ScalarDate 
| ⟨day⟩ => ⟨day - (day - k).rataDie⟩

def ScalarDate.kDayOnOrAfter (k : Nat) (d : ScalarDate) (h : k < 7 := by decide) : ScalarDate :=
  kDayOnOrBefore k h (d.addDays 6)

def ScalarDate.kDayNearest (k : Nat) (d : ScalarDate) (h : k < 7 := by decide) : ScalarDate :=
  kDayOnOrBefore k h (d.addDays 3)

def ScalarDate.kDayBefore (k : Nat) (d : ScalarDate) (h : k < 7 := by decide) : ScalarDate :=
  kDayOnOrBefore k h (d.subDays 1)

def ScalarDate.kDayAfter (k : Nat) (d : ScalarDate) (h : k < 7 := by decide) : ScalarDate :=
  kDayOnOrBefore k h (d.addDays 7)

/--
If n > 0, the date of the nth k-day on or after the date.
If n < 0, counts backwards, returning the nth k-day on or before the date.
-/
def ScalarDate.nthKDay (n : Int) (k : Nat) (d : ScalarDate) (hk : k < 7 := by decide) (hn : n ≠ 0 := by decide) : ScalarDate := 
  if n > 0  
  then ⟨7 * n + (d.kDayBefore k hk).day⟩
  else ⟨7 * n + (d.kDayAfter k hk).day⟩

/--
Returns the first k-day on or after the current date. To use this to find the
first k-day of the month, the date should be the first day of the month.
-/
def ScalarDate.firstKDay (k : Nat) (d : ScalarDate) (h : k < 7 := by decide) : ScalarDate :=
  d.nthKDay 1 k h

/--
Returns the last kday on or before the current date. To use this to find the 
last kday of a given month, the date should be the final day of that month.
-/
def ScalarDate.lastKDay (k : Nat) (d : ScalarDate) (h : k < 7 := by decide) : ScalarDate :=
  d.nthKDay (-1) k h

def Year.nthKDayOfMonth (y : Year) (n : Nat) (k : Nat) (m : Month) (hk : k < 7 := by decide) (hn : (Int.ofNat n) ≠ 0 := by decide) : ScalarDate :=
  (ScalarDate.firstOfTheMonth y m).nthKDay (.ofNat n) k hk hn

def Year.firstKDayOfMonth (y : Year) (k : Nat) (m : Month) (hk : k < 7 := by decide) : ScalarDate :=
  (ScalarDate.firstOfTheMonth y m).firstKDay k hk

def Year.lastKDayOfMonth (y : Year) (k : Nat) (m : Month) (hk : k < 7 := by decide) : ScalarDate :=
  (ScalarDate.lastOfTheMonth y m).lastKDay k hk