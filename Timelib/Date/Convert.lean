import Timelib.Date.Year
import Timelib.Date.Month
import Timelib.Date.Scalar
import Timelib.Date.Ordinal
import Timelib.Date.Ymd
import Timelib.Util

namespace Timelib

open Month

namespace ScalarDate

/-
Taken from 2.21 and 2.22 in the Gregorian Calendar chapter of Calendrical Calculations.
We can switch to using `/` and `%` instead of `fmod` and `fdiv` once we've uesd `fmod`
the first time, because `fmod` with a nonnegative modulus alwayd produces a positive remainder.
-/
def toOrdinalDate (d : ScalarDate) : OrdinalDate :=
  /- We substract one since the measure is 1-based. -/
  let dayPred := d.day - 1
  /- So days < 146097; the days in the 100 groups. -/
  let hundredGroupsDays := dayPred % 146097
  /- days < 36524; the days in the 4 groups -/
  let fourGroupDays := hundredGroupsDays % 36524
  /- days < 1461; the days in the singles -/
  let singlesGroupDays := fourGroupDays % 1461
  /- The number of 400 groups -/
  let num400YearGroups := dayPred / 146097
  /- The number of 100 groups -/
  let num100YearGroups := hundredGroupsDays / 36524
  /- The number of 4 groups -/
  let num4YearGroups := fourGroupDays / 1461
  /- Number of single years -/
  let numSingleYears := singlesGroupDays / 365
  /- Years from the 400 groups -/
  let yearsFrom400Groups := num400YearGroups * 400
  /- Years from the 100 groups -/
  let yearsFrom100Groups := num100YearGroups * 100
  /- Years from the 4 groups -/
  let yearsFrom4Groups := num4YearGroups * 4
  let isLastDayOfLeapYear := num100YearGroups = 4 ∨ numSingleYears = 4
  /- Add one iff it's not the last day of a leap year. If it is the last day of a leap year, withhold that additional year. -/
  let year := ⟨
    yearsFrom400Groups
    + yearsFrom100Groups
    + yearsFrom4Groups
    + numSingleYears
    + if isLastDayOfLeapYear then 0 else 1
  ⟩
  let day := if isLastDayOfLeapYear then 366 else ((singlesGroupDays % 365) + 1)
  have h_day_ge_one : 1 <= day.toNat := by omega
  have hle' : Int.toNat day ≤ Year.numDaysInGregorianYear year := by
    by_cases hleap : isLastDayOfLeapYear
    case pos =>
      have hIsLeap : year.isLeapYear := by
        simp only [Year.isLeapYear]
        have hx : year = {
        val :=
          yearsFrom400Groups + yearsFrom100Groups + yearsFrom4Groups + numSingleYears } := by
          have h01 : year = {
          val :=
            yearsFrom400Groups + yearsFrom100Groups + yearsFrom4Groups + numSingleYears + if isLastDayOfLeapYear then 0 else 1 } := rfl
          have h00 : (if isLastDayOfLeapYear then (0 : Int) else (1 : Int)) = 0 := by simp [hleap]
          simp [h00] at h01
          simp [h01]
        simp [hx]
        omega
      simp only [Year.numDaysInGregorianYear, hIsLeap, ↓reduceIte, Nat.reduceAdd, ge_iff_le]
      omega
    case neg => simp only [Year.numDaysInGregorianYear]; omega
  ⟨year, day.toNat, h_day_ge_one, hle'⟩

def toOrdinalDate_rassoc (d : ScalarDate) : OrdinalDate :=
  /- We substract one since the measure is 1-based. -/
  let dayPred := d.day - 1
  /- So days < 146097; the days in the 100 groups. -/
  let hundredGroupsDays := dayPred % 146097
  /- days < 36524; the days in the 4 groups -/
  let fourGroupDays := hundredGroupsDays % 36524
  /- days < 1461; the days in the singles -/
  let singlesGroupDays := fourGroupDays % 1461
  /- The number of 400 groups -/
  let num400YearGroups := dayPred / 146097
  /- The number of 100 groups -/
  let num100YearGroups := hundredGroupsDays / 36524
  /- The number of 4 groups -/
  let num4YearGroups := fourGroupDays / 1461
  /- Number of single years -/
  let numSingleYears := singlesGroupDays / 365
  /- Years from the 400 groups -/
  let yearsFrom400Groups := num400YearGroups * 400
  /- Years from the 100 groups -/
  let yearsFrom100Groups := num100YearGroups * 100
  /- Years from the 4 groups -/
  let yearsFrom4Groups := num4YearGroups * 4
  let isLastDayOfLeapYear := num100YearGroups = 4 ∨ numSingleYears = 4
  /- Add one iff it's not the last day of a leap year. If it is the last day of a leap year, withhold that additional year. -/
  let year := ⟨
    yearsFrom400Groups
    + (yearsFrom100Groups
    + (yearsFrom4Groups
    + (numSingleYears
    + if isLastDayOfLeapYear then 0 else 1)))
  ⟩
  let day := if isLastDayOfLeapYear then 366 else ((singlesGroupDays % 365) + 1)
  have h_day_ge_one : 1 ≤ day.toNat := by omega
  have hle' : Int.toNat day ≤ Year.numDaysInGregorianYear year := by
    by_cases hleap : isLastDayOfLeapYear
    case pos =>
      have hIsLeap : year.isLeapYear := by
        simp only [Year.isLeapYear]
        --simp [isLastDayOfLeapYear, num100YearGroups, numSingleYears] at hleap
        have hx : year = {
        val :=
          yearsFrom400Groups + yearsFrom100Groups + yearsFrom4Groups + numSingleYears } := by
          have h01 : year = {
           val :=
             yearsFrom400Groups +
               (yearsFrom100Groups + (yearsFrom4Groups + (numSingleYears + if isLastDayOfLeapYear then 0 else 1))) } := rfl
          have h00 : (if isLastDayOfLeapYear then (0 : Int) else (1 : Int)) = 0 := by simp [hleap]
          simp [h00] at h01
          simp [h01]
          omega
        simp [hx]

        omega
      simp only [Year.numDaysInGregorianYear, hIsLeap, ↓reduceIte, Nat.reduceAdd, ge_iff_le]
      omega
    case neg => simp only [Year.numDaysInGregorianYear]; omega
  ⟨year, day.toNat, h_day_ge_one, hle'⟩

theorem toOrdinalDate_rassoc_eq : toOrdinalDate = toOrdinalDate_rassoc := by
  apply funext
  simp only [toOrdinalDate, toOrdinalDate_rassoc, OrdinalDate.mk.injEq, Year.mk.injEq, and_true]
  omega


end ScalarDate

namespace OrdinalDate
/-
Derived from 2.17 in Calendrical Calculations.
-/
def toScalarDate : OrdinalDate → ScalarDate
| ⟨⟨year⟩, ordinalDay, _, _⟩ =>
  let yearPred := year - 1
  -- number of 400 groups
  let fourHundredGroups := yearPred / 400
  -- number of 100 groups; 0-3
  let oneHundredGroups := (yearPred % 400) / 100
  -- number of 4 groups; 0-24
  let fourGroups := (yearPred % 100) / 4
  -- number of single years; 0, 1, 2, or 3
  let singles := yearPred % 4
  let daysFrom400YearGroups := fourHundredGroups * 146097
  let daysFrom100YearGroups := oneHundredGroups * 36524
  let daysFrom4YearGroups := fourGroups * 1461
  let daysFrom1YearGroups := singles * 365
  ⟨daysFrom400YearGroups + daysFrom100YearGroups + daysFrom4YearGroups + daysFrom1YearGroups + ordinalDay⟩

def toScalarDate_rassoc : OrdinalDate → ScalarDate
| ⟨⟨year⟩, ordinalDay, _, _⟩ =>
  let yearPred := year - 1
  -- number of 400 groups
  let fourHundredGroups := yearPred / 400
  -- number of 100 groups; 0-3
  let oneHundredGroups := (yearPred % 400) / 100
  -- number of 4 groups; 0-24
  let fourGroups := (yearPred % 100) / 4
  -- number of single years; 0, 1, 2, or 3
  let singles := yearPred % 4
  let daysFrom400YearGroups := fourHundredGroups * 146097
  let daysFrom100YearGroups := oneHundredGroups * 36524
  let daysFrom4YearGroups := fourGroups * 1461
  let daysFrom1YearGroups := singles * 365
  ⟨daysFrom400YearGroups + (daysFrom100YearGroups + (daysFrom4YearGroups + (daysFrom1YearGroups + ordinalDay)))⟩

theorem toScalarDate_rassoc_eq : toScalarDate = toScalarDate_rassoc := by
  apply funext
  simp only [toScalarDate, toScalarDate_rassoc, ScalarDate.mk.injEq]
  omega

theorem convGeneric {d : OrdinalDate} {m : Month} : d.day ≤ (m.nextWrapping.lastDayOf d.year) →
  d.day - (m.lastDayOf d.year) <= (m.nextWrapping).numDays d.year := by
  cases m using Month.casesOn' <;> (by_cases h: d.year.isLeapYear <;> (simp [h, numDays, lastDayOf]; omega))

def toYmd (d : OrdinalDate) : Ymd :=
  if hJan: d.day <= january.lastDayOf d.year
    then ⟨d.year, january, d.day, d.hGe, by dsimp [numDays, lastDayOf] at *; assumption⟩
  else if _: d.day <= february.lastDayOf d.year
    then ⟨d.year, february, d.day - (january.lastDayOf d.year), by omega, convGeneric ‹_›⟩
  else if _: d.day <= march.lastDayOf d.year
    then ⟨d.year, march, d.day - (february.lastDayOf d.year), by omega, convGeneric ‹_›⟩
  else if _: d.day <= april.lastDayOf d.year
    then ⟨d.year, april, d.day - (march.lastDayOf d.year), by omega, convGeneric ‹_›⟩
  else if _: d.day <= may.lastDayOf d.year
    then ⟨d.year, may, d.day - (april.lastDayOf d.year), by omega, convGeneric ‹_›⟩
  else if _: d.day <= june.lastDayOf d.year
    then ⟨d.year, june, d.day - (may.lastDayOf d.year), by omega, convGeneric ‹_›⟩
  else if _: d.day <= july.lastDayOf d.year
    then ⟨d.year, july, d.day - (june.lastDayOf d.year), by omega, convGeneric ‹_›⟩
  else if _: d.day <= august.lastDayOf d.year
    then ⟨d.year, august, d.day - (july.lastDayOf d.year), by omega, convGeneric ‹_›⟩
  else if _: d.day <= september.lastDayOf d.year
    then ⟨d.year, september, d.day - (august.lastDayOf d.year), by omega, convGeneric ‹_›⟩
  else if _: d.day <= october.lastDayOf d.year
    then ⟨d.year, october, d.day - (september.lastDayOf d.year), by omega, convGeneric ‹_›⟩
  else if _: d.day <= november.lastDayOf d.year
    then ⟨d.year, november, d.day - (october.lastDayOf d.year), by omega, convGeneric ‹_›⟩
  else
    have h := last_december_eq d.year
    ⟨d.year, december, d.day - (november.lastDayOf d.year), by omega, convGeneric (h ▸ d.hLe)⟩

end OrdinalDate

namespace Ymd

theorem conv_generic (ymd : Ymd) (m : Month) : (_ : m ≠ december := by decide)
  → ymd.day + m.lastDayOf ymd.year <= ymd.year.numDaysInGregorianYear := by
  simp only [Year.numDaysInGregorianYear]
  have _ := ymd.month.numDays_le_31 ymd.year
  have _ := ymd.dayLe
  cases m using Month.casesOn'
  all_goals (first | simp [lastDayOf]; try omega | contradiction)

def toOrdinalDate (ymd : Ymd) : OrdinalDate :=
  have hDay : forall n, ymd.day + n >= 1 := have _ := ymd.dayGe; by omega
  match h:ymd.month with
  | january =>
    ⟨ymd.year, ymd.day, ymd.dayGe, Nat.le_trans ymd.dayLe (Nat.le_of_lt ymd.month_numDays_lt_gregorianYearNumDays)⟩
  | february  =>
    ⟨ymd.year, ymd.day + january.lastDayOf ymd.year, hDay _, conv_generic ymd _⟩
  | march  =>
    ⟨ymd.year, ymd.day + february.lastDayOf ymd.year, hDay _, conv_generic ymd _⟩
  | april  =>
    ⟨ymd.year, ymd.day + march.lastDayOf ymd.year, hDay _, conv_generic ymd _⟩
  | may =>
    ⟨ymd.year, ymd.day + april.lastDayOf ymd.year, hDay _, conv_generic ymd _⟩
  | june =>
    ⟨ymd.year, ymd.day + may.lastDayOf ymd.year, hDay _, conv_generic ymd _⟩
  | july  =>
    ⟨ymd.year, ymd.day + june.lastDayOf ymd.year, hDay _, conv_generic ymd _⟩
  | august  =>
    ⟨ymd.year, ymd.day + july.lastDayOf ymd.year, hDay _, conv_generic ymd _⟩
  | september  =>
    ⟨ymd.year, ymd.day + august.lastDayOf ymd.year, hDay _, conv_generic ymd _⟩
  | october =>
    ⟨ymd.year, ymd.day + september.lastDayOf ymd.year, hDay _, conv_generic ymd _⟩
  | november =>
    ⟨ymd.year, ymd.day + october.lastDayOf ymd.year, hDay _, conv_generic ymd _⟩
  | december =>
    ⟨ymd.year, ymd.day + november.lastDayOf ymd.year, hDay _, conv_generic ymd _⟩

def toScalarDate (ymd : Ymd) : ScalarDate := ymd.toOrdinalDate.toScalarDate

end Ymd

def ScalarDate.toYmd (d : ScalarDate) : Ymd := d.toOrdinalDate.toYmd

namespace OrdinalDate

abbrev ofArrayAux (lastDayFn : Month → Nat) (n : Nat) (d : Fin n) : (Month × Nat) :=
  if d.val <= (lastDayFn january)
    then (january, d.val)
  else if d.val <= (lastDayFn february)
    then (february, d.val - (lastDayFn january))
  else if d.val <= lastDayFn march
    then (march, d.val - (lastDayFn february))
  else if d.val <= lastDayFn april
    then (april, d.val - (lastDayFn march))
  else if d.val <= lastDayFn may
    then (may, d.val - (lastDayFn april))
  else if d.val <= lastDayFn june
    then (june, d.val - (lastDayFn may))
  else if d.val <= lastDayFn july
    then (july, d.val - (lastDayFn june))
  else if d.val <= lastDayFn august
    then (august, d.val - (lastDayFn july))
  else if d.val <= lastDayFn september
    then (september, d.val - (lastDayFn august))
  else if d.val <= lastDayFn october
    then (october, d.val - (lastDayFn september))
  else if d.val <= lastDayFn november
    then (november, d.val - (lastDayFn october))
  else
    (december, d.val - (lastDayFn november))

/-
These would be made effectively constants that are kept alive.
-/
abbrev ofArrayLeap := ofArrayAux lastDayOfLeap 367
abbrev ofArrayNonLeap := ofArrayAux lastDayOfNonLeap 366


--def ofArrayLeap (d : Fin 367) : (Month × Nat) :=
--  if d.val <= 31
--    then (january, d.val)
--  else if d.val <= february.lastDayOfLeap
--    then (february, d.val - (january.lastDayOfLeap))
--  else if d.val <= march.lastDayOfLeap
--    then (march, d.val - (february.lastDayOfLeap))
--  else if d.val <= april.lastDayOfLeap
--    then (april, d.val - (march.lastDayOfLeap))
--  else if d.val <= may.lastDayOfLeap
--    then (may, d.val - (april.lastDayOfLeap))
--  else if d.val <= june.lastDayOfLeap
--    then (june, d.val - (may.lastDayOfLeap))
--  else if d.val <= july.lastDayOfLeap
--    then (july, d.val - (june.lastDayOfLeap))
--  else if d.val <= august.lastDayOfLeap
--    then (august, d.val - (july.lastDayOfLeap))
--  else if d.val <= september.lastDayOfLeap
--    then (september, d.val - (august.lastDayOfLeap))
--  else if d.val <= october.lastDayOfLeap
--    then (october, d.val - (september.lastDayOfLeap))
--  else if d.val <= november.lastDayOfLeap
--    then (november, d.val - (october.lastDayOfLeap))
--  else
--    (december, d.val - (november.lastDayOfLeap))
--
--def ofArrayNonLeap (d : Fin 366) : (Month × Nat) :=
--  if d.val <= 31
--    then (january, d.val)
--  else if d.val <= february.lastDayOfNonLeap
--    then (february, d.val - (january.lastDayOfNonLeap))
--  else if d.val <= march.lastDayOfNonLeap
--    then (march, d.val - (february.lastDayOfNonLeap))
--  else if d.val <= april.lastDayOfNonLeap
--    then (april, d.val - (march.lastDayOfNonLeap))
--  else if d.val <= may.lastDayOfNonLeap
--    then (may, d.val - (april.lastDayOfNonLeap))
--  else if d.val <= june.lastDayOfNonLeap
--    then (june, d.val - (may.lastDayOfNonLeap))
--  else if d.val <= july.lastDayOfNonLeap
--    then (july, d.val - (june.lastDayOfNonLeap))
--  else if d.val <= august.lastDayOfNonLeap
--    then (august, d.val - (july.lastDayOfNonLeap))
--  else if d.val <= september.lastDayOfNonLeap
--    then (september, d.val - (august.lastDayOfNonLeap))
--  else if d.val <= october.lastDayOfNonLeap
--    then (october, d.val - (september.lastDayOfNonLeap))
--  else if d.val <= november.lastDayOfNonLeap
--    then (november, d.val - (october.lastDayOfNonLeap))
--  else
--    (december, d.val - (november.lastDayOfNonLeap))

--  def ofArray (od : OrdinalDate) : (Year × Month × Nat) :=
--    if od.year.isLeapYear
--    then
--      let ⟨m, da⟩ := ofArrayLeap od.day
--      (od.year, m, da)
--    else
--      let ⟨m, da⟩ := ofArrayNonLeap od.day
--      ⟨od.year, m, da⟩
--

end OrdinalDate
