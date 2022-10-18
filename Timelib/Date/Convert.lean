import Lean.Data.Json
import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Equiv.Basic
import Mathlib.Init.Data.Int.Order
import Timelib.Date.Year
import Timelib.Date.Month
import Timelib.Date.ScalarDate
import Timelib.Date.OrdinalDate
import Timelib.Date.Ymd
import Timelib.Util

open Lean

theorem Year.lastDayFebruary_eq (y : Year) : y.lastDayFebruary = Month.february.numDays y + Year.lastDayJanuary := by 
  by_cases h: y.isLeapYear <;> simp [h,  Month.numDays]

theorem Year.lastDayMarch_eq (y : Year) : y.lastDayMarch = Month.march.numDays y + y.lastDayFebruary := by 
  simp [Month.numDays]; by_cases h: y.isLeapYear <;> simp [h]

theorem Year.lastDayApril_eq (y : Year) : y.lastDayApril = Month.april.numDays y + y.lastDayMarch := by 
  simp [Month.numDays]; by_cases h: y.isLeapYear <;> simp [h]

theorem Year.lastDayMay_eq (y : Year) : y.lastDayMay = Month.may.numDays y + y.lastDayApril := by 
  simp [Month.numDays]; by_cases h: y.isLeapYear <;> simp [h]

theorem Year.lastDayJune_eq (y : Year) : y.lastDayJune = Month.june.numDays y + y.lastDayMay := by 
  simp [Month.numDays]; by_cases h: y.isLeapYear <;> simp [h]

theorem Year.lastDayJuly_eq (y : Year) : y.lastDayJuly = Month.july.numDays y + y.lastDayJune := by 
  simp [Month.numDays]; by_cases h: y.isLeapYear <;> simp [h]

theorem Year.lastDayAugust_eq (y : Year) : y.lastDayAugust = Month.august.numDays y + y.lastDayJuly := by 
  simp [Month.numDays]; by_cases h: y.isLeapYear <;> simp [h]

theorem Year.lastDaySeptember_eq (y : Year) : y.lastDaySeptember = Month.september.numDays y + y.lastDayAugust := by 
  simp [Month.numDays]; by_cases h: y.isLeapYear <;> simp [h]

theorem Year.lastDayOctober_eq (y : Year) : y.lastDayOctober = Month.october.numDays y + y.lastDaySeptember := by 
  simp [Month.numDays]; by_cases h: y.isLeapYear <;> simp [h]

theorem Year.lastDayNovember_eq (y : Year) : y.lastDayNovember = Month.november.numDays y + y.lastDayOctober := by 
  simp [Month.numDays]; by_cases h: y.isLeapYear <;> simp [h]

theorem Year.lastDayDecember_eq (y : Year) : y.lastDayDecember = Month.december.numDays y + y.lastDayNovember := by 
  simp [Month.numDays]; by_cases h: y.isLeapYear <;> simp [h]

/- Predicates used to show that the conversion between (days <= 365) and (Month, day) pairs
   is a bijection. There isn't really a "nice" way of doing this, because
   months have irregular numbers of days, and the number of days depends on
   whether the current year is a leap year. Lean can't handle a function
   with 365 cases, so instead we chunk them into 12 groups by month -/
@[reducible] def OrdinalDate.isJanuaryDay   (d : OrdinalDate) : Prop := d.day <= Year.lastDayJanuary
@[reducible] def OrdinalDate.isFebruaryDay  (d : OrdinalDate) : Prop := Year.lastDayJanuary < d.day ∧ d.day <= d.year.lastDayFebruary
@[reducible] def OrdinalDate.isMarchDay     (d : OrdinalDate) : Prop := d.year.lastDayFebruary < d.day ∧ d.day <= d.year.lastDayMarch
@[reducible] def OrdinalDate.isAprilDay     (d : OrdinalDate) : Prop := d.year.lastDayMarch < d.day ∧ d.day <= d.year.lastDayApril
@[reducible] def OrdinalDate.isMayDay       (d : OrdinalDate) : Prop := d.year.lastDayApril < d.day ∧ d.day <= d.year.lastDayMay
@[reducible] def OrdinalDate.isJuneDay      (d : OrdinalDate) : Prop := d.year.lastDayMay < d.day ∧ d.day <= d.year.lastDayJune
@[reducible] def OrdinalDate.isJulyDay      (d : OrdinalDate) : Prop := d.year.lastDayJune < d.day ∧ d.day <= d.year.lastDayJuly
@[reducible] def OrdinalDate.isAugustDay    (d : OrdinalDate) : Prop := d.year.lastDayJuly < d.day ∧ d.day <= d.year.lastDayAugust
@[reducible] def OrdinalDate.isSeptemberDay (d : OrdinalDate) : Prop := d.year.lastDayAugust < d.day ∧ d.day <= d.year.lastDaySeptember
@[reducible] def OrdinalDate.isOctoberDay   (d : OrdinalDate) : Prop := d.year.lastDaySeptember < d.day ∧ d.day <= d.year.lastDayOctober
@[reducible] def OrdinalDate.isNovemberDay  (d : OrdinalDate) : Prop := d.year.lastDayOctober < d.day ∧ d.day <= d.year.lastDayNovember
@[reducible] def OrdinalDate.isDecemberDay  (d : OrdinalDate) : Prop := d.year.lastDayNovember < d.day

@[reducible] def OrdinalDate.toYmd (ordinal : OrdinalDate) : Ymd :=
  if hJan: ordinal.day <= Year.lastDayJanuary 
    then ⟨ordinal.year, Month.january, ordinal.day, ordinal.hGe, hJan⟩
  else if hFeb: ordinal.day <= ordinal.year.lastDayFebruary
    then ⟨ordinal.year, Month.february, ordinal.day - Year.lastDayJanuary, Nat.sub_pos_of_lt (Nat.gt_of_not_le hJan), Nat.sub_le_of_le_add (ordinal.year.lastDayFebruary_eq ▸ hFeb)⟩ 
  else if hMar: ordinal.day <= ordinal.year.lastDayMarch
    then ⟨ordinal.year, Month.march, ordinal.day - ordinal.year.lastDayFebruary, Nat.sub_pos_of_lt (Nat.gt_of_not_le hFeb), Nat.sub_le_of_le_add (ordinal.year.lastDayMarch_eq ▸ hMar)⟩
  else if hApr: ordinal.day <= ordinal.year.lastDayApril 
    then ⟨ordinal.year, Month.april, ordinal.day - ordinal.year.lastDayMarch, Nat.sub_pos_of_lt (Nat.gt_of_not_le hMar), Nat.sub_le_of_le_add (ordinal.year.lastDayApril_eq ▸ hApr)⟩
  else if hMay: ordinal.day <= ordinal.year.lastDayMay
    then ⟨ordinal.year, Month.may, ordinal.day - ordinal.year.lastDayApril, Nat.sub_pos_of_lt (Nat.gt_of_not_le hApr), Nat.sub_le_of_le_add (ordinal.year.lastDayMay_eq ▸ hMay)⟩
  else if hJun: ordinal.day <= ordinal.year.lastDayJune
    then ⟨ordinal.year, Month.june, ordinal.day - ordinal.year.lastDayMay, Nat.sub_pos_of_lt (Nat.gt_of_not_le hMay), Nat.sub_le_of_le_add (ordinal.year.lastDayJune_eq ▸ hJun)⟩
  else if hJul: ordinal.day <= ordinal.year.lastDayJuly
    then ⟨ordinal.year, Month.july, ordinal.day - ordinal.year.lastDayJune, Nat.sub_pos_of_lt (Nat.gt_of_not_le hJun), Nat.sub_le_of_le_add (ordinal.year.lastDayJuly_eq ▸ hJul)⟩
  else if hAug: ordinal.day <= ordinal.year.lastDayAugust
    then ⟨ordinal.year, Month.august, ordinal.day - ordinal.year.lastDayJuly, Nat.sub_pos_of_lt (Nat.gt_of_not_le hJul), Nat.sub_le_of_le_add (ordinal.year.lastDayAugust_eq ▸ hAug)⟩
  else if hSep: ordinal.day <= ordinal.year.lastDaySeptember
    then ⟨ordinal.year, Month.september, ordinal.day - ordinal.year.lastDayAugust, Nat.sub_pos_of_lt (Nat.gt_of_not_le hAug), Nat.sub_le_of_le_add (ordinal.year.lastDaySeptember_eq ▸ hSep)⟩
  else if hOct: ordinal.day <= ordinal.year.lastDayOctober
    then ⟨ordinal.year, Month.october, ordinal.day - ordinal.year.lastDaySeptember, Nat.sub_pos_of_lt (Nat.gt_of_not_le hSep), Nat.sub_le_of_le_add (ordinal.year.lastDayOctober_eq ▸ hOct)⟩
  else if hNov: ordinal.day <= ordinal.year.lastDayNovember
    then ⟨ordinal.year, Month.november, ordinal.day - ordinal.year.lastDayOctober, Nat.sub_pos_of_lt (Nat.gt_of_not_le hOct), Nat.sub_le_of_le_add (ordinal.year.lastDayNovember_eq ▸ hNov)⟩
  else 
    have hr : ordinal.day - Year.lastDayNovember ordinal.year ≤ Month.numDays ordinal.year 12 := by
      apply Nat.sub_le_of_le_add
      have hLe := ordinal.hLe
      simp [Year.numDaysInGregorianYear] at hLe
      simp [Month.numDays]
      refine le_trans hLe ?hLe2
      by_cases hh: ordinal.year.isLeapYear <;> simp [hh]
    ⟨ordinal.year, Month.december, ordinal.day - ordinal.year.lastDayNovember, Nat.sub_pos_of_lt (Nat.gt_of_not_le hNov), hr⟩ 

def Ymd.toOrdinalDate (ymd : Ymd) : OrdinalDate := 
  match ymd.month with
  | Month.january => 
    have hLe : ymd.day ≤ Year.numDaysInGregorianYear ymd.year := by
      by_cases hLeap : ymd.year.isLeapYear <;> simp_arith [hLeap, Year.numDaysInGregorianYear]
      case pos => exact Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 366 by decide))
      case neg => exact Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 365 by decide))
    ⟨ymd.year, ymd.day, ymd.dayGe, hLe⟩
  | Month.february  => 
    have hLe : ymd.day + Year.lastDayJanuary ≤ ymd.year.numDaysInGregorianYear := by
      by_cases hLeap : ymd.year.isLeapYear <;> simp_arith [hLeap, Year.numDaysInGregorianYear]
      case pos => exact Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 335 by decide))
      case neg => exact Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 334 by decide))
    ⟨ymd.year, ymd.day + Year.lastDayJanuary, Nat.le_trans ymd.dayGe (Nat.le_add_right _ _), hLe⟩ 
  | Month.march  => 
    have hLe : ymd.day + ymd.year.lastDayFebruary ≤ ymd.year.numDaysInGregorianYear := by
      by_cases hLeap : ymd.year.isLeapYear <;> simp_arith [Year.numDaysInGregorianYear, hLeap, Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 306 by decide))]
    ⟨ymd.year, ymd.day + ymd.year.lastDayFebruary, Nat.le_trans ymd.dayGe (Nat.le_add_right _ _), hLe⟩ 
  | Month.april  => 
    have hLe : ymd.day + ymd.year.lastDayMarch ≤ ymd.year.numDaysInGregorianYear := by
      by_cases hLeap : ymd.year.isLeapYear <;> simp_arith [Year.numDaysInGregorianYear, hLeap, Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 275 by decide))]
    ⟨ymd.year, ymd.day + ymd.year.lastDayMarch, Nat.le_trans ymd.dayGe (Nat.le_add_right _ _), hLe⟩ 
  | Month.may => 
    have hLe : ymd.day + ymd.year.lastDayApril ≤ ymd.year.numDaysInGregorianYear := by
      by_cases hLeap : ymd.year.isLeapYear <;> simp_arith [Year.numDaysInGregorianYear, hLeap, Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 245 by decide))]
    ⟨ymd.year, ymd.day + ymd.year.lastDayApril, Nat.le_trans ymd.dayGe (Nat.le_add_right _ _), hLe⟩  
  | Month.june => 
    have hLe : ymd.day + ymd.year.lastDayMay ≤ ymd.year.numDaysInGregorianYear := by
      by_cases hLeap : ymd.year.isLeapYear <;> simp_arith [Year.numDaysInGregorianYear, hLeap, Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 214 by decide))]
    ⟨ymd.year, ymd.day + ymd.year.lastDayMay, Nat.le_trans ymd.dayGe (Nat.le_add_right _ _), hLe⟩  
  | Month.july  => 
    have hLe : ymd.day + ymd.year.lastDayJune ≤ ymd.year.numDaysInGregorianYear := by
      by_cases hLeap : ymd.year.isLeapYear <;> simp_arith [Year.numDaysInGregorianYear, hLeap, Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 184 by decide))]
    ⟨ymd.year, ymd.day + ymd.year.lastDayJune, Nat.le_trans ymd.dayGe (Nat.le_add_right _ _), hLe⟩  
  | Month.august  => 
    have hLe : ymd.day + ymd.year.lastDayJuly ≤ ymd.year.numDaysInGregorianYear := by
      by_cases hLeap : ymd.year.isLeapYear <;> simp_arith [Year.numDaysInGregorianYear, hLeap, Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 153 by decide))]
    ⟨ymd.year, ymd.day + ymd.year.lastDayJuly, Nat.le_trans ymd.dayGe (Nat.le_add_right _ _), hLe⟩  
  | Month.september  => 
    have hLe : ymd.day + ymd.year.lastDayAugust ≤ ymd.year.numDaysInGregorianYear := by
      by_cases hLeap : ymd.year.isLeapYear <;> simp_arith [Year.numDaysInGregorianYear, hLeap, Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 122 by decide))]
    ⟨ymd.year, ymd.day + ymd.year.lastDayAugust, Nat.le_trans ymd.dayGe (Nat.le_add_right _ _), hLe⟩  
  | Month.october => 
    have hLe : ymd.day + ymd.year.lastDaySeptember ≤ ymd.year.numDaysInGregorianYear := by
      by_cases hLeap : ymd.year.isLeapYear <;> simp_arith [Year.numDaysInGregorianYear, hLeap, Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 92 by decide))]
    ⟨ymd.year, ymd.day + ymd.year.lastDaySeptember, Nat.le_trans ymd.dayGe (Nat.le_add_right _ _), hLe⟩  
  | Month.november => 
    have hLe : ymd.day + ymd.year.lastDayOctober ≤ ymd.year.numDaysInGregorianYear := by
      by_cases hLeap : ymd.year.isLeapYear <;> simp_arith [Year.numDaysInGregorianYear, hLeap, Nat.le_trans (ymd.dayLe) (Nat.le_trans (ymd.month.numDays_lt_31 ymd.year) (show 31 <= 61 by decide))]
    ⟨ymd.year, ymd.day + ymd.year.lastDayOctober, Nat.le_trans ymd.dayGe (Nat.le_add_right _ _), hLe⟩  
  | Month.december => 
    have hLe : ymd.day + ymd.year.lastDayNovember ≤ ymd.year.numDaysInGregorianYear := by
    by_cases hLeap : ymd.year.isLeapYear <;> simp_arith [hLeap, Year.numDaysInGregorianYear, Month.numDays_lt_31, Nat.le_trans ymd.dayLe (ymd.month.numDays_lt_31 ymd.year)]
    ⟨ymd.year, ymd.day + ymd.year.lastDayNovember, Nat.le_trans ymd.dayGe (Nat.le_add_right _ _), hLe⟩

@[simp] theorem Ymd.toOrdinalDate_year_same (ymd : Ymd) : (ymd.toOrdinalDate).year = ymd.year := by 
  simp [Ymd.toOrdinalDate]; cases ymd.month <;> simp


def ScalarDate.toOrdinalDateYearIsLastDayOfLeapYear (d : ScalarDate) : Prop := 
  let dayPred := d.day - 1
  let hundredGroupsDays := dayPred.fmod 146097
  let fourGroupDays := hundredGroupsDays % 36524
  let singlesGroupDays := fourGroupDays % 1461
  let num100YearGroups := hundredGroupsDays / 36524
  let numSingleYears : Int := singlesGroupDays / 365
  num100YearGroups = 4 ∨ numSingleYears = 4

def ScalarDate.toOrdinalDateYear (d : ScalarDate) : Year := 
  /- We substract one since the measure is 1-based. -/
  let dayPred := d.day - 1
  /- So days < 146097; the days in the 100 groups. -/
  let hundredGroupsDays := dayPred.fmod 146097
  /- days < 36524; the days in the 4 groups -/
  let fourGroupDays := hundredGroupsDays % 36524
  /- days < 1461; the days in the singles -/
  let singlesGroupDays := fourGroupDays % 1461
  /- The number of 400 groups -/
  let num400YearGroups := dayPred.fdiv 146097
  /- The number of 100 groups -/
  let num100YearGroups := hundredGroupsDays / 36524
  /- The number of 4 groups -/
  let num4YearGroups := fourGroupDays / 1461
  /- Number of single years -/
  let numSingleYears : Int := singlesGroupDays / 365
  /- Years from the 400 groups -/
  let yearsFrom400Groups := num400YearGroups * 400
  /- Years from the 100 groups -/
  let yearsFrom100Groups := num100YearGroups * 100
  /- Years from the 4 groups -/
  let yearsFrom4Groups := num4YearGroups * 4
  let isLastDayOfLeapYear := num100YearGroups = 4 ∨ numSingleYears = 4
  Year.mk (yearsFrom400Groups + yearsFrom100Groups + yearsFrom4Groups + numSingleYears + (if isLastDayOfLeapYear then 0 else 1))


theorem ScalarDate.toOrdinalDateYear_leap (d : ScalarDate) : 
  d.toOrdinalDateYearIsLastDayOfLeapYear → d.toOrdinalDateYear.isLeapYear := by 
  simp only [ScalarDate.toOrdinalDateYearIsLastDayOfLeapYear, Year.isLeapYear, ScalarDate.toOrdinalDateYear]
  refine Or.rec ?l ?r
  case l =>
    intro h
    have h_eq : (Int.fmod (d.day - 1) 146097) = 146096 := by
      have hle_left : 146096 ≤ Int.fmod (d.day - 1) 146097 := 
         @Int.mul_le_of_le_div 4 (b := Int.fmod (d.day - 1) 146097) 36524 pos36524 (le_of_eq h.symm)
      exact le_antisymm (Int.le_of_add_le_add_right (Int.fmod_lt _ pos146097)) hle_left
    apply Or.inr
    simp [h_eq, h4, h1, h100, hdiv']
  case r =>
    intro h
    have h_eq : (((Int.fmod (d.day - 1) 146097) % 36524) % 1461) = 1460 := by
      have hle_left : 1460 ≤ (((Int.fmod (d.day - 1) 146097) % 36524) % 1461) :=
        @Int.mul_le_of_le_div 4 ((((Int.fmod (d.day - 1) 146097) % 36524) % 1461)) 365 (pos365) (le_of_eq h.symm) 
      refine le_antisymm (Int.le_of_add_le_add_right (Int.mod_lt_of_pos _ pos1461)) hle_left
    apply Or.inl
    simp [h_eq, h100, h4, h1, hdiv, hdiv']
    refine And.intro ?ll ?rr
    case ll =>
      have hleft : (Int.fdiv (d.day - 1) 146097) * 400 = ((Int.fdiv (d.day - 1) 146097) * 100) * 4 := by
        rw [mul_assoc _ 100 4]; simp [show (100 : Int) * 4 = 400 by decide]
      have hright : ((Int.fmod (d.day - 1) 146097) / 36524) * 100 = (((Int.fmod (d.day - 1) 146097) / 36524) * 25) * 4 := by
        rw [mul_assoc _ 25 4]; simp [show (25 : Int) * 4 = 100 by decide]
      simp [hleft, hright, (Int.distrib_right _ _ _).symm]
    case rr =>
      have hleft : (Int.fdiv (d.day - 1) 146097) * 400 = ((Int.fdiv (d.day - 1) 146097) * 4) * 100 := by
        rw [mul_assoc _ 4 100]; simp [show (4 : Int) * 100 = 400 by decide]
      simp [hleft, (Int.distrib_right _ _ _).symm]
      rw [add_assoc]
      rw [add_comm (((Int.fdiv (d.day - 1) 146097 * 4) + (Int.fmod (d.day - 1) 146097 / 36524)) * 100) _]
      simp
      intro hf
      have hdiv_nonneg : 0 ≤ (Int.fmod (d.day - 1) 146097) % 36524 / 1461 := 
        Int.div_nonneg (Int.mod_nonneg _ (by decide)) (le_of_lt pos1461)
      have hlt_100 : ((Int.fmod (d.day - 1) 146097) % 36524) / 1461 * 4 + 4 < 100 := by
        apply Int.add_lt_of_lt_sub_right
        rw [(show (100 : Int) - 4 = 96 by decide)]
        apply Int.mul_lt_of_lt_div pos4
        rw [(show (96 : Int) / 4 = 24 by decide)]
        apply Int.div_lt_of_lt_mul pos1461
        rw [(show (24 : Int) * 1461 = 35064 by decide)]
        apply lt_of_not_ge
        intro hf
        cases lt_or_eq_of_le hf with
        | inl hl =>
          have lt_upper : (Int.fmod (d.day - 1) 146097) % 36524 < 36524 := Int.mod_lt_of_pos _ pos36524
          have h_fac_24 :  (1461 : Int) * 24 = 35064 := by decide
          rw [<- h_fac_24] at hl hf 
          have h_lt25 : ((Int.fmod (d.day - 1) 146097) % 36524) < (1461 : Int) * 25 := by
            have h_fac_25 : (1461 : Int) * 25 = 36525 := by decide
            rw [h_fac_25]; exact lt_trans lt_upper (by decide)
          have h_hard : ((Int.fmod (d.day - 1) 146097) % 36524) / 1461 = 24 := by
            exact Int.div_pigeonhole (Int.mod_nonneg _ (by decide)) (by decide) (by decide) hl h_lt25 
          have h_from := ((@Int.div_mod_unique ((Int.fmod (d.day - 1) 146097) % 36524) 1461 1460 24 (show (0 : Int) < 1461 by decide)).mp (And.intro h_hard h_eq)).left
          rw [<- h_from] at lt_upper
          simp at lt_upper
          done
        | inr hr =>
          rw [<- hr] at h_eq
          have hne : Int.fmod 35064 1461 ≠ 1460 := by decide 
          exact False.elim (hne h_eq)
      have hmul4 : 0 <=(Int.fmod (d.day - 1) 146097) % 36524 / 1461 * 4 :=
        Int.mul_nonneg hdiv_nonneg (le_of_lt pos4)
      have hout : 
        ((Int.fmod (d.day - 1) 146097) % 36524 / 1461 * 4 + 4) % 100 =
        (Int.fmod (d.day - 1) 146097) % 36524 / 1461 * 4 + 4 := by
        refine Int.mod_eq_of_lt ?x hlt_100
        exact Int.add_right_nonneg (Int.mul_nonneg hdiv_nonneg (le_of_lt pos4)) (le_of_lt pos4)
      rw [hout] at hf
      have h_ne_zero : ((Int.fmod (d.day - 1) 146097) % 36524 / 1461 * 4) + 4 ≠ 0 := Int.add_pos_ne_zero_of_nonneg hmul4 (by decide)
      exact False.elim (h_ne_zero hf)
      done

/-
Taken from 2.21 and 2.22 in the Gregorian Calendar chapter of Calendrical Calculations.
We can switch to using `/` and `%` instead of `fmod` and `fdiv` once we've uesd `fmod`
the first time, because `fmod` with a nonnegative modulus alwayd produces a positive remainder.
-/
def ScalarDate.toOrdinalDate (d : ScalarDate) : OrdinalDate := 
  /- We substract one since the measure is 1-based. -/
  let dayPred := d.day - 1
  /- So days < 146097; the days in the 100 groups. -/
  let hundredGroupsDays := dayPred.fmod 146097
  /- days < 36524; the days in the 4 groups -/
  let fourGroupDays := hundredGroupsDays % 36524
  /- days < 1461; the days in the singles -/
  let singlesGroupDays := fourGroupDays % 1461
  /- The number of 400 groups -/
  let num400YearGroups := dayPred.fdiv 146097
  /- The number of 100 groups -/
  let num100YearGroups := hundredGroupsDays / 36524
  /- The number of 4 groups -/
  let num4YearGroups := fourGroupDays / 1461
  /- Number of single years -/
  let numSingleYears : Int := singlesGroupDays / 365
  /- Years from the 400 groups -/
  let yearsFrom400Groups := num400YearGroups * 400
  /- Years from the 100 groups -/
  let yearsFrom100Groups := num100YearGroups * 100
  /- Years from the 4 groups -/
  let yearsFrom4Groups := num4YearGroups * 4
  let isLastDayOfLeapYear := num100YearGroups = 4 ∨ numSingleYears = 4
  /- Add one iff it's not the last day of a leap year. If it is the last day of a leap year, withhold that additional year. -/
  let year := Year.mk (yearsFrom400Groups + yearsFrom100Groups + yearsFrom4Groups + numSingleYears + (if isLastDayOfLeapYear then 0 else 1))
  let day := if isLastDayOfLeapYear then 366 else ((singlesGroupDays.fmod 365) + 1)

  have h_day_ge_one : 1 <= day.toNat := by
    by_cases hleap : isLastDayOfLeapYear <;> simp [hleap]
    case neg => 
      refine toOrdinalDate_helper1 ?hle
      exact Int.le_add_of_sub_right_le (Int.mod_nonneg _ (ne_of_lt pos365).symm)
  have hle' : Int.toNat day ≤ Year.numDaysInGregorianYear year := by
    by_cases hleap : isLastDayOfLeapYear <;> simp [hleap]
    -- If it is the last day of a leap year
    case pos => 
      have h_is_leap := ScalarDate.toOrdinalDateYear_leap d hleap
      simp_all [toOrdinalDateYear, hleap, Year.numDaysInGregorianYear]
      done
    -- If it's not the last day of a leap year.
    case neg => 
      generalize hday : (((Int.fmod (d.day - 1) 146097) % 36524) % 1461) % 365  = day
      generalize hy' : 
        Year.mk
          (Int.fdiv (d.day - 1) 146097 * 400 
          + (Int.fmod (d.day - 1) 146097) / 36524 * 100 
          + ((Int.fmod (d.day - 1) 146097) % 36524) / 1461 * 4 
          + (((Int.fmod (d.day - 1) 146097) % 36524) % 1461) / 365 + 1) = y'
      have hd' : day < 365 :=
        hday ▸ (Int.mod_lt_of_pos (((Int.fmod (d.day - 1) 146097) % 36524) % 1461) pos365)
      have hpos : 0 <= day := 
        hday ▸ (Int.mod_nonneg (((Int.fmod (d.day - 1) 146097) % 36524) % 1461) (ne_of_lt pos365).symm)
      exact Int.toNat_le_of_le_of_nonneg (Int.add_nonneg hpos (by decide)) (le_trans (hd' : (day + 1) <= 365) y'.num_days_in_gregorian_year_ge_365)
      done
  ⟨year, day.toNat, h_day_ge_one, hle'⟩ 

/-
Derived from 2.17 in Calendrical Calculations.
-/
def OrdinalDate.toScalarDate : OrdinalDate → ScalarDate
| ⟨⟨year⟩, ordinalDay, _, _⟩ =>
  let yearPred := year - 1
  -- number of 400 groups
  let fourHundredGroups := yearPred.fdiv 400
  -- number of 100 groups; 0-3
  let oneHundredGroups := (yearPred.fmod 400) / 100
  -- number of 4 groups; 0-24
  let fourGroups := (yearPred.fmod 100) / 4
  -- number of single years; 0, 1, 2, or 3
  let singles := yearPred.fmod 4
  let daysFrom400YearGroups := fourHundredGroups * 146097
  let daysFrom100YearGroups := oneHundredGroups * 36524
  let daysFrom4YearGroups := fourGroups * 1461
  let daysFrom1YearGroups := singles * 365
  ⟨daysFrom400YearGroups + daysFrom100YearGroups + daysFrom4YearGroups + daysFrom1YearGroups + ordinalDay⟩

def Ymd.toScalarDate (ymd : Ymd) : ScalarDate := ymd.toOrdinalDate.toScalarDate

def ScalarDate.toYmd (date : ScalarDate) : Ymd := date.toOrdinalDate.toYmd

def ScalarDate.year (d : ScalarDate) : Year := d.toYmd.year

def ScalarDate.fromYmd 
  (y : Year) 
  (m : Month) 
  (d : Nat)  
  (dayGe : d >= 1 := by decide)
  (dayLe : d <= m.numDays y := by decide) : ScalarDate :=
  (Ymd.mk y m d dayGe dayLe).toScalarDate
