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
import Timelib.Date.Convert
import Timelib.Util

/--
Proof that `Ymd` and `Ordinal` are Equivalent using their respective conversion functions
`Ymd.toOrdinalDate` and `OrdinalDate.toYmd`
-/

theorem Ymd.is_january_month {ymd : Ymd} (h_is_month_day : (ymd.toOrdinalDate).isJanuaryDay) : ymd.month = Month.january := by
  simp only [Ymd.toOrdinalDate]
  by_cases hLeap : ymd.year.isLeapYear <;>
    (simp_arith [hLeap, OrdinalDate.isJanuaryDay] at h_is_month_day
     simp only [Ymd.toOrdinalDate] at h_is_month_day
     simp only [hLeap]
     split at h_is_month_day <;> (simp (config := { arith := true }) at *; try assumption)
     case _ hM =>
       simp_arith [hM] at h_is_month_day
       exact False.elim ((show ¬0 >= 1 by decide) (h_is_month_day ▸ ymd.dayGe)))

theorem Ymd.is_february_month {ymd : Ymd} (h_is_month_day : ymd.toOrdinalDate.isFebruaryDay) : ymd.month = Month.february := by
  simp only [Ymd.toOrdinalDate]
  by_cases hLeap : ymd.year.isLeapYear <;>
    (simp_arith [hLeap, OrdinalDate.isFebruaryDay] at h_is_month_day
     simp only [Ymd.toOrdinalDate] at h_is_month_day
     simp only [hLeap]
     split at h_is_month_day <;> (simp (config := { arith := true }) [Month.numDays, hLeap] at *; try assumption)
     case _ hM =>
       have hDayLe := ymd.dayLe
       simp [hM, Month.numDays, hLeap] at hDayLe
       exact False.elim (not_le_and_ge_of_lt hDayLe (by decide) h_is_month_day.left)
     case _ hM =>
       simp_arith [hM, hLeap] at h_is_month_day
       exact False.elim ((show ¬0 >= 1 by decide) (h_is_month_day ▸ ymd.dayGe)))

theorem Ymd.is_march_month {ymd : Ymd} (h_is_month_day : ymd.toOrdinalDate.isMarchDay) : ymd.month = Month.march := by
  simp only [Ymd.toOrdinalDate]
  by_cases hLeap : ymd.year.isLeapYear <;> 
    (simp [hLeap, OrdinalDate.isMarchDay] at h_is_month_day
     simp only [Ymd.toOrdinalDate] at h_is_month_day
     simp only [hLeap]
     have hDayLe := ymd.dayLe
     split at h_is_month_day <;> (simp (config := { arith := true }) at *; try assumption)
     case _ hM =>
       simp [hM, Month.numDays, hLeap] at hDayLe
       exact False.elim (not_le_and_ge_of_lt hDayLe (by decide) h_is_month_day.left)
     case _ hM =>
       simp [hM, Month.numDays, hLeap] at hDayLe
       exact False.elim (not_le_and_ge_of_lt hDayLe (by decide) h_is_month_day.left)
     case _ hM =>
       simp_arith [hLeap] at h_is_month_day
       exact False.elim ((show ¬0 >= 1 by decide) (h_is_month_day ▸ ymd.dayGe)))

theorem Ymd.is_april_month {ymd : Ymd} (h_is_month_day : ymd.toOrdinalDate.isAprilDay) : ymd.month = Month.april := by
  simp only [Ymd.toOrdinalDate]
  by_cases hLeap : ymd.year.isLeapYear <;> 
  (simp [OrdinalDate.isAprilDay, hLeap] at h_is_month_day
   simp only [Ymd.toOrdinalDate] at h_is_month_day
   simp only [hLeap]
   have h_DayLe := ymd.dayLe
   split at h_is_month_day <;> (simp (config := { arith := true }) [Month.numDays, hLeap] at *; try assumption)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => exact False.elim ((show ¬0 >= 1 by decide) (h_is_month_day ▸ ymd.dayGe)))

theorem Ymd.is_may_month {ymd : Ymd} (h_is_month_day : ymd.toOrdinalDate.isMayDay) : ymd.month = Month.may := by
  simp only [Ymd.toOrdinalDate]
  by_cases hLeap : ymd.year.isLeapYear <;> 
  (simp [OrdinalDate.isMayDay, hLeap] at h_is_month_day
   simp only [Ymd.toOrdinalDate] at h_is_month_day
   simp only [hLeap]
   have h_DayLe := ymd.dayLe
   split at h_is_month_day <;> (simp (config := { arith := true }) [Month.numDays, hLeap] at *; try assumption)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => exact False.elim ((show ¬0 >= 1 by decide) (h_is_month_day ▸ ymd.dayGe)))

theorem Ymd.is_june_month {ymd : Ymd} (h_is_month_day : ymd.toOrdinalDate.isJuneDay) : ymd.month = Month.june := by
  simp only [Ymd.toOrdinalDate]
  by_cases hLeap : ymd.year.isLeapYear <;> 
  (simp [OrdinalDate.isJuneDay, hLeap] at h_is_month_day
   simp only [Ymd.toOrdinalDate] at h_is_month_day
   simp only [hLeap]
   have h_DayLe := ymd.dayLe
   split at h_is_month_day <;> (simp (config := { arith := true }) [Month.numDays, hLeap] at *; try assumption)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => 
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => exact False.elim ((show ¬0 >= 1 by decide) (h_is_month_day ▸ ymd.dayGe)))

theorem Ymd.is_july_month {ymd : Ymd} (h_is_month_day : ymd.toOrdinalDate.isJulyDay) : ymd.month = Month.july := by
  simp only [Ymd.toOrdinalDate]
  by_cases hLeap : ymd.year.isLeapYear <;> 
  (simp [OrdinalDate.isJulyDay, hLeap] at h_is_month_day
   simp only [Ymd.toOrdinalDate] at h_is_month_day
   simp only [hLeap]
   have h_DayLe := ymd.dayLe
   split at h_is_month_day <;> (simp (config := { arith := true }) [Month.numDays, hLeap] at *; try assumption)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => 
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => exact False.elim ((show ¬0 >= 1 by decide) (h_is_month_day ▸ ymd.dayGe)))

theorem Ymd.is_august_month {ymd : Ymd} (h_is_month_day : ymd.toOrdinalDate.isAugustDay) : ymd.month = Month.august := by
  simp only [Ymd.toOrdinalDate]
  by_cases hLeap : ymd.year.isLeapYear <;> 
  (simp [OrdinalDate.isAugustDay, hLeap] at h_is_month_day
   simp only [Ymd.toOrdinalDate] at h_is_month_day
   simp only [hLeap]
   have h_DayLe := ymd.dayLe
   split at h_is_month_day <;> (simp (config := { arith := true }) [Month.numDays, hLeap] at *; try assumption)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => 
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => exact False.elim ((show ¬0 >= 1 by decide) (h_is_month_day ▸ ymd.dayGe)))

theorem Ymd.is_september_month {ymd : Ymd} (h_is_month_day : ymd.toOrdinalDate.isSeptemberDay) : ymd.month = Month.september := by
  simp only [Ymd.toOrdinalDate]
  by_cases hLeap : ymd.year.isLeapYear <;> 
  (simp [OrdinalDate.isSeptemberDay, hLeap] at h_is_month_day
   simp only [Ymd.toOrdinalDate] at h_is_month_day
   simp only [hLeap]
   have h_DayLe := ymd.dayLe
   split at h_is_month_day <;> (simp (config := { arith := true }) [Month.numDays, hLeap] at *; try assumption)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => 
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => exact False.elim ((show ¬0 >= 1 by decide) (h_is_month_day ▸ ymd.dayGe)))

theorem Ymd.is_october_month {ymd : Ymd} (h_is_month_day : ymd.toOrdinalDate.isOctoberDay) : ymd.month = Month.october := by
  simp only [Ymd.toOrdinalDate]
  by_cases hLeap : ymd.year.isLeapYear <;> 
  (simp [OrdinalDate.isOctoberDay, hLeap] at h_is_month_day
   simp only [Ymd.toOrdinalDate] at h_is_month_day
   simp only [hLeap]
   have h_DayLe := ymd.dayLe
   split at h_is_month_day <;> (simp (config := { arith := true }) [Month.numDays, hLeap] at *; try assumption)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => 
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => exact False.elim ((show ¬0 >= 1 by decide) (h_is_month_day ▸ ymd.dayGe)))

theorem Ymd.is_november_month {ymd : Ymd} (h_is_month_day : ymd.toOrdinalDate.isNovemberDay) : ymd.month = Month.november := by
  simp only [Ymd.toOrdinalDate]
  by_cases hLeap : ymd.year.isLeapYear <;> 
  (simp [OrdinalDate.isNovemberDay, hLeap] at h_is_month_day
   simp only [Ymd.toOrdinalDate] at h_is_month_day
   simp only [hLeap]
   have h_DayLe := ymd.dayLe
   split at h_is_month_day <;> (simp (config := { arith := true }) [Month.numDays, hLeap] at *; try assumption)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => 
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day.left)
   case _ hM => exact False.elim ((show ¬0 >= 1 by decide) (h_is_month_day ▸ ymd.dayGe)))

theorem Ymd.is_december_month {ymd : Ymd} (h_is_month_day : ymd.toOrdinalDate.isDecemberDay) : ymd.month = Month.december := by
  simp only [Ymd.toOrdinalDate]
  by_cases hLeap : ymd.year.isLeapYear <;> 
  (simp [OrdinalDate.isDecemberDay, hLeap] at h_is_month_day
   simp only [Ymd.toOrdinalDate] at h_is_month_day
   simp only [hLeap]
   have h_DayLe := ymd.dayLe
   split at h_is_month_day <;> (simp (config := { arith := true }) [Month.numDays, hLeap] at *; try assumption)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day)
   case _ hM =>
     simp [hM, Month.numDays, hLeap] at h_DayLe
     exact False.elim (not_le_and_ge_of_lt h_DayLe (by decide) h_is_month_day))


theorem OrdinalDate.toYmd_right_inv (ordinal : OrdinalDate) : ordinal.toYmd.toOrdinalDate = ordinal := by
  by_cases hLeap : ordinal.year.isLeapYear <;> 
  (simp [OrdinalDate.toYmd, hLeap]
   split
   case _ hJan => simp [Ymd.toOrdinalDate, hJan]
   case _ hJan =>
      split
      case _ hFeb => 
        simp [hFeb, Ymd.toOrdinalDate]
        apply OrdinalDate.eq_of_val_eq
        case h_year => simp
        case h_day => exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.gt_of_not_le hJan))
      case _ hFeb =>
        split
        case _ hMar => 
          simp [hMar, Ymd.toOrdinalDate, hLeap]
          apply OrdinalDate.eq_of_val_eq
          case h_year => simp
          case h_day => exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.gt_of_not_le hFeb))
        case _ hMar =>
          split
          case _ hApr => 
            simp [hApr, Ymd.toOrdinalDate, hLeap]
            apply OrdinalDate.eq_of_val_eq
            case h_year => simp
            case h_day => exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.gt_of_not_le hMar))
          case _ hApr =>
            split
            case _ hMay => 
              simp [hMay, Ymd.toOrdinalDate, hLeap]
              apply OrdinalDate.eq_of_val_eq
              case h_year => simp
              case h_day => exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.gt_of_not_le hApr))
            case _ hMay =>
                split
                case _ hJun => 
                  simp [hJun, Ymd.toOrdinalDate, hLeap]
                  apply OrdinalDate.eq_of_val_eq
                  case h_year => simp
                  case h_day => exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.gt_of_not_le hMay))
                case _ hJun =>
                  split
                  case _ hJul => 
                    simp [hJul, Ymd.toOrdinalDate, hLeap]
                    apply OrdinalDate.eq_of_val_eq
                    case h_year => simp
                    case h_day => exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.gt_of_not_le hJun))
                  case _ hJul =>
                    split
                    case _ hAug => 
                      simp [hAug, Ymd.toOrdinalDate, hLeap]
                      apply OrdinalDate.eq_of_val_eq
                      case h_year => simp
                      case h_day => exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.gt_of_not_le hJul))
                    case _ hAug =>
                      split
                      case _ hSep => 
                        simp [hSep, Ymd.toOrdinalDate, hLeap]
                        apply OrdinalDate.eq_of_val_eq
                        case h_year => simp
                        case h_day => exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.gt_of_not_le hAug))
                      case _ hSep =>
                        split
                        case _ hOct => 
                          simp [hOct, Ymd.toOrdinalDate, hLeap]
                          apply OrdinalDate.eq_of_val_eq
                          case h_year => simp
                          case h_day => exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.gt_of_not_le hSep))
                        case _ hOct =>
                          split
                          case _ hNov => 
                            simp [hNov, Ymd.toOrdinalDate, hLeap]
                            apply OrdinalDate.eq_of_val_eq
                            case h_year => simp
                            case h_day => exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.gt_of_not_le hOct))
                          case _ hNov =>
                            simp [hNov, Ymd.toOrdinalDate, hLeap]
                            apply OrdinalDate.eq_of_val_eq
                            case h_year => simp
                            case h_day => exact Nat.sub_add_cancel (Nat.le_of_lt (Nat.gt_of_not_le hNov)))

theorem Ymd.toOrdinalDate_left_inv (ymd : Ymd) : ymd.toOrdinalDate.toYmd = ymd := by
  simp [OrdinalDate.toYmd]
  by_cases hLeap : ymd.year.isLeapYear <;> 
  (simp [hLeap, Ymd.toOrdinalDate_year_same]
   split 
   case _ hJan => 
     have h_is_month_day : ymd.toOrdinalDate.isJanuaryDay := by simp [OrdinalDate.isJanuaryDay]; exact hJan
     apply Ymd.eq_of_val_eq <;> simp [Ymd.toOrdinalDate, (Ymd.is_january_month h_is_month_day), hLeap, Nat.add_sub_cancel]
   case _ hJan =>
     split
     case _ hFeb => 
         have h_is_month_day : ymd.toOrdinalDate.isFebruaryDay := by
           simp [OrdinalDate.isFebruaryDay, Year.lastDayFebruary, hLeap]
           exact And.intro (Nat.gt_of_not_le hJan) hFeb
         apply Ymd.eq_of_val_eq <;> simp [Ymd.toOrdinalDate, (Ymd.is_february_month h_is_month_day), hLeap, Nat.add_sub_cancel]
     case _ hFeb =>
       split
       case _ hMar => 
         have h_is_month_day : ymd.toOrdinalDate.isMarchDay := by
           simp [OrdinalDate.isMarchDay, Year.lastDayMarch, hLeap]
           exact And.intro (Nat.gt_of_not_le hFeb) hMar
         apply Ymd.eq_of_val_eq <;> simp [Ymd.toOrdinalDate, (Ymd.is_march_month h_is_month_day), hLeap, Nat.add_sub_cancel]
       case _ hMar =>
         split
         case _ hApr => 
           have h_is_month_day : ymd.toOrdinalDate.isAprilDay := by
             simp [OrdinalDate.isAprilDay, Year.lastDayApril, hLeap]
             exact And.intro (Nat.gt_of_not_le hMar) hApr
           apply Ymd.eq_of_val_eq <;> simp [Ymd.toOrdinalDate, (Ymd.is_april_month h_is_month_day), hLeap, Nat.add_sub_cancel]
         case _ hApr =>
           split
           case _ hMay => 
             have h_is_month_day : ymd.toOrdinalDate.isMayDay := by
               simp [OrdinalDate.isMayDay, Year.lastDayMay, hLeap]
               exact And.intro (Nat.gt_of_not_le hApr) hMay
             apply Ymd.eq_of_val_eq <;> simp [Ymd.toOrdinalDate, (Ymd.is_may_month h_is_month_day), hLeap, Nat.add_sub_cancel]
           case _ hMay =>
               split
               case _ hJun => 
                 have h_is_month_day : ymd.toOrdinalDate.isJuneDay := by
                   simp [OrdinalDate.isJuneDay, Year.lastDayJune, hLeap]
                   exact And.intro (Nat.gt_of_not_le hMay) hJun
                 apply Ymd.eq_of_val_eq <;> simp [Ymd.toOrdinalDate, (Ymd.is_june_month h_is_month_day), hLeap, Nat.add_sub_cancel]
               case _ hJun =>
                 split
                 case _ hJul => 
                   have h_is_month_day : ymd.toOrdinalDate.isJulyDay := by
                     simp [OrdinalDate.isJulyDay, Year.lastDayJuly, hLeap]
                     exact And.intro (Nat.gt_of_not_le hJun) hJul
                   apply Ymd.eq_of_val_eq <;> simp [Ymd.toOrdinalDate, (Ymd.is_july_month h_is_month_day), hLeap, Nat.add_sub_cancel]
                 case _ hJul =>
                   split
                   case _ hAug => 
                     have h_is_month_day : ymd.toOrdinalDate.isAugustDay := by
                       simp [OrdinalDate.isAugustDay, Year.lastDayAugust, hLeap]
                       exact And.intro (Nat.gt_of_not_le hJul) hAug
                     apply Ymd.eq_of_val_eq <;> simp [Ymd.toOrdinalDate, (Ymd.is_august_month h_is_month_day), hLeap, Nat.add_sub_cancel]
                   case _ hAug =>
                     split
                     case _ hSep => 
                       have h_is_month_day : ymd.toOrdinalDate.isSeptemberDay := by
                         simp [OrdinalDate.isSeptemberDay, Year.lastDaySeptember, hLeap]
                         exact And.intro (Nat.gt_of_not_le hAug) hSep
                       apply Ymd.eq_of_val_eq <;> simp [Ymd.toOrdinalDate, (Ymd.is_september_month h_is_month_day), hLeap, Nat.add_sub_cancel]
                     case _ hSep =>
                       split
                       case _ hOct => 
                         have h_is_month_day : ymd.toOrdinalDate.isOctoberDay := by
                           simp [OrdinalDate.isOctoberDay, Year.lastDayOctober, hLeap]
                           exact And.intro (Nat.gt_of_not_le hSep) hOct
                         apply Ymd.eq_of_val_eq <;> simp [Ymd.toOrdinalDate, (Ymd.is_october_month h_is_month_day), hLeap, Nat.add_sub_cancel]
                       case _ hOct =>
                         split
                         case _ hNov => 
                           have h_is_month_day : ymd.toOrdinalDate.isNovemberDay := by
                             simp [OrdinalDate.isNovemberDay, Year.lastDayNovember, hLeap]
                             exact And.intro (Nat.gt_of_not_le hOct) hNov
                           apply Ymd.eq_of_val_eq <;> simp [Ymd.toOrdinalDate, (Ymd.is_november_month h_is_month_day), hLeap, Nat.add_sub_cancel]
                         case _ hNov =>
                           have h_is_month_day : ymd.toOrdinalDate.isDecemberDay := by
                             simp [OrdinalDate.isDecemberDay, hLeap]
                             exact Nat.gt_of_not_le hNov
                           apply Ymd.eq_of_val_eq <;> simp [Ymd.toOrdinalDate, (Ymd.is_december_month h_is_month_day), hLeap, Nat.add_sub_cancel])

