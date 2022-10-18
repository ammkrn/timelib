import Lean.Data.Json
import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.SimpRw
import Mathlib.Data.Equiv.Basic
import Mathlib.Init.Data.Int.Order

open Lean

/--
A year in the proleptic gregorian calendar
-/
structure Year where
  val : Int
deriving DecidableEq, Repr

instance (n : Nat) : OfNat Year n where
  ofNat := Year.mk n

instance : LE Year where
  le := InvImage Int.le Year.val

instance : LT Year where
  lt := InvImage Int.lt Year.val

theorem Year.le_def {y₁ y₂ : Year} : (y₁ <= y₂) = (y₁.val <= y₂.val) := rfl
theorem Year.lt_def {y₁ y₂ : Year} : (y₁ < y₂) = (y₁.val < y₂.val) := rfl

instance instDecidableLEYear (y₁ y₂ : Year) : Decidable (y₁ <= y₂) := inferInstanceAs (Decidable (y₁.val <= y₂.val))
instance instDecidableLTYear (y₁ y₂ : Year) : Decidable (y₁ < y₂) := inferInstanceAs (Decidable (y₁.val < y₂.val))

theorem Year.val_eq_of_eq : ∀ {y₁ y₂ : Year} (h : y₁ = y₂), y₁.val = y₂.val
| ⟨_⟩, _, rfl => rfl

theorem Year.eq_of_val_eq : ∀ {y₁ y₂ : Year} (h : y₁.val = y₂.val), y₁ = y₂
| ⟨_⟩, _, rfl => rfl

instance : LinearOrder Year where
  le_refl (a) := le_refl a.val
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply Year.eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp [Year.le_def, le_total]
  decidable_le := inferInstance

instance : Ord Year := ⟨fun y₁ y₂ => compareOfLessAndEq y₁ y₂⟩

theorem Year.monotonic {y₁ y₂ : Year} : y₁.val <= y₂.val -> y₁ <= y₂ := 
  fun h => (Year.le_def) ▸ h

instance : ToString Year where
  toString y := ToString.toString y.val

instance : Equiv Int Year where
  toFun := Year.mk
  invFun := Year.val
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]


/-- 
The definition of a leap year given by the United States Naval Observatory:
"Every year that is exactly divisible by four is a leap year, except for years that 
are exactly divisible by 100, but these centurial years are leap years if they 
are exactly divisible by 400. For example, the years 1700, 1800, and 1900 are not 
leap years, but the years 1600 and 2000 are."
-/
@[reducible] 
abbrev Year.isLeapYear (y : Year) : Prop := (y.val % 4 = 0 ∧ y.val % 100 ≠ 0) ∨ (y.val % 400 = 0)

@[reducible] abbrev Year.numDaysInGregorianYear (y : Year) : Nat := 365 + (if y.isLeapYear then 1 else 0)

theorem Year.num_days_in_gregorian_year_eq (y : Year) : (y.numDaysInGregorianYear = 365) ∨ (y.numDaysInGregorianYear = 366) := by
  by_cases h : y.isLeapYear <;> simp only [numDaysInGregorianYear, h]

theorem Year.num_days_in_gregorian_year_ge_365 (y : Year) : (365 : Int) <= ↑y.numDaysInGregorianYear := by
  by_cases h : y.isLeapYear <;> simp only [numDaysInGregorianYear, h]

theorem Year.num_days_in_gregorian_year_pos (y : Year) : 0 < y.numDaysInGregorianYear :=  
  match y.num_days_in_gregorian_year_eq with
  | Or.inl hl => by rw [hl]; apply Nat.zero_lt_succ 
  | Or.inr hr => by rw [hr]; apply Nat.zero_lt_succ

/--
A cycle of 400 years has (365 * 400) + 97 days, for an average year length 
of 365.2425 days.
-/
abbrev Year.daysIn400Group : Nat := 146097

/--
If the last year is a leap year, a cycle of 100 years contains 36525 days
(365 * 100) + 25 = 36525

Otherwise, if the last year is not a leap year, a cycle of 100 years contains 36525 days
(365 * 100) + 24 = 36524
-/
abbrev Year.daysIn100Group (y : Year) : Nat := if y.isLeapYear then 36525 else 36524
theorem Year.days_in_100_group_pos (y : Year) : 0 < y.daysIn100Group := by
  simp [daysIn100Group]; split <;> simp

/--
The number of days in a group of four years.
-/
abbrev Year.daysIn4Group (y : Year) : Nat := if y.isLeapYear then 1461 else 1460

theorem Year.days_in_4_group_pos (y : Year) : 0 < y.daysIn4Group := by simp [daysIn4Group]; split <;> simp

@[simp] abbrev Year.lastDayJanuary : Nat := 31
@[simp] abbrev Year.lastDayFebruary  (y : Year) : Nat := 59  + (ite y.isLeapYear 1 0)  
@[simp] abbrev Year.lastDayMarch     (y : Year) : Nat := 90  + (ite y.isLeapYear 1 0)  
@[simp] abbrev Year.lastDayApril     (y : Year) : Nat := 120 + (ite y.isLeapYear 1 0)  
@[simp] abbrev Year.lastDayMay       (y : Year) : Nat := 151 + (ite y.isLeapYear 1 0)  
@[simp] abbrev Year.lastDayJune      (y : Year) : Nat := 181 + (ite y.isLeapYear 1 0)  
@[simp] abbrev Year.lastDayJuly      (y : Year) : Nat := 212 + (ite y.isLeapYear 1 0)  
@[simp] abbrev Year.lastDayAugust    (y : Year) : Nat := 243 + (ite y.isLeapYear 1 0)  
@[simp] abbrev Year.lastDaySeptember (y : Year) : Nat := 273 + (ite y.isLeapYear 1 0)  
@[simp] abbrev Year.lastDayOctober   (y : Year) : Nat := 304 + (ite y.isLeapYear 1 0)  
@[simp] abbrev Year.lastDayNovember  (y : Year) : Nat := 334 + (ite y.isLeapYear 1 0)  
@[simp] abbrev Year.lastDayDecember  (y : Year) : Nat := 365 + (ite y.isLeapYear 1 0)  
