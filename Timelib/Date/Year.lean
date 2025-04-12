
namespace Timelib

/--
A year in the proleptic Gregorian calendar. Newtyped as a structure for downstream type safety
-/
@[ext]
structure Year where
  val : Int
deriving DecidableEq, Repr

namespace Year

instance (n : Nat) : OfNat Year n where
  ofNat := Year.mk n

instance : LE Year where
  le := InvImage Int.le Year.val

instance : LT Year where
  lt := InvImage Int.lt Year.val

theorem le_def {y₁ y₂ : Year} : (y₁ <= y₂) = (y₁.val <= y₂.val) := rfl
theorem lt_def {y₁ y₂ : Year} : (y₁ < y₂) = (y₁.val < y₂.val) := rfl

theorem lt_trichotomy (y₁ y₂ : Year) : (y₁ < y₂) ∨ y₁ = y₂ ∨ (y₂ < y₁) := by
  rcases Int.lt_trichotomy y₁.val y₂.val with a | b | c
  . exact Or.inl (lt_def ▸ a)
  . exact Or.inr (Or.inl (Year.mk.injEq y₁.val y₂.val ▸ b))
  . exact Or.inr (Or.inr (lt_def ▸ c))

theorem lt_irrefl (y : Year) : ¬(y < y) := by simp only [lt_def, Int.lt_irrefl, not_false_eq_true]; done

theorem ne_of_lt (y₁ y₂: Year) : y₁ < y₂ → y₁ ≠ y₂ :=
  fun hlt heq => (lt_irrefl y₁) (heq ▸ hlt)

theorem le_total (y₁ y₂ : Year) : y₁ ≤ y₂ ∨ y₂ ≤ y₁ :=
  Int.le_total y₁.val y₂.val

theorem lt_asymm (y₁ y₂ : Year) : y₁ < y₂ → ¬(y₂ < y₁) := by
  simp only [lt_def]
  exact fun h => Int.not_lt.mpr (Int.le_of_lt h)

instance instDecidableLEYear (y₁ y₂ : Year) : Decidable (y₁ <= y₂) := inferInstanceAs (Decidable (y₁.val <= y₂.val))
instance instDecidableLTYear (y₁ y₂ : Year) : Decidable (y₁ < y₂) := inferInstanceAs (Decidable (y₁.val < y₂.val))

theorem val_eq_of_eq : ∀ {y₁ y₂ : Year} (_ : y₁ = y₂), y₁.val = y₂.val
| ⟨_⟩, _, rfl => rfl

theorem eq_of_val_eq : ∀ {y₁ y₂ : Year} (_ : y₁.val = y₂.val), y₁ = y₂
| ⟨_⟩, _, rfl => rfl

instance : Ord Year := ⟨fun y₁ y₂ => compareOfLessAndEq y₁ y₂⟩

theorem monotonic {y₁ y₂ : Year} : y₁.val <= y₂.val -> y₁ <= y₂ :=
  fun h => Year.le_def ▸ h

instance : ToString Year where
  toString y := ToString.toString y.val

/--
The definition of a leap year given by the United States Naval Observatory:
"Every year that is exactly divisible by four is a leap year, except for years that
are exactly divisible by 100, but these centurial years are leap years if they
are exactly divisible by 400. For example, the years 1700, 1800, and 1900 are not
leap years, but the years 1600 and 2000 are."
-/
@[reducible]
def isLeapYear (y : Year) : Prop := (y.val % 4 = 0 ∧ y.val % 100 ≠ 0) ∨ (y.val % 400 = 0)

@[reducible] def numDaysInGregorianYear (y : Year) : Nat := 365 + (if y.isLeapYear then 1 else 0)

theorem num_days_in_gregorian_year_eq (y : Year) : (y.numDaysInGregorianYear = 365) ∨ (y.numDaysInGregorianYear = 366) := by
  by_cases h : y.isLeapYear <;> simp [numDaysInGregorianYear, h, ite_true, Nat.add_right_eq_self,
    or_true]

theorem num_days_in_gregorian_year_ge_365 (y : Year) : (365 : Int) <= ↑y.numDaysInGregorianYear := by
  by_cases h : y.isLeapYear <;> simp [numDaysInGregorianYear, h, ite_true, Int.natCast_add]

theorem num_days_in_gregorian_year_le_366 (y : Year) : y.numDaysInGregorianYear <= 366 := by
  dsimp only [numDaysInGregorianYear]
  by_cases h: y.isLeapYear
  case pos => simp only [h, ↓reduceIte, Nat.reduceAdd, Nat.le_refl]
  case neg => simp only [h, ↓reduceIte, Nat.add_zero, Nat.reduceLeDiff]

theorem num_days_in_gregorial_year_eq_365 (y : Year) : ¬y.isLeapYear → y.numDaysInGregorianYear = 365 := by
  intro h; simp [numDaysInGregorianYear, h]

theorem num_days_in_gregorial_year_eq_366 (y : Year) : y.isLeapYear → y.numDaysInGregorianYear = 366 := by
  intro h;  simp [numDaysInGregorianYear, h]

theorem num_days_in_gregorian_year_pos (y : Year) : 0 < y.numDaysInGregorianYear :=
  match y.num_days_in_gregorian_year_eq with
  | Or.inl hl => by rw [hl]; apply Nat.zero_lt_succ
  | Or.inr hr => by rw [hr]; apply Nat.zero_lt_succ

/--
A cycle of 400 years has (365 * 400) + 97 days, for an average year length
of 365.2425 days.
-/
abbrev daysIn400Group : Nat := 146097

/--
If the last year is a leap year, a cycle of 100 years contains 36525 days
(365 * 100) + 25 = 36525

Otherwise, if the last year is not a leap year, a cycle of 100 years contains 36524 days
(365 * 100) + 24 = 36524
-/
abbrev daysIn100Group (y : Year) : Nat := if y.isLeapYear then 36525 else 36524

theorem days_in_100_group_pos (y : Year) : 0 < y.daysIn100Group := by
  simp [daysIn100Group]; split <;> simp

/--
The number of days in a group of four years.
-/
abbrev daysIn4Group (y : Year) : Nat := if y.isLeapYear then 1461 else 1460

theorem days_in_4_group_pos (y : Year) : 0 < y.daysIn4Group := by simp [daysIn4Group]; split <;> simp

theorem not_lt_of_gt {y₁ y₂ : Year} : y₁ > y₂ → ¬y₁ < y₂ := by
  intro h; simp [lt_def] at *; omega

theorem ofNat_le_of_le (a b : Nat) : a ≤ b → (⟨Int.ofNat a⟩: Year) ≤ (⟨Int.ofNat b⟩ : Year) := by
  intro _; simpa only [Year.le_def, Int.ofNat_eq_coe, Int.ofNat_le]
