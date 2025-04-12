import Timelib.Util
import Timelib.Date.Year
import Timelib.Date.Month

namespace Timelib

@[ext]
structure Ymd where
  year : Year
  month : Month
  day : Nat
  dayGe : day ≥ 1
  dayLe : day ≤ month.numDays year
deriving Repr

namespace Ymd

theorem eq_of_val_eq : ∀ {o₁ o₂ : Ymd} (_ : o₁.year = o₂.year) (_ : o₁.month = o₂.month) (_ : o₁.day = o₂.day), o₁ = o₂
| ⟨y₁, m₁, d₁, hGt₁, hLt₁⟩, ⟨y₂, m₂, d₂, hGt₂, hLt₂⟩, hy, hm, hd => by
  simp [hy, hm, hd]; exact ⟨hy, hm, hd⟩

instance : Ord Ymd where
  compare d₁ d₂ :=
    match Ord.compare d₁.year d₂.year with
    | Ordering.eq =>
      match Ord.compare d₁.month d₂.month with
      | Ordering.eq => Ord.compare d₁.day d₂.day
      | owise => owise
    | owise => owise

instance : LE Ymd := leOfOrd
instance : LT Ymd := ltOfOrd

theorem le_def (d₁ d₂ : Ymd) : (d₁ ≤ d₂) = (compare d₁ d₂).isLE := rfl
theorem lt_def (d₁ d₂ : Ymd) : (d₁ < d₂) = (Ord.compare d₁ d₂ = Ordering.lt) := rfl

theorem lt_def' (d₁ d₂ : Ymd) :
  (d₁ < d₂) =
  (d₁.year < d₂.year
   ∨ (d₁.year = d₂.year ∧ d₁.month < d₂.month)
   ∨ (d₁.year = d₂.year ∧ d₁.month = d₂.month ∧ d₁.day < d₂.day)) := by
   simp only [lt_def, compare, compareOfLessAndEq, eq_iff_iff]

   rcases Year.lt_trichotomy d₁.year d₂.year with year_lt | year_eq | year_gt
   . simp [year_lt]
   .
     have year_irrefl1 := Year.lt_irrefl d₁.year
     have year_irrefl2 := Year.lt_irrefl d₂.year
     simp only [year_eq, year_irrefl2, ↓reduceIte, true_and, false_or]
     rcases Month.lt_trichotomy d₁.month d₂.month with month_lt | month_eq | month_gt
     . simp [month_lt]
     .
       have month_irrefl := Month.lt_irrefl d₂.month
       rcases Nat.lt_trichotomy d₁.day d₂.day with day_lt | day_eq | day_gt
       .
         simp [month_eq, month_irrefl]
         refine Iff.intro ?mp0 ?mpr0
         . exact (fun _ => day_lt)
         . simp [Nat.ne_of_lt day_lt]
       . simp [month_eq, month_irrefl, ↓reduceIte, day_eq, Nat.lt_irrefl, reduceCtorEq]
       .
         simp [month_eq, month_irrefl]
         refine Iff.intro ?mp ?mpr
         . simp [Ne.symm <| Nat.ne_of_lt day_gt]
         . exact (fun day_lt => False.elim ((Nat.not_lt_of_gt day_gt) day_lt))
     . simp [Month.not_lt_of_gt month_gt, Ne.symm <| Month.ne_of_lt month_gt]
   . simp [Year.not_lt_of_gt year_gt, Ne.symm (Year.ne_of_lt _ _ year_gt)]

theorem le_def' (d₁ d₂ : Ymd) :
  (d₁ <= d₂) =
  (d₁.year < d₂.year ∨ (d₁.year = d₂.year ∧ d₁.month < d₂.month) ∨ (d₁.year = d₂.year ∧ d₁.month = d₂.month ∧ d₁.day <= d₂.day)) := by
   simp only [le_def, Ordering.isLE, compare, compareOfLessAndEq, eq_iff_iff]
   rcases Year.lt_trichotomy d₁.year d₂.year with year_lt | year_eq | year_gt
   . simp [year_lt]
   .
     have year_irrefl1 := Year.lt_irrefl d₁.year
     have year_irrefl2 := Year.lt_irrefl d₂.year
     simp only [year_eq, year_irrefl2, ↓reduceIte, true_and, false_or]
     rcases Month.lt_trichotomy d₁.month d₂.month with month_lt | month_eq | month_gt
     . simp [month_lt]
     .
       have month_irrefl := Month.lt_irrefl d₂.month
       rcases Nat.lt_trichotomy d₁.day d₂.day with day_lt | day_eq | day_gt
       .
         simp [month_eq, month_irrefl]
         refine Iff.intro ?mp0 ?mpr0
         . simp [Nat.le_of_lt day_lt]
         . simp [day_lt]
       . simp [month_eq, month_irrefl, day_eq]
       .
         simp [month_eq, month_irrefl]
         refine Iff.intro ?mp ?mpr
         . simp [Nat.not_lt_of_gt day_gt, Nat.ne_of_gt day_gt]
         . simp [Nat.not_le_of_gt day_gt]
     . simp [Month.not_lt_of_gt month_gt, Ne.symm <| Month.ne_of_lt month_gt]
   . simp [Year.not_lt_of_gt year_gt, Ne.symm (Year.ne_of_lt _ _ year_gt)]


theorem lt_trichotomy {y₁ y₂ : Ymd} : (y₁ < y₂) ∨ y₁ = y₂ ∨ (y₂ < y₁) := by
  rcases Year.lt_trichotomy y₁.year y₂.year with year_lt | year_eq | year_gt
  . simp [lt_def', year_lt]
  .
    rcases Month.lt_trichotomy y₁.month y₂.month with month_lt | month_eq | month_gt
    .
      simp [lt_def', year_eq, month_lt]
    .
      rcases Nat.lt_trichotomy y₁.day y₂.day with day_lt | day_eq | day_gt
      . simp [lt_def', year_eq, month_eq, day_lt]
      . simp [eq_of_val_eq year_eq month_eq day_eq]
      . simp [lt_def', year_eq, month_eq, day_gt]
    . simp [lt_def', year_eq, month_gt]
  . simp [lt_def', year_gt]

theorem numDays_pos (ymd : Ymd) : 0 < ymd.month.numDays ymd.year := by
  simp only [Month.numDays]
  by_cases hy : ymd.year.isLeapYear <;> (split <;> simp [hy, if_true, if_false])

theorem month_numDays_lt_gregorianYearNumDays (ymd : Ymd) : ymd.month.numDays ymd.year < ymd.year.numDaysInGregorianYear := by
  simp only [Month.numDays, Year.numDaysInGregorianYear]
  by_cases hy : ymd.year.isLeapYear <;>
  · simp [hy, if_true, if_false]
    split
    all_goals decide

theorem day_lt_gregorianYearNumDays (ymd : Ymd) : ymd.day < ymd.year.numDaysInGregorianYear :=
  Nat.lt_of_le_of_lt ymd.dayLe ymd.month_numDays_lt_gregorianYearNumDays

theorem le_refl (d: Ymd) : d <= d := by
  simp only [le_def', true_and, Nat.le_refl, and_self, or_true]

theorem le_total (y₁ y₂ : Ymd) : y₁ ≤ y₂ ∨ y₂ ≤ y₁ := by
  rcases Year.lt_trichotomy y₁.year y₂.year with year_lt | year_eq | year_gt
  . simp [le_def', year_lt]
  .
    rcases Month.lt_trichotomy y₁.month y₂.month with month_lt | month_eq | month_gt
    . simp [le_def', year_eq, month_lt]
    .
      rcases Nat.lt_trichotomy y₁.day y₂.day with day_lt | day_eq | day_gt
      . simp [le_def', year_eq, month_eq, Nat.le_of_lt day_lt]
      . simp [le_def', year_eq, month_eq, Nat.le_of_eq day_eq]
      . simp [le_def', year_eq, month_eq, Nat.le_of_lt day_gt]
    . simp [le_def', year_eq, month_gt]
  . simp [le_def', year_gt]

theorem lt_or_eq_of_le {d₁ d₂ : Ymd} : d₁ <= d₂ → d₁ < d₂ ∨ d₁ = d₂ := by
  rw [le_def', lt_def']
  intro hLe
  rcases hLe with year_lt | year_eq | year_gt
  . simp [year_lt]
  . simp [year_eq]
  .
    match Nat.eq_or_lt_of_le year_gt.right.right with
    | .inl hl => exact Or.inr (eq_of_val_eq year_gt.left year_gt.right.left hl)
    | .inr hr => exact .inl (.inr (.inr ⟨year_gt.left, ⟨year_gt.right.left, hr⟩⟩))

theorem lt_inl {d₁ d₂ : Ymd} : d₁.year < d₂.year → d₁ < d₂ := by
  rw [lt_def']; exact Or.inl

theorem lt_inr_inl {d₁ d₂ : Ymd} : d₁.year = d₂.year → d₁.month < d₂.month → d₁ < d₂ := by
  intro hy hm; rw [lt_def']; exact .inr (.inl ⟨hy, hm⟩)

theorem lt_inr_inr {d₁ d₂ : Ymd} : d₁.year = d₂.year → d₁.month = d₂.month → d₁.day < d₂.day → d₁ < d₂ := by
  intro hy hm hd; rw [lt_def']; exact .inr (.inr ⟨hy, ⟨hm, hd⟩⟩)

--@[reducible]
--def validISO8601Basic (xs : List Char) : Prop :=
--  xs.length = 8 ∧ xs.all Char.isDigit
--
--@[reducible]
--def validISO8601Basic_s (s : String) : Prop :=
--  validISO8601Basic s.data
--
--def printISO8601Basic (d : Ymd) : 0 < d.year → d.year ≤ 9999 → String
--  | _, _ =>
--    let y := printNumberPadded d.year.val.toNat 4
--    let m := printNumberPadded d.month.val 2
--    let d := printNumberPadded d.day 2
--    y ++ m ++ d
--
--theorem basic_allDigits (d : Ymd) : (h : 0 < d.year) → (h' : d.year ≤ 9999) → (d.printISO8601Basic h h').data.all Char.isDigit := by
--  intros
--  have hy := printNumberPadded_digits d.year.val.toNat 4
--  have hm := printNumberPadded_digits d.month.val 2
--  have hd := printNumberPadded_digits d.day 2
--  simp only [printISO8601Basic, String.data_append, List.all_append, hy, hm, hd, Bool.and_self]
--  done
--
--def printISO8601Basic? (d : Ymd) : Option String :=
--  if h : 0 < d.year ∧ d.year ≤ 9999 then some (d.printISO8601Basic h.left h.right) else none
--
--theorem basic?_imp {d : Ymd} : d.printISO8601Basic?.isSome → 0 < d.year ∧ d.year ≤ 9999 := by
--  simp only [printISO8601Basic?, Option.isSome_dite, imp_self]
--
--theorem basic?_eq {d : Ymd} (h : d.printISO8601Basic?.isSome) :
--  d.printISO8601Basic?.get h = (d.printISO8601Basic (basic?_imp h).left (basic?_imp h).right) := by
--  simp only [printISO8601Basic?, Option.get_dite]
--
--theorem basic?_allDigits (d : Ymd) (h : d.printISO8601Basic?.isSome) :
--  ((d.printISO8601Basic?.get h).data.all Char.isDigit) := by
--  have h0 := basic?_imp h
--  simp only [basic?_eq h, d.basic_allDigits h0.left h0.right]
--
--def printISO8601Extended (d : Ymd) : 0 < d.year → d.year ≤ 9999 → String
--  | _, _ =>
--    let y := printNumberPadded d.year.val.toNat 4
--    let m := printNumberPadded d.month.val 2
--    let d := printNumberPadded d.day 2
--    y ++ "-" ++ m ++ "-" ++ d
--
--def printISO8601Extended? (d : Ymd) : Option String :=
--  if h : 0 < d.year ∧ d.year ≤ 9999 then some (d.printISO8601Extended h.left h.right) else none
--
--def parseISO8601Basic (s : String) : Option Ymd :=
--  let xs := s.data
--  let y := xs.take 4
--  let m := (xs.drop 4).take 2
--  let d := (xs.drop 6).take 2
--  if y.length = 4 ∧ m.length = 2 ∧ d.length = 2 ∧ y.all Char.isDigit ∧ m.all Char.isDigit ∧ d.all Char.isDigit
--  then
--    let y := Year.mk <| Int.ofNat <| parseFoldl y
--    let m := parseFoldl m
--    let d := parseFoldl d
--    if h_m : 1 ≤ m ∧ m ≤ 12
--    then
--      let m := Month.mk m h_m.left h_m.right
--      if h_d : 1 ≤ d ∧ d ≤ m.numDays y
--      then some ⟨y, m, d, h_d.left, h_d.right⟩
--      else none
--    else
--      none
--  else
--    none
--
