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

open Lean

structure OrdinalDate where
  year : Year
  day : Nat
  hGe : day >= 1  
  hLe : day <= year.numDaysInGregorianYear
deriving Repr

instance : ToJson OrdinalDate where
  toJson od := Json.mkObj [("year", ToJson.toJson od.year.val), ("day", od.day)]

instance : FromJson OrdinalDate where
  fromJson? j := do
    let (year : Year) ← (fromJson? (← j.getObjVal? "year")).map Year.mk
    let (day : Nat) ← fromJson? (← j.getObjVal? "day")
    if h : day >= 1 ∧ day <= year.numDaysInGregorianYear
    then return OrdinalDate.mk year day h.left h.right
    else Except.error s!"OrdinalDate day out of range: {day}"


theorem OrdinalDate.eq_of_val_eq : ∀ {o₁ o₂ : OrdinalDate} (h_year : o₁.year = o₂.year) (h_day : o₁.day = o₂.day), o₁ = o₂
| ⟨y₁, d₁, hGt₁, hLt₁⟩, ⟨y₂, d₂, hGt₂, hLt₂⟩, hy, hd => by simp [hy, hd]

instance : Ord OrdinalDate where
  compare d₁ d₂ := 
    match Ord.compare d₁.year d₂.year with
    | Ordering.eq => Ord.compare d₁.day d₂.day 
    | owise => owise

instance : LE OrdinalDate := leOfOrd 
instance : LT OrdinalDate := ltOfOrd

theorem OrdinalDate.le_def (d₁ d₂ : OrdinalDate) : (d₁ <= d₂) = (compare d₁ d₂).isLE := rfl 
theorem OrdinalDate.lt_def (d₁ d₂ : OrdinalDate) : (d₁ < d₂) = (compare d₁ d₂ == Ordering.lt) := rfl 

theorem OrdinalDate.le_def' (d₁ d₂ : OrdinalDate) : 
  (d₁ <= d₂) ↔ (d₁.year < d₂.year ∨ (d₁.year = d₂.year ∧ d₁.day <= d₂.day)) := by
   simp [OrdinalDate.le_def, Ordering.isLE, compare, compareOfLessAndEq]
   match lt_trichotomy d₁.year d₂.year with
   | .inl y_lt => simp [y_lt]
   | .inr (.inr y_gt) => simp [not_lt_of_gt y_gt, ne_of_gt y_gt]
   | .inr (.inl y_eq) => 
     simp [y_eq, lt_irrefl]
     match lt_trichotomy d₁.day d₂.day with
     | .inl d_lt => simp [d_lt]; exact le_of_lt d_lt
     | .inr (.inr d_gt) => simp [not_lt_of_gt d_gt, ne_of_gt d_gt]; assumption
     | .inr (.inl d_eq) => simp [d_eq, lt_irrefl d₂.day]

theorem OrdinalDate.lt_def' (d₁ d₂ : OrdinalDate) : 
  (d₁ < d₂) = (d₁.year < d₂.year ∨ (d₁.year = d₂.year ∧ d₁.day < d₂.day)) := by
   simp [OrdinalDate.lt_def, compare, compareOfLessAndEq]
   match lt_trichotomy d₁.year d₂.year with
   | .inl y_lt => simp [y_lt]
   | .inr (.inr y_gt) => simp [not_lt_of_gt y_gt, ne_of_gt y_gt]
   | .inr (.inl y_eq) => 
     simp [y_eq, lt_irrefl]
     match lt_trichotomy d₁.day d₂.day with
     | .inl d_lt => simp [d_lt] 
     | .inr (.inr d_gt) => simp [not_lt_of_gt d_gt, ne_of_gt d_gt]
     | .inr (.inl d_eq) => simp [d_eq, lt_irrefl d₂.day]

instance : LinearOrder OrdinalDate where
  le_refl (a) := by simp [OrdinalDate.le_def']
  le_trans (a b c) := by 
    simp only [OrdinalDate.le_def']
    rintro (ay_lt_by | ⟨ay_eq_by, ad_le_bd⟩)
    <;> rintro (by_lt_cy | ⟨by_eq_cy, bd_le_cd⟩)
    . exact .inl $ lt_trans ay_lt_by by_lt_cy
    . exact .inl $ by_eq_cy ▸ ay_lt_by
    . exact .inl $ ay_eq_by ▸ by_lt_cy
    . exact .inr $ ⟨by_eq_cy ▸ ay_eq_by, le_trans ad_le_bd bd_le_cd⟩
  lt_iff_le_not_le (a b) := by
    simp only [OrdinalDate.le_def', OrdinalDate.lt_def']
    refine Iff.intro ?mp ?mpr    
    case mp =>
      rintro (y_lt | ⟨y_eq, d_lt⟩)
      case inl =>
        have hr : ¬(b.year < a.year ∨ b.year = a.year ∧ b.day ≤ a.day) := 
          fun
          | .inl y_lt' => absurd y_lt (lt_asymm y_lt')
          | .inr ⟨by_eq_ay, bd_le_ad⟩ => absurd (by_eq_ay ▸ y_lt : a.year < a.year) (lt_irrefl _)
        exact And.intro (Or.inl y_lt) hr
      case inr.intro =>
        have hr : ¬(b.year < a.year ∨ b.year = a.year ∧ b.day ≤ a.day) := 
          fun
          | .inl y_lt' => absurd (y_eq ▸ y_lt' : a.year < a.year) (lt_irrefl _)
          | .inr ⟨by_eq_ay, bd_le_ad⟩ => absurd bd_le_ad (not_le_of_gt d_lt)
        exact And.intro (Or.inr ⟨y_eq, le_of_lt d_lt⟩) hr
    case mpr =>
      rintro ⟨y_lt | ⟨y_eq, d_le⟩, hr⟩
      case intro.inl => exact Or.inl y_lt
      case intro.inr.intro =>
        refine .inr ⟨y_eq, ?x⟩
        match lt_or_eq_of_le d_le with
        | .inl d_lt => exact d_lt
        | .inr d_eq => exact False.elim <| hr <| Or.inr ⟨y_eq.symm, le_of_eq d_eq.symm⟩
  le_antisymm (a b) := by
    simp [OrdinalDate.le_def']
    rintro (ay_lt_by | ⟨ay_eq_by, ad_le_bd⟩)
    <;> rintro (by_lt_ay | ⟨by_eq_ay, bd_le_ad⟩)
    . exact absurd ay_lt_by (not_lt_of_gt by_lt_ay)
    . rw [by_eq_ay] at ay_lt_by; exact absurd (ay_lt_by) (lt_irrefl _)
    . rw [ay_eq_by] at by_lt_ay; exact absurd (by_lt_ay) (lt_irrefl _)
    . exact OrdinalDate.eq_of_val_eq ay_eq_by (le_antisymm ad_le_bd bd_le_ad)
  le_total (a b) := by
    simp [OrdinalDate.le_def']
    match lt_trichotomy a.year b.year with
    | .inl y_lt => simp [y_lt]
    | .inr (.inr y_gt) => simp [y_gt]
    | .inr (.inl y_eq) => 
      simp [y_eq, lt_irrefl]
      match lt_trichotomy a.day b.day with
      | .inl d_lt => simp [le_of_lt d_lt] 
      | .inr (.inr d_gt) => simp [le_of_lt d_gt]
      | .inr (.inl d_eq) => simp [d_eq]
  decidable_le := inferInstance
