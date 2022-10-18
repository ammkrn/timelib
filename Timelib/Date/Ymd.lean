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

open Lean

structure Ymd where
  year : Year
  month : Month
  day : Nat
  dayGe : day >= 1
  dayLe : day <= month.numDays year
deriving Repr

instance : ToJson Ymd where
  toJson ymd := Json.mkObj [("year", ToJson.toJson ymd.year.val), ("month", ToJson.toJson ymd.month), ("day", ymd.day)]

instance : FromJson Ymd where
  fromJson? j := do
    let (year : Year) ← (fromJson? (← j.getObjVal? "year")).map Year.mk
    let (month : Month) ← (fromJson? (← j.getObjVal? "month"))
    let (day : Nat) ← fromJson? (← j.getObjVal? "day")
    if h : day >= 1 ∧ day <= month.numDays year
    then return Ymd.mk year month day h.left h.right
    else Except.error s!"Ymd day out of range: {day}"

theorem Ymd.eq_of_val_eq : ∀ {o₁ o₂ : Ymd} (h_year : o₁.year = o₂.year) (h_month : o₁.month = o₂.month) (h_day : o₁.day = o₂.day), o₁ = o₂
| ⟨y₁, m₁, d₁, hGt₁, hLt₁⟩, ⟨y₂, m₂, d₂, hGt₂, hLt₂⟩, hy, hm, hd => by simp [hy, hm, hd]

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

theorem Ymd.le_def (d₁ d₂ : Ymd) : (d₁ <= d₂) = (compare d₁ d₂).isLE := rfl 
theorem Ymd.lt_def (d₁ d₂ : Ymd) : (d₁ < d₂) = (Ord.compare d₁ d₂ == Ordering.lt) := rfl 

theorem Ymd.le_def' (d₁ d₂ : Ymd) : 
  (d₁ <= d₂) = 
  (d₁.year < d₂.year ∨ (d₁.year = d₂.year ∧ d₁.month < d₂.month) ∨ (d₁.year = d₂.year ∧ d₁.month = d₂.month ∧ d₁.day <= d₂.day)) := by
   simp [Ymd.le_def, Ordering.isLE, compare, compareOfLessAndEq]
   match lt_trichotomy d₁.year d₂.year with
   | .inl y_lt => simp [y_lt]
   | .inr (.inr y_gt) => simp [not_lt_of_gt y_gt, ne_of_gt y_gt]
   | .inr (.inl y_eq) => 
     simp [y_eq, lt_irrefl]
     match lt_trichotomy d₁.month d₂.month with
     | .inl m_lt => simp [m_lt]
     | .inr (.inr m_gt) => simp [not_lt_of_gt m_gt, ne_of_gt m_gt]
     | .inr (.inl m_eq) => 
       simp [m_eq, lt_irrefl]
       match lt_trichotomy d₁.day d₂.day with
       | .inl d_lt => simp [d_lt]; exact le_of_lt d_lt
       | .inr (.inr d_gt) => simp [not_lt_of_gt d_gt, ne_of_gt d_gt]; assumption
       | .inr (.inl d_eq) => simp [d_eq, lt_irrefl d₂.day]

theorem Ymd.lt_def' (d₁ d₂ : Ymd) : 
  (d₁ < d₂) = 
  (d₁.year < d₂.year 
   ∨ (d₁.year = d₂.year ∧ d₁.month < d₂.month)
   ∨ (d₁.year = d₂.year ∧ d₁.month = d₂.month ∧ d₁.day < d₂.day)) := by
   simp [Ymd.lt_def, compare, compareOfLessAndEq]
   match lt_trichotomy d₁.year d₂.year with
   | .inl y_lt => simp [y_lt]
   | .inr (.inr y_gt) => simp [not_lt_of_gt y_gt, ne_of_gt y_gt]
   | .inr (.inl y_eq) => 
     simp [y_eq, lt_irrefl]
     match lt_trichotomy d₁.month d₂.month with
     | .inl m_lt => simp [m_lt]
     | .inr (.inr m_gt) => simp [not_lt_of_gt m_gt, ne_of_gt m_gt]
     | .inr (.inl m_eq) => 
       simp [m_eq, lt_irrefl]
       match lt_trichotomy d₁.day d₂.day with
       | .inl d_lt => simp [d_lt] 
       | .inr (.inr d_gt) => simp [not_lt_of_gt d_gt, ne_of_gt d_gt]
       | .inr (.inl d_eq) => simp [d_eq, lt_irrefl d₂.day]

instance : LinearOrder Ymd where
  le_refl (a) := by simp [Ymd.le_def']
  le_trans (a b c) := by 
    simp only [Ymd.le_def']
    rintro (ay_lt_by | ⟨ay_eq_by, am_lt_bm⟩ | ⟨ay_eq_by, am_eq_bm, ad_le_bd⟩)
    <;> rintro (by_lt_cy | ⟨by_eq_cy, bm_lt_cm⟩ | ⟨by_eq_cy, bm_eq_cm, bd_le_cd⟩)
    . exact .inl $ lt_trans ay_lt_by by_lt_cy
    . exact .inl $ by_eq_cy ▸ ay_lt_by
    . exact .inl $ by_eq_cy ▸ ay_lt_by
    . exact .inl $ ay_eq_by ▸ by_lt_cy
    . exact .inr $ .inl ⟨ay_eq_by ▸ by_eq_cy, lt_trans am_lt_bm bm_lt_cm⟩
    . exact .inr $ .inl ⟨ay_eq_by ▸ by_eq_cy, bm_eq_cm ▸ am_lt_bm⟩
    . exact .inl $ ay_eq_by ▸ by_lt_cy
    . exact .inr $ .inl ⟨ay_eq_by ▸ by_eq_cy, am_eq_bm ▸ bm_lt_cm⟩
    . exact .inr $ .inr ⟨ay_eq_by ▸ by_eq_cy, ⟨am_eq_bm ▸ bm_eq_cm, le_trans ad_le_bd bd_le_cd⟩⟩
  lt_iff_le_not_le (a b) := by
    simp only [Ymd.le_def', Ymd.lt_def']
    refine Iff.intro ?mp ?mpr    
    case mp =>
      rintro (y_lt | ⟨y_eq, m_lt⟩ | ⟨y_eq, m_eq, d_le⟩)
      case inl =>
        have hr : ¬(b.year < a.year ∨ b.year = a.year ∧ b.month < a.month ∨ b.year = a.year ∧ b.month = a.month ∧ b.day ≤ a.day) := by
          rintro (y_lt' | ⟨y_eq', m_lt'⟩ | ⟨y_eq', m_lt', d_le'⟩)           
          . exact (not_lt_of_gt y_lt) y_lt'
          . exact (lt_irrefl a.year (y_eq' ▸ y_lt))
          . exact (lt_irrefl a.year (y_eq' ▸ y_lt))
        exact ⟨Or.inl y_lt, hr⟩
      case inr.inl.intro =>
        have hr : ¬(b.year < a.year ∨ b.year = a.year ∧ b.month < a.month ∨ b.year = a.year ∧ b.month = a.month ∧ b.day ≤ a.day) := by
          rintro (y_lt' | ⟨y_eq', m_le⟩ | ⟨y_eq', m_eq', d_le'⟩)           
          . exact (lt_irrefl a.year (y_eq ▸ y_lt'))
          . exact (not_lt_of_gt m_lt) m_le
          . exact (lt_irrefl a.month (m_eq' ▸ m_lt))
        exact ⟨.inr $ .inl ⟨y_eq, m_lt⟩, hr⟩ 
      case inr.inr.intro.intro =>
        have hr : ¬(b.year < a.year ∨ b.year = a.year ∧ b.month < a.month ∨ b.year = a.year ∧ b.month = a.month ∧ b.day ≤ a.day) := by
          rintro (y_lt' | ⟨y_eq', m_lt⟩ | ⟨y_eq', m_eq, d_le'⟩)
          . exact (lt_irrefl a.year (y_eq ▸ y_lt'))
          . exact (lt_irrefl a.month (m_eq ▸ m_lt))
          . exact (not_le_of_gt d_le d_le')
        exact ⟨.inr $ .inr ⟨y_eq, ⟨m_eq, le_of_lt d_le⟩⟩, hr⟩
    case mpr =>
      rintro (y_lt | ⟨y_eq, m_lt⟩ | ⟨y_eq, m_eq, d_le⟩)
      case intro.inl => exact .inl y_lt
      case intro.inr.inl.intro => exact .inr $ .inl ⟨y_eq, m_lt⟩
      case intro.inr.inr.intro.intro hnot => 
        match lt_or_eq_of_le d_le with
        | .inl d_lt => exact Or.inr $ .inr ⟨y_eq, ⟨m_eq, d_lt⟩⟩
        | .inr d_eq => exact False.elim $ hnot $ .inr $ .inr ⟨y_eq.symm, ⟨m_eq.symm, (le_of_eq d_eq.symm)⟩⟩
  le_antisymm (a b) := by 
    simp [Ymd.le_def']
    rintro (ay_lt_by | ⟨ay_eq_by, am_lt_bm⟩ | ⟨ay_eq_by, am_eq_bm, ad_le_bd⟩) 
    <;> rintro (by_lt_ay | ⟨by_eq_ay, bm_lt_am⟩ | ⟨by_eq_ay, bm_eq_am, bd_le_ad⟩)
    . exact absurd ay_lt_by (not_lt_of_gt by_lt_ay)
    . rw [by_eq_ay] at ay_lt_by; exact absurd (ay_lt_by) (lt_irrefl _)
    . rw [by_eq_ay] at ay_lt_by; exact absurd (ay_lt_by) (lt_irrefl _)
    . rw [ay_eq_by] at by_lt_ay; exact absurd (by_lt_ay) (lt_irrefl _)
    . exact absurd am_lt_bm (not_lt_of_gt bm_lt_am)
    . rw [bm_eq_am] at am_lt_bm; exact absurd (am_lt_bm) (lt_irrefl _)
    . rw [ay_eq_by] at by_lt_ay; exact absurd (by_lt_ay) (lt_irrefl _)
    . rw [am_eq_bm] at bm_lt_am; exact absurd (bm_lt_am) (lt_irrefl _)
    . exact Ymd.eq_of_val_eq ay_eq_by am_eq_bm (le_antisymm ad_le_bd bd_le_ad)
  le_total (a b) := by
    simp [Ymd.le_def']
    match lt_trichotomy a.year b.year with
    | .inl y_lt => simp [y_lt]
    | .inr (.inr y_gt) => simp [y_gt]
    | .inr (.inl y_eq) => 
      simp [y_eq, lt_irrefl]
      match lt_trichotomy a.month b.month with
      | .inl m_lt => simp [m_lt] 
      | .inr (.inr m_gt) => simp [m_gt]
      | .inr (.inl m_eq) => 
        simp [m_eq, lt_irrefl]
        match lt_trichotomy a.day b.day with
        | .inl d_lt => simp [le_of_lt d_lt] 
        | .inr (.inr d_gt) => simp [le_of_lt d_gt]
        | .inr (.inl d_eq) => simp [d_eq]
  decidable_le := inferInstance

theorem Ymd.numDays_pos (ymd : Ymd) : 0 < ymd.month.numDays ymd.year := by
  simp only [Month.numDays]
  by_cases hy : ymd.year.isLeapYear <;> (split <;> simp [hy, if_true, if_false])

theorem Ymd.numDays_lt_numDaysInGregorianYear (ymd : Ymd) : ymd.month.numDays ymd.year < ymd.year.numDaysInGregorianYear := by
  simp only [Month.numDays, Year.numDaysInGregorianYear]
  by_cases hy : ymd.year.isLeapYear <;> (split <;> simp [hy, if_true, if_false])

theorem Ymd.numDays_lt_31 (ymd : Ymd) : ymd.month.numDays ymd.year <= 31 := by
  simp only [Month.numDays, Year.numDaysInGregorianYear]
  by_cases hy : ymd.year.isLeapYear <;> (split <;> simp [hy, if_true, if_false])
