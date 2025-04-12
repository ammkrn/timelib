import Timelib.Util
import Timelib.Date.Year
import Timelib.Date.Month
import Init.Data.RArray

namespace Timelib

/--
A date in the proleptic Gregorian calendar in ordinal form, which is a year,
and a day between 1 and 366.
-/
@[ext]
structure OrdinalDate where
  year : Year
  day : Nat
  hGe : day ≥ 1
  hLe : day ≤ year.numDaysInGregorianYear
deriving Repr

namespace OrdinalDate

theorem eq_of_val_eq : ∀ {o₁ o₂ : OrdinalDate} (_ : o₁.year = o₂.year) (_ : o₁.day = o₂.day), o₁ = o₂
| ⟨y₁, d₁, hGt₁, hLt₁⟩, ⟨y₂, d₂, hGt₂, hLt₂⟩, hy, hd => by simp [hy, hd]; exact
  { left := hy, right := hd }

instance : Ord OrdinalDate where
  compare d₁ d₂ :=
    match Ord.compare d₁.year d₂.year with
    | Ordering.eq => Ord.compare d₁.day d₂.day
    | owise => owise

instance : LE OrdinalDate := leOfOrd
instance : LT OrdinalDate := ltOfOrd

theorem le_def (d₁ d₂ : OrdinalDate) : (d₁ <= d₂) = (compare d₁ d₂).isLE := rfl
theorem lt_def (d₁ d₂ : OrdinalDate) : (d₁ < d₂) = (compare d₁ d₂ = Ordering.lt) := rfl

theorem le_def' (d₁ d₂ : OrdinalDate) :
  (d₁ <= d₂) = (d₁.year < d₂.year ∨ (d₁.year = d₂.year ∧ d₁.day <= d₂.day)) := by
   simp [OrdinalDate.le_def, Ordering.isLE, compare, compareOfLessAndEq]
   rcases Year.lt_trichotomy d₁.year d₂.year with inl | inr | inrinr
   . simp [inl]
   .
     have h0 : ¬(d₁.year < d₂.year) := by rw [inr]; exact Year.lt_irrefl d₂.year
     have h1 : ¬(d₁.year < d₁.year) := Year.lt_irrefl d₁.year
     have h2 : ¬(d₂.year < d₂.year) := Year.lt_irrefl d₂.year
     rcases Nat.lt_trichotomy d₁.day d₂.day with inl_ | inr_ | inrinr_
     . simp [h0, h1, h2, inr, inl_]; omega
     . simp [h0, h1, h2, inr, inr_]
     .
      have h3 : ¬d₁.day < d₂.day := by omega
      have h4 : d₂.day ≠ d₁.day := by omega
      simp [h0, h1, h2, inr, h3, h4.symm]
      assumption
   .
    have h00 : ¬d₁.year < d₂.year := Year.lt_asymm d₂.year d₁.year inrinr
    have h01 := Year.ne_of_lt d₂.year d₁.year inrinr
    simp [h00, h01.symm]

theorem lt_def' (d₁ d₂ : OrdinalDate) :
  (d₁ < d₂) = (d₁.year < d₂.year ∨ (d₁.year = d₂.year ∧ d₁.day < d₂.day)) := by
   simp [OrdinalDate.lt_def, compare, compareOfLessAndEq]
   rcases Year.lt_trichotomy d₁.year d₂.year with inl | inrinl | inrinr
   . simp [inl]
   .
     have h0 : ¬(d₁.year < d₂.year) := by rw [inrinl]; exact Year.lt_irrefl d₂.year
     have h1 : ¬(d₁.year < d₁.year) := Year.lt_irrefl d₁.year
     have h2 : ¬(d₂.year < d₂.year) := Year.lt_irrefl d₂.year
     rcases Nat.lt_trichotomy d₁.day d₂.day with inl_ | inr_ | inrinr_
     . simp [h0, h1, h2, inrinl, inl_]
     . simp [h0, h1, h2, inrinl, inr_]
     .
      have h3 : ¬d₁.day < d₂.day := by omega
      have h4 : d₂.day ≠ d₁.day := by omega
      simp [h0, h1, h2, inrinl, h3, h4.symm]
   .
    have h00 : ¬d₁.year < d₂.year := Year.lt_asymm d₂.year d₁.year inrinr
    have h01 := Year.ne_of_lt d₂.year d₁.year inrinr
    simp [h00, h01.symm]

theorem le_of_lt (d₁ d₂ : OrdinalDate) : d₁ < d₂ → d₁ <= d₂ := by
  simp only [le_def', lt_def'];
  rintro (hl | ⟨hr0, hr1⟩)
  exact .inl hl
  exact .inr ⟨hr0, by omega⟩


--instance : LinearOrder OrdinalDate where
--  le_refl (a) := by simp [OrdinalDate.le_def']
--  le_trans (a b c) := by
--    simp only [OrdinalDate.le_def']
--    rintro (ay_lt_by | ⟨ay_eq_by, ad_le_bd⟩)
--    <;> rintro (by_lt_cy | ⟨by_eq_cy, bd_le_cd⟩)
--    . exact .inl $ lt_trans ay_lt_by by_lt_cy
--    . exact .inl $ by_eq_cy ▸ ay_lt_by
--    . exact .inl $ ay_eq_by ▸ by_lt_cy
--    . exact .inr $ ⟨by_eq_cy ▸ ay_eq_by, le_trans ad_le_bd bd_le_cd⟩
--  lt_iff_le_not_le (a b) := by
--    simp only [OrdinalDate.le_def', OrdinalDate.lt_def']
--    refine Iff.intro ?mp ?mpr
--    case mp =>
--      rintro (y_lt | ⟨y_eq, d_lt⟩)
--      case inl =>
--        have hr : ¬(b.year < a.year ∨ b.year = a.year ∧ b.day ≤ a.day) :=
--          fun
--          | .inl y_lt' => absurd y_lt (lt_asymm y_lt')
--          | .inr ⟨by_eq_ay, bd_le_ad⟩ => absurd (by_eq_ay ▸ y_lt : a.year < a.year) (lt_irrefl _)
--        exact And.intro (Or.inl y_lt) hr
--      case inr.intro =>
--        have hr : ¬(b.year < a.year ∨ b.year = a.year ∧ b.day ≤ a.day) :=
--          fun
--          | .inl y_lt' => absurd (y_eq ▸ y_lt' : a.year < a.year) (lt_irrefl _)
--          | .inr ⟨by_eq_ay, bd_le_ad⟩ => absurd bd_le_ad (not_le_of_gt d_lt)
--        exact And.intro (Or.inr ⟨y_eq, le_of_lt d_lt⟩) hr
--    case mpr =>
--      rintro ⟨y_lt | ⟨y_eq, d_le⟩, hr⟩
--      case intro.inl => exact Or.inl y_lt
--      case intro.inr.intro =>
--        refine .inr ⟨y_eq, ?x⟩
--        match lt_or_eq_of_le d_le with
--        | .inl d_lt => exact d_lt
--        | .inr d_eq => exact False.elim <| hr <| Or.inr ⟨y_eq.symm, le_of_eq d_eq.symm⟩
--  le_antisymm (a b) := by
--    simp [OrdinalDate.le_def']
--    rintro (ay_lt_by | ⟨ay_eq_by, ad_le_bd⟩)
--    <;> rintro (by_lt_ay | ⟨by_eq_ay, bd_le_ad⟩)
--    . exact absurd ay_lt_by (not_lt_of_gt by_lt_ay)
--    . rw [by_eq_ay] at ay_lt_by; exact absurd (ay_lt_by) (lt_irrefl _)
--    . rw [ay_eq_by] at by_lt_ay; exact absurd (by_lt_ay) (lt_irrefl _)
--    . exact OrdinalDate.eq_of_val_eq ay_eq_by (le_antisymm ad_le_bd bd_le_ad)
--  le_total (a b) := by
--    simp [OrdinalDate.le_def']
--    match lt_trichotomy a.year b.year with
--    | .inl y_lt => simp [y_lt]
--    | .inr (.inr y_gt) => simp [y_gt]
--    | .inr (.inl y_eq) =>
--      simp [y_eq, lt_irrefl]
--      match lt_trichotomy a.day b.day with
--      | .inl d_lt => simp [le_of_lt d_lt]
--      | .inr (.inr d_gt) => simp [le_of_lt d_gt]
--      | .inr (.inl d_eq) => simp [d_eq]
--  decidableLE := inferInstance
--  compare_eq_compareOfLessAndEq := by sorry

theorem lt_trichotomy (y₁ y₂ : OrdinalDate) : (y₁ < y₂) ∨ y₁ = y₂ ∨ (y₂ < y₁) := by
  simp [lt_def']
  rcases Year.lt_trichotomy y₁.year y₂.year with a | b | c
  . exact .inl (.inl a)
  .
    rcases Nat.lt_trichotomy y₁.day y₂.day with x | y | z
    . exact .inl (.inr ⟨b, x⟩)
    . apply Or.inr (Or.inl _)
      have hE := OrdinalDate.mk.injEq y₁.year y₁.day y₁.hGe y₁.hLe y₂.year y₂.day y₂.hGe y₂.hLe
      exact hE ▸ ⟨b, y⟩
    . exact .inr (.inr (.inr ⟨b.symm, z⟩))
  . exact .inr (.inr (.inl c))

theorem lt_or_eq_of_le {d₁ d₂ : OrdinalDate} : d₁ <= d₂ → d₁ < d₂ ∨ d₁ = d₂ := by
  simp only [le_def', lt_def']
  intro h
  rcases h with hl | ⟨hr0, hr1⟩
  . exact .inl (.inl hl)
  . rcases Nat.eq_or_lt_of_le hr1 with hll | hrr
    .
      have hE := OrdinalDate.mk.injEq d₁.year d₁.day d₁.hGe d₁.hLe d₂.year d₂.day d₂.hGe d₂.hLe
      exact .inr (hE ▸ ⟨hr0, hll⟩)
    . exact .inl (.inr ⟨hr0, hrr⟩)

theorem lt_of_year_lt {d₁ d₂ : OrdinalDate} : d₁.year < d₂.year → d₁ < d₂ := by
  simp only [lt_def']; exact Or.inl

theorem lt_of_year_eq_of_day_lt {d₁ d₂ : OrdinalDate} : d₁.year = d₂.year → d₁.day < d₂.day → d₁ < d₂ :=  fun h0 h1 => by
  simp only [lt_def']; exact .inr ⟨h0, h1⟩

theorem le_total (a b : OrdinalDate) : a <= b ∨ b <= a := by
    simp [OrdinalDate.le_def']
    match Year.lt_trichotomy a.year b.year with
    | .inl y_lt => simp [y_lt]
    | .inr (.inr y_gt) => simp [y_gt]
    | .inr (.inl y_eq) =>
      simp only [y_eq, true_and]
      match Nat.lt_trichotomy a.day b.day with
      | .inl d_lt => omega
      | .inr (.inr d_gt) => omega
      | .inr (.inl d_eq) => omega

theorem le_refl (d : OrdinalDate) : d <= d := by
  simp only [le_def', Nat.le_refl, and_self, or_true]

open Month

@[simp]
abbrev isDayInMonth (d : OrdinalDate) (m : Month) := m.isDayOf d.year d.day

@[elab_as_elim]
def casesOn''''.{u}
      {motive : (d : OrdinalDate) → (m : Month) → d.isDayInMonth m → Sort u}
      (d : OrdinalDate)
      (m : Month)
      (h : d.isDayInMonth m)
      (minor : motive d m h)
      : motive d m h := minor

@[elab_as_elim]
def casesOn''.{u}
      {motive : OrdinalDate → Sort u}
      (major : OrdinalDate)
      (minor : ∀ (m : Month), major.isDayInMonth m → motive major)
      : motive major :=
  if h0 : major.day <= january.lastDayOf major.year
  then minor january ⟨by dsimp [lastDayOf, firstDayOf] at *; have _ := major.hGe; omega, ‹_›⟩
  else if h1 : major.day <= february.lastDayOf major.year
  then minor february ⟨by dsimp [lastDayOf, firstDayOf] at *; omega, ‹_›⟩
  else if h2 : major.day <= march.lastDayOf major.year
  then minor march ⟨by dsimp only [lastDayOf, firstDayOf] at *; omega, ‹_›⟩
  else if h3 : major.day <= april.lastDayOf major.year
  then minor april ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h4 : major.day <= may.lastDayOf major.year
  then minor may ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h5 : major.day <= june.lastDayOf major.year
  then minor june ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h6 : major.day <= july.lastDayOf major.year
  then minor july ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h7 : major.day <= august.lastDayOf major.year
  then minor august ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h8 : major.day <= september.lastDayOf major.year
  then minor september ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h9 : major.day <= october.lastDayOf major.year
  then minor october ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h10 : major.day <= november.lastDayOf major.year
  then minor november ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else
    minor december ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ((last_december_eq major.year ▸ major.hLe))⟩

theorem exists_isDayInMonth (d : OrdinalDate) : ∃ m, d.isDayInMonth m :=
  if h0 : d.day <= january.lastDayOf d.year
  then ⟨january, ⟨by dsimp only [lastDayOf, firstDayOf] at *; have _ := d.hGe; omega, ‹_›⟩⟩
  else if h1 : d.day <= february.lastDayOf d.year
  then ⟨february, ⟨by dsimp only [lastDayOf, firstDayOf] at *; omega, ‹_›⟩⟩
  else if h2 : d.day <= march.lastDayOf d.year
  then ⟨march, ⟨by dsimp only [lastDayOf, firstDayOf] at *; omega, ‹_›⟩⟩
  else if h3 : d.day <= april.lastDayOf d.year
  then ⟨april, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h4 : d.day <= may.lastDayOf d.year
  then ⟨may, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h5 : d.day <= june.lastDayOf d.year
  then ⟨june, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h6 : d.day <= july.lastDayOf d.year
  then ⟨july, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h7 : d.day <= august.lastDayOf d.year
  then ⟨august, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h8 : d.day <= september.lastDayOf d.year
  then ⟨september, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h9 : d.day <= october.lastDayOf d.year
  then ⟨october,⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h10 : d.day <= november.lastDayOf d.year
  then ⟨november, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else
    ⟨december, by dsimp only [firstDayOf, lastDayOf] at *; omega, ((last_december_eq d.year ▸ d.hLe))⟩


theorem isDayInMonth_unique_r (d : OrdinalDate) : (m : Month) → d.isDayInMonth m → ∀ (m' : Month), d.isDayInMonth m' → m = m' := by
  intro m hm m' hm'
  cases m using Month.casesOn'
  all_goals
  (
    cases m' using Month.casesOn'
    all_goals (
      first
      | (simp [isDayInMonth, isDayOf] at *; omega; done)
      | (rfl; done)
    )
  )

theorem isDayInMonth_unique (d : OrdinalDate) : ∃ (m : Month), d.isDayInMonth m ∧ ∀ (m' : Month), d.isDayInMonth m' → m = m' :=
  have ⟨m, hm⟩ := d.exists_isDayInMonth
  Exists.intro m ⟨hm, isDayInMonth_unique_r d m hm⟩

def curMonth (d : OrdinalDate) : { m // d.isDayInMonth m } :=
  if h0 : d.day <= january.lastDayOf d.year
  then ⟨january, ⟨by dsimp only [lastDayOf, firstDayOf] at *; have _ := d.hGe; omega, ‹_›⟩⟩
  else if h1 : d.day <= february.lastDayOf d.year
  then ⟨february, ⟨by dsimp only [lastDayOf, firstDayOf] at *; omega, ‹_›⟩⟩
  else if h2 : d.day <= march.lastDayOf d.year
  then ⟨march, ⟨by dsimp only [lastDayOf, firstDayOf] at *; omega, ‹_›⟩⟩
  else if h3 : d.day <= april.lastDayOf d.year
  then ⟨april, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h4 : d.day <= may.lastDayOf d.year
  then ⟨may, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h5 : d.day <= june.lastDayOf d.year
  then ⟨june, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h6 : d.day <= july.lastDayOf d.year
  then ⟨july, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h7 : d.day <= august.lastDayOf d.year
  then ⟨august, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h8 : d.day <= september.lastDayOf d.year
  then ⟨september, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h9 : d.day <= october.lastDayOf d.year
  then ⟨october,⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else if h10 : d.day <= november.lastDayOf d.year
  then ⟨november, ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩⟩
  else
    ⟨december, by dsimp only [firstDayOf, lastDayOf] at *; omega, ((last_december_eq d.year ▸ d.hLe))⟩

@[elab_as_elim]
def casesOn'.{u}
      {motive : OrdinalDate → Sort u}
      (d : OrdinalDate)
      (h_jan : d.isDayInMonth january → motive d)
      (h_feb : d.isDayInMonth february → motive d)
      (h_mar : d.isDayInMonth march → motive d)
      (h_apr : d.isDayInMonth april → motive d)
      (h_may : d.isDayInMonth may       → motive d)
      (h_jun : d.isDayInMonth june    → motive d)
      (h_jul : d.isDayInMonth july    → motive d)
      (h_aug : d.isDayInMonth august  → motive d)
      (h_sep : d.isDayInMonth september → motive d)
      (h_oct : d.isDayInMonth october → motive d)
      (h_nov : d.isDayInMonth november → motive d)
      (h_dec : d.isDayInMonth december → motive d)
      : motive d :=
  if h0 : d.day <= january.lastDayOf d.year
  then h_jan ⟨by dsimp only [lastDayOf, firstDayOf] at *; have _ := d.hGe; omega, ‹_›⟩
  else if h1 : d.day <= february.lastDayOf d.year
  then h_feb ⟨by dsimp only [lastDayOf, firstDayOf] at *; omega, ‹_›⟩
  else if h2 : d.day <= march.lastDayOf d.year
  then h_mar ⟨by dsimp only [lastDayOf, firstDayOf] at *; omega, ‹_›⟩
  else if h3 : d.day <= april.lastDayOf d.year
  then h_apr ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h4 : d.day <= may.lastDayOf d.year
  then h_may ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h5 : d.day <= june.lastDayOf d.year
  then h_jun ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h6 : d.day <= july.lastDayOf d.year
  then h_jul ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h7 : d.day <= august.lastDayOf d.year
  then h_aug ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h8 : d.day <= september.lastDayOf d.year
  then h_sep ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h9 : d.day <= october.lastDayOf d.year
  then h_oct ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else if h10 : d.day <= november.lastDayOf d.year
  then h_nov ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ‹_›⟩
  else
    h_dec ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, ((last_december_eq d.year ▸ d.hLe))⟩

theorem day_le_366 (d : OrdinalDate) : d.day ≤ 366 :=
  Nat.le_trans d.hLe d.year.num_days_in_gregorian_year_le_366

theorem day_le_365 (d : OrdinalDate) : ¬d.year.isLeapYear → d.day ≤ 365 := by
  intro h; exact (d.year.num_days_in_gregorial_year_eq_365 h) ▸ d.hLe

theorem isLeapYear_of_day_eq_366 (d : OrdinalDate) : d.day = 366 → d.year.isLeapYear :=
  fun h =>
    if ht : d.year.isLeapYear
    then ht
    else by
      have h2 := d.hLe
      simp [Year.numDaysInGregorianYear, ht] at h2
      omega
