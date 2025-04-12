import Timelib.Date.Year
import Timelib.Date.Month
import Timelib.Date.Scalar
import Timelib.Date.Ordinal
import Timelib.Date.Ymd
import Timelib.Util
import Timelib.Date.Convert

private theorem eq_or_lt_of_le {a b : Int} : a <= b → a = b ∨ a < b := by omega

theorem rearrange00 (p : Int) {r : Int} (_ : 0 <= r) : (p * 36524 + r) % 36524 = r % 36524  := by
  omega

theorem rearrange1 (p : Int) {r : Int} (_ : r < 146097) (_ : 0 <= r) :
  (p * 146097 + r) % 146097 = r  := by
  omega
theorem rearrange2 (p : Int) {r : Int} (_ : r < 146097) (_ : 0 <= r) :
  (p * 146097 + r) % 146097 % 36524 % 1461 = r % 36524  % 1461 := by
  omega

theorem rearrange4 (p : Int) {r : Int} (_ : r < 36524) (_ : 0 <= r) :
  (p * 36524 + r) % 36524 = r := by
  omega

theorem mul_add_emod_self (p : Int) {r X : Int} (zero_le : 0 <= r) (hlt : r < X) : (p * X + r) % X = r :=
  calc
    (p * X + r) % X = (r + (p * X)) % X := by rw [Int.add_comm]
    _ = r % X := by rw [Int.add_mul_emod_self]
    _ = r := by rw [Int.emod_eq_of_lt zero_le hlt]

theorem mul_add_div_self_left (p : Int) {X r : Int} :
  r < X → 1 < X → 0 <= r → (p * X + r) / X = p := fun _ _ _ =>
  have h := Int.add_mul_ediv_left (a := r) (b := X) (c := p) (by omega)
  have h' := Int.ediv_eq_zero_of_lt (a := r) (b := X) (by omega) (by omega)
  calc
    (p * X + r) / X = (r + X * p) / X := by rw [Int.add_comm, Int.mul_comm]
    _ = r / X + p := by rw [h]
    _ = p := by rw [h', Int.zero_add]

private theorem congr_r_4 (a b c d e x y z w : Int) :
  ((b + c + d + e) <= (x + y + z + w)) → (a + b + c + d + e) <= (a + x + y + z + w) := by
  omega

private theorem congr_r_3 (a b c d x y z : Int) :
  ((b + c + d ) <= (x + y + z)) → (a + b + c + d) <= (a + x + y + z) := by
  omega

private theorem congr_r_2 (a b c x y : Int) :
  ((b + c) <= (x + y)) → (a + b + c) <= (a + x + y) := by
  omega

namespace Timelib
open Month

theorem case1 (d₁ d₂ : OrdinalDate) :
  (d₁.year.val - 1) / 400 < (d₂.year.val - 1) / 400
  → d₁.toScalarDate ≤ d₂.toScalarDate := fun h0 => by
  simp only [OrdinalDate.toScalarDate, ScalarDate.le_def, ge_iff_le]
  have _ : d₁.day <= 366 := d₁.day_le_366
  have _ : d₂.day <= 366 := d₂.day_le_366

  generalize h_a : (d₁.1.val - 1) / 400 = a
  generalize h_b : (d₂.1.val - 1) / 400 = b

  generalize h_c :
    ((d₁.1.val - 1) % 400 / 100 * 36524 + (d₁.1.val - 1) % 100 / 4 * 1461 +
    (d₁.1.val - 1) % 4 * 365 + ↑d₁.day) = c
  generalize h_d :
    ((d₂.1.val - 1) % 400 / 100 * 36524 + (d₂.1.val - 1) % 100 / 4 * 1461 +
    (d₂.1.val - 1) % 4 * 365 + ↑d₂.day) = d


  have h_eq_left' : a * 146097 + (d₁.1.val - 1) % 400 / 100 * 36524 +
    (d₁.1.val - 1) % 100 / 4 * 1461 + (d₁.1.val -1) % 4 * 365 +
    ↑d₁.day = a * 146097 + c := by omega
  have h_eq_right' : b * 146097 + (d₂.1.val - 1) % 400 / 100 * 36524 +
    (d₂.1.val - 1) % 100 / 4 * 1461 + (d₂.1.val - 1) % 4 * 365 +
    ↑d₂.day = b * 146097 + d := by omega
  rw [h_eq_left', h_eq_right']
  exact conv_helper1 a b c d 146097 (h_a ▸ h_b ▸ h0) (by omega) (show 1 < 146097 by decide) (have _ := d₂.hGe; by omega)


theorem case2 (d₁ d₂ : OrdinalDate) :
  (d₁.year.val - 1) / 400 = (d₂.year.val - 1) / 400
  → (d₁.year.val - 1) % 400 / 100 < (d₂.year.val - 1) % 400 / 100
  → d₁.toScalarDate ≤ d₂.toScalarDate := fun heq hlt => by
  dsimp only [OrdinalDate.toScalarDate, ScalarDate.le_def, ge_iff_le]
  rw [heq]
  apply congr_r_4
  have _ : d₁.day <= 366 := d₁.day_le_366
  have _ : d₂.day <= 366 := d₂.day_le_366

  generalize h_a : (d₁.1.val - 1) % 400 / 100 = a
  generalize h_b : (d₂.1.val - 1) % 400 / 100 = b
  generalize h_c : ((d₁.1.val - 1) % 100 / 4 * 1461 + (d₁.1.val - 1) % 4 * 365 + ↑d₁.day) = c
  generalize h_d : ((d₂.1.val - 1) % 100 / 4 * 1461 + (d₂.1.val - 1) % 4 * 365 + ↑d₂.day) = d

  have h_eq_left' : a * 36524 + (d₁.1.val - 1) % 100 / 4 * 1461 +
    (d₁.1.val -1) % 4 * 365 + ↑d₁.day = a * 36524 + c := by omega
  have h_eq_right' : b * 36524 + (d₂.1.val - 1) % 100 / 4 * 1461 +
    (d₂.1.val - 1) % 4 * 365 + ↑d₂.day = b * 36524 + d := by omega
  have hconv1 := conv_helper1 a b c d 36524 (h_a ▸ h_b ▸ hlt) (by omega) (by omega) (by have _ := d₂.hGe; omega)
  rw [h_eq_left', h_eq_right']
  exact hconv1

theorem case3 (d₁ d₂ : OrdinalDate) :
  (d₁.year.val - 1) / 400 = (d₂.year.val - 1) / 400
  → (d₁.year.val - 1) % 400 / 100 = (d₂.year.val - 1) % 400 / 100
  → (d₁.1.val - 1) % 100 / 4 < (d₂.1.val - 1) % 100 / 4

  → d₁.toScalarDate ≤ d₂.toScalarDate := fun heq heq' hlt => by
  have _ : d₁.day <= 366 := d₁.day_le_366
  have _ : d₂.day <= 366 := d₂.day_le_366
  dsimp only [OrdinalDate.toScalarDate, ScalarDate.le_def, ge_iff_le]
  rw [heq]
  apply congr_r_4
  rw [heq']
  apply congr_r_3
  generalize h_a : (d₁.1.val - 1) % 100 / 4 = a
  generalize h_b : (d₂.1.val - 1) % 100 / 4 = b
  generalize h_c : ((d₁.1.val - 1) % 4 * 365 + ↑d₁.day) = c
  generalize h_d : ((d₂.1.val - 1) % 4 * 365 + ↑d₂.day) = d
  have _ : c <= 1461 := by omega
  have _ := conv_helper1 a b c d 1461 (h_a ▸ h_b ▸ hlt) (by omega) (show 1 < 1461 by decide) (have _ := d₂.hGe; by omega)
  omega

theorem case4 (d₁ d₂ : OrdinalDate) :
  (d₁.year.val - 1) / 400 = (d₂.year.val - 1) / 400
  → (d₁.year.val - 1) % 400 / 100 = (d₂.year.val - 1) % 400 / 100
  → (d₁.1.val - 1) % 100 / 4 = (d₂.1.val - 1) % 100 / 4
  → (d₁.year.val - 1) % 4 < (d₂.year.val - 1) % 4
  → d₁.toScalarDate ≤ d₂.toScalarDate := fun heq heq' heq'' hlt => by
  dsimp only [OrdinalDate.toScalarDate, ScalarDate.le_def, ge_iff_le]
  rw [heq]
  apply congr_r_4
  rw [heq']
  apply congr_r_3
  rw [heq'']
  apply congr_r_2
  have _ : d₁.day <= 366 := d₁.day_le_366
  have _ : d₂.day <= 366 := d₂.day_le_366
  have _ : d₁.day >= 1 := d₁.hGe
  have _ : d₂.day >= 1 := d₂.hGe
  generalize h_a : (d₁.1.val - 1) % 4 = a
  generalize h_b : (d₂.1.val - 1) % 4 = b
  omega

theorem OrdinalDate.toScalarDate_mono (d₁ d₂ : OrdinalDate) :
 d₁ <= d₂ → d₁.toScalarDate <= d₂.toScalarDate := by
  intro hle
  cases lt_or_eq_of_le hle with
  | inr heq => exact heq ▸ d₂.toScalarDate.le_refl
  | inl hlt =>
    rw [lt_def', Year.lt_def] at hlt
    simp [ScalarDate.le_def]
    dsimp [toScalarDate]
    rcases hlt with yearLt | ⟨yearsEq, dayLe⟩
    -- The day1 < day2 case
    case inl.inr.intro =>
      rw [Year.val_eq_of_eq yearsEq]
      apply Int.add_le_add_left
      omega
      done
    case inl.inl =>
      have yearLt' : d₁.1.val < d₂.1.val := yearLt
      have day₁Le := d₁.hLe
      have day₂Le := d₂.hLe
      have h0 := Int.lt_trichotomy ((d₁.1.val - 1) / 400) ((d₂.1.val - 1) / 400)
      rcases h0 with l | m | r
      . exact case1 d₁ d₂ l
      .
        have h1 := Int.lt_trichotomy ((d₁.1.val - 1) % 400 / 100) ((d₂.1.val - 1) % 400 / 100)
        rcases h1 with l | m' | r
        . exact case2 d₁ d₂ m l
        .
          have h2 := Int.lt_trichotomy ((d₁.1.val - 1) % 100 / 4) ((d₂.1.val - 1) % 100 / 4)
          rcases h2 with l | m'' | r
          . exact case3 d₁ d₂ m m' l
          .
            have h3 := Int.lt_trichotomy ((d₁.1.val - 1) % 4) ((d₂.1.val - 1) % 4)
            rcases h3 with l | m''' | r
            . exact case4 d₁ d₂ m m' m'' l
            . rw [m]; omega
            . omega
          . omega
        . omega
      . omega


-- yeah this is the problem one; if it's a leap year in that category that makes 400.

theorem case2_ {d₁ d₂ : ScalarDate} :
 (d₁.day - 1) / 146097 = (d₂.day - 1) / 146097
 → (d₁.day - 1) % 146097 / 36524 < (d₂.day - 1) % 146097 / 36524
 → d₁.toOrdinalDate <= d₂.toOrdinalDate
 := by
  dsimp only [ScalarDate.toOrdinalDate]
  intro h0 h1
  simp only [h0]
  by_cases hleap₁ : (d₁.day - 1) % 146097 / 36524 = 4 ∨ (d₁.day - 1) % 146097 % 36524 % 1461 / 365 = 4
  case pos =>
    apply OrdinalDate.le_of_lt; apply OrdinalDate.lt_of_year_lt; simp [Year.lt_def]
    omega
  case neg =>
    simp only [hleap₁, ↓reduceIte]
    by_cases hleap₂ : (d₂.day - 1) % 146097 / 36524 = 4 ∨ (d₂.day - 1) % 146097 % 36524 % 1461 / 365 = 4
    case pos =>
      simp only [hleap₂, ↓reduceIte, Int.add_zero, Int.reduceToNat]
      have hh : ((d₂.day - 1) / 146097 * 400 + (d₁.day - 1) % 146097 / 36524 * 100 +
        (d₁.day - 1) % 146097 % 36524 / 1461 * 4 +
        (d₁.day - 1) % 146097 % 36524 % 1461 / 365 + 1) ≤
        ((d₂.day - 1) / 146097 * 400 + (d₂.day - 1) % 146097 / 36524 * 100 +
        (d₂.day - 1) % 146097 % 36524 / 1461 * 4 + (d₂.day - 1) % 146097 % 36524 % 1461 / 365) := by
        omega
      match eq_or_lt_of_le hh with
      | .inl hl =>
        apply OrdinalDate.le_of_lt; refine OrdinalDate.lt_of_year_eq_of_day_lt ?hyear ?hday
        case hyear => simp; exact hl
        case hday => simp; omega
      | .inr hlt =>
        apply OrdinalDate.le_of_lt; apply OrdinalDate.lt_of_year_lt; simp only [Year.lt_def]; omega
    case neg =>
      apply OrdinalDate.le_of_lt; apply OrdinalDate.lt_of_year_lt; simp only [Year.lt_def]
      omega

theorem case3_ {d₁ d₂ : ScalarDate} :
  ((d₁.day - 1) / 146097 = (d₂.day - 1) / 146097)
  → ((d₁.day - 1) % 146097 / 36524 = (d₂.day - 1) % 146097 / 36524)
  → ((d₁.day - 1) % 146097 % 36524 / 1461 < (d₂.day - 1) % 146097 % 36524 / 1461)
  → d₁.toOrdinalDate <= d₂.toOrdinalDate := by
  dsimp only [ScalarDate.toOrdinalDate]
  intro h0 h1 h2
  simp only [h0, h1]
  apply OrdinalDate.le_of_lt; apply OrdinalDate.lt_of_year_lt; simp [Year.lt_def]
  omega

theorem case4_ {d₁ d₂ : ScalarDate} :
  ((d₁.day - 1) / 146097 = (d₂.day - 1) / 146097)
  → ((d₁.day - 1) % 146097 / 36524 = (d₂.day - 1) % 146097 / 36524)
  → ((d₁.day - 1) % 146097 % 36524 / 1461 = (d₂.day - 1) % 146097 % 36524 / 1461)
  → ((d₁.day - 1) % 146097 % 36524 % 1461 / 365 < (d₂.day - 1) % 146097 % 36524 % 1461 / 365)
  → d₁.toOrdinalDate <= d₂.toOrdinalDate := by
  dsimp only [ScalarDate.toOrdinalDate]
  intro h0 h1 h2 h3
  simp only [h0, h1, h2]
  by_cases hleap₁ : (d₂.day - 1) % 146097 / 36524 = 4 ∨ (d₁.day - 1) % 146097 % 36524 % 1461 / 365 = 4
  case pos =>
    apply OrdinalDate.le_of_lt
    apply OrdinalDate.lt_of_year_lt
    simp only [hleap₁, ↓reduceIte, Int.add_zero, Year.lt_def]
    omega
  case neg =>
    by_cases hleap₂ : (d₂.day - 1) % 146097 / 36524 = 4 ∨ (d₂.day - 1) % 146097 % 36524 % 1461 / 365 = 4
    case pos =>
      simp [hleap₁, hleap₂]
      have hh : ((d₂.day - 1) / 146097 * 400 + (d₂.day - 1) % 146097 / 36524 * 100 +
        (d₂.day - 1) % 146097 % 36524 / 1461 * 4 +
        (d₁.day - 1) % 146097 % 36524 % 1461 / 365 + 1) ≤ ((d₂.day - 1) / 146097 * 400 +
        (d₂.day - 1) % 146097 / 36524 * 100 + (d₂.day - 1) % 146097 % 36524 / 1461 * 4 +
        (d₂.day - 1) % 146097 % 36524 % 1461 / 365) := by omega
      match eq_or_lt_of_le hh with
      | .inl hl =>
        apply OrdinalDate.le_of_lt; refine OrdinalDate.lt_of_year_eq_of_day_lt ?hyear ?hday
        case hyear => simp only [Year.mk.injEq]; exact hl
        case hday => simp only; omega
      | .inr hlt =>
        apply OrdinalDate.le_of_lt; apply OrdinalDate.lt_of_year_lt; simp [Year.lt_def]; omega
    case neg =>
      apply OrdinalDate.le_of_lt
      apply OrdinalDate.lt_of_year_lt
      simp only [hleap₂, ↓reduceIte, Year.lt_def]
      omega


theorem ScalarDate.toOrdinalDate_mono (d₁ d₂ : ScalarDate) : d₁ ≤ d₂ → d₁.toOrdinalDate ≤ d₂.toOrdinalDate := by
  intro hle
  cases lt_or_eq_of_le hle with
  | inr heq => exact heq ▸ d₂.toOrdinalDate.le_refl
  | inl hlt =>
    rw [lt_def] at hlt
    rw [le_def] at hle
    dsimp [toOrdinalDate]
    have h0 := Int.lt_trichotomy ((d₁.day - 1) / 146097) ((d₂.day - 1) / 146097)
    have h1 := Int.lt_trichotomy ((d₁.day - 1) % 146097 / 36524) ((d₂.day - 1) % 146097 / 36524)
    have h2 := Int.lt_trichotomy
      ((d₁.day - 1) % 146097 % 36524 / 1461)
      ((d₂.day - 1) % 146097 % 36524 / 1461)
    have h3 := Int.lt_trichotomy
      ((d₁.day - 1) % 146097 % 36524 % 1461 / 365)
      ((d₂.day - 1) % 146097 % 36524 % 1461 / 365)
    rcases h0 with l | m0 | r
    .
      apply OrdinalDate.le_of_lt
      apply OrdinalDate.lt_of_year_lt
      simp only [Year.lt_def]
      omega
    .
      rcases h1 with l | m1 | r
      . exact case2_ m0 l
      .
        rcases h2 with l | m2 | r
        . exact case3_ m0 m1 l
        .
          rcases h3 with l | m3 | r
          . exact case4_ m0 m1 m2 l
          .
            simp only [m0, m1, m2, m3, ge_iff_le]
            apply OrdinalDate.le_of_lt
            exact OrdinalDate.lt_of_year_eq_of_day_lt (by simp only [m1]) (by simp only [m1]; omega)
          . omega
        . omega
      . omega
    . omega



namespace ScalarDate

@[simp]
abbrev num400YearGroups (d : ScalarDate) : Int := (d.day - 1) / 146097

@[simp]
abbrev hundredGroupDays (d : ScalarDate) : Int := (d.day - 1) % 146097

@[simp]
abbrev numSingleYears (d : ScalarDate) : Int := ((d.hundredGroupDays % 36524) % 1461) / 365

@[simp]
abbrev num100YearGroups (d : ScalarDate) : Int := d.hundredGroupDays / 36524

@[simp]
abbrev fourGroupDays (d : ScalarDate) : Int := d.hundredGroupDays % 36524

@[simp]
abbrev num4YearGroups (d : ScalarDate) : Int := d.fourGroupDays / 1461

theorem direction1_s_case1 {d : ScalarDate} (h : d.numSingleYears  = 4) :
  d.toOrdinalDate.toScalarDate = d := by
  have _ : d.num100YearGroups <= 3 ∧ 0 <= d.num100YearGroups := by
    dsimp [num100YearGroups, numSingleYears] at *
    omega
  have _ : d.num4YearGroups <= 23 ∧ 0 <= d.num4YearGroups := by
    dsimp [num4YearGroups, numSingleYears, num100YearGroups] at *
    omega

  simp only [OrdinalDate.toScalarDate, toOrdinalDate, h, or_true, ↓reduceIte, Int.add_zero,
    Int.reduceToNat]
  apply congrArg
  generalize hk : (d.num400YearGroups * 400 + d.num100YearGroups * 100 + d.num4YearGroups * 4 + 4 - 1) = k
  have goal_sum_part0 : (k / 400) = ((d.num400YearGroups * 400) / 400) := by
    dsimp only [num400YearGroups] at *
    omega
  have goal_sum_part1 : ((k % 400) / 100) = ((d.num100YearGroups * 100) / 100) := by
    dsimp only [num100YearGroups, num4YearGroups, num400YearGroups] at *
    omega
  simp only [goal_sum_part0, num400YearGroups, ne_eq, Int.reduceEq, not_false_eq_true,
    Int.mul_ediv_cancel, goal_sum_part1, num100YearGroups, hundredGroupDays]
  dsimp only [numSingleYears, num400YearGroups, num100YearGroups,
    num4YearGroups, hundredGroupDays, fourGroupDays] at *
  omega

theorem direction1_s_case2 {d : ScalarDate} :
  d.num100YearGroups ≠ 4 →
  d.numSingleYears ≠ 4 →
  d.toOrdinalDate.toScalarDate = d := fun hne4 hne4' => by
      have hlt4 : d.numSingleYears < 4 := by dsimp [numSingleYears] at *; omega
      have hge0 : d.numSingleYears >= 0 := by dsimp [numSingleYears]; omega
      have hlt4' : d.num100YearGroups < 4 := by dsimp [numSingleYears] at *; omega
      have hge0' : d.num100YearGroups >= 0 := by dsimp [num100YearGroups] at *; omega
      simp only [OrdinalDate.toScalarDate, toOrdinalDate, hne4, hne4', or_self, ↓reduceIte,
        Int.add_sub_cancel, Int.ofNat_toNat]
      apply congrArg
      generalize hjk : (d.num400YearGroups * 400 + d.num100YearGroups * 100 + d.num4YearGroups * 4 +
              d.numSingleYears) = jk
      have goal_sum_part0 : (jk / 400) = (((d.day - 1) / 146097 * 400) / 400) := by
        dsimp [num100YearGroups, num4YearGroups] at *
        omega
      have goal_sum_part1 : ((jk % 400) / 100) = ((d.num100YearGroups * 100) / 100) := by
        dsimp [num100YearGroups] at *
        omega
      have h02 : (jk % 100) = d.num4YearGroups * 4 + d.numSingleYears := by
        dsimp [numSingleYears] at *
        omega
      have goal_sum_part2 : ((jk % 100) / 4) = ((d.num4YearGroups * 4) / 4) := by
        rw [h02]
        omega
      rw [goal_sum_part0, goal_sum_part1, goal_sum_part2]
      dsimp [num100YearGroups, num4YearGroups, numSingleYears] at *
      omega

theorem toOrdinalDate_toScalarDate_inv (d : ScalarDate) : d.toOrdinalDate.toScalarDate = d :=
  if h0 : d.num100YearGroups = 4
  then by
      dsimp only [ScalarDate.toOrdinalDate, OrdinalDate.toScalarDate]
      dsimp only [num100YearGroups, hundredGroupDays] at h0
      apply congrArg
      omega
  else if h1 : d.numSingleYears = 4
  then direction1_s_case1 h1
  else direction1_s_case2 h0 h1


end ScalarDate

theorem OrdinalDate.yearconv400_lem (d : OrdinalDate) :
  ((d.1.val - 1) % 400 / 100 * 36524 + (d.1.val - 1) % 100 / 4 * 1461 +
    (d.1.val - 1) % 4 * 365 + ↑d.day - 1) < 146097 := by
  have _ : d.day <= 366 := d.day_le_366
  omega

theorem OrdinalDate.yearconv400_lem' (d : OrdinalDate) :
  0 ≤ ((d.1.val - 1) % 400 / 100 * 36524 + (d.1.val - 1) % 100 / 4 * 1461 +
    (d.1.val - 1) % 4 * 365 + ↑d.day - 1) := by
  have _ : d.day <= 366 := d.day_le_366; have _ := d.hGe; omega

theorem OrdinalDate.yearconv400 (d : OrdinalDate) :
((d.1.val - 1) / 400 * 146097 + (d.1.val - 1) % 400 / 100 * 36524 +
  (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 +
    ↑d.day - 1) / 146097 = ((d.1.val - 1) / 400) := by
  have _ := div_mul_add_eq_of
    ((d.1.val - 1) / 400) d.yearconv400_lem (by decide) d.yearconv400_lem'
  omega

theorem OrdinalDate.yearconv100_part0_ (d : OrdinalDate) :
  ((d.1.val - 1) / 400 * 146097 + (d.1.val - 1) % 400 / 100 * 36524 +
    (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 +
      ↑d.day - 1) % 146097 =
  (((d.1.val - 1) % 400 / 100 * 36524 + (d.1.val - 1) % 100 / 4 * 1461 +
    (d.1.val - 1) % 4 * 365 + ↑d.day - 1)) := by
  have h0 := rearrange1 ((d.1.val - 1) / 400) d.yearconv400_lem d.yearconv400_lem'
  omega

theorem OrdinalDate.yearconv4_part0
  {d : OrdinalDate}
  (_ : (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + ↑d.day - 1 < 36524) :
    ((d.1.val - 1) / 400 * 146097 + (d.1.val - 1) % 400 / 100 * 36524 +
      (d.1.val - 1) % 100 / 4 * 1461 +
        (d.1.val - 1) % 4 * 365 + ↑d.day - 1) % 146097 % 36524 =
  (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + ↑d.day - 1 := by
  have _ := rearrange4 ((d.year.val - 1) % 400 / 100) ‹_› (have _ := d.hGe; by omega)
  rw [yearconv100_part0_]
  omega

theorem ScalarDate.toOrdinalDate_lastDay_lemma (d : ScalarDate) :
  d.toOrdinalDate.day = 366 ↔ d.num100YearGroups = 4 ∨ d.numSingleYears = 4 := by
  refine Iff.intro ?mp ?mpr
  case mp => dsimp [ScalarDate.toOrdinalDate]; omega
  case mpr => dsimp [ScalarDate.toOrdinalDate]; omega


theorem OrdinalDate.toScalarDate_ne_366 {d : OrdinalDate} :
  d.day = 366 → d.toScalarDate.num100YearGroups = 4 ∨ d.toScalarDate.numSingleYears = 4 := by
  intro day_eq_366
  have _ := d.hGe
  have _ := d.day_le_366
  have h_leap : d.year.isLeapYear := d.isLeapYear_of_day_eq_366 day_eq_366

  dsimp [ScalarDate.num100YearGroups, ScalarDate.numSingleYears, toScalarDate] at day_eq_366 |-
  dsimp [Year.isLeapYear] at h_leap

  have hrassoc0 :
    ((d.1.val - 1) / 400 * 146097 + (d.1.val - 1) % 400 / 100 * 36524 +
    (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + 366 - 1) % 146097 =
    ((d.1.val - 1) / 400 * 146097 + ((d.1.val - 1) % 400 / 100 * 36524 +
    (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + 366 - 1)) % 146097 := by
    omega
  have hrw1 :
    ((d.1.val - 1) / 400 * 146097 + ((d.1.val - 1) % 400 / 100 * 36524 +
    (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + 366 - 1)) % 146097 =
    (((d.1.val - 1) / 400 * 146097) % 146097 + ((d.1.val - 1) % 400 / 100 * 36524 +
    (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + 366 - 1)) % 146097 := by
    rw [← Int.emod_add_emod]
  have hrassoc1 :
    ((d.year.val - 1) % 400 / 100 * 36524 + (d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1) =
    ((d.year.val - 1) % 400 / 100 * 36524 + ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1)) :=
    by omega
  have hrw5 :
    ((d.year.val - 1) % 400 / 100 * 36524 + ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1)) % 146097 =
    ((d.year.val - 1) % 400 / 100 * 36524 + ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1)) := by
    have hrassoc : ((d.year.val - 1) % 400 / 100 * 36524 +
      ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1)) =
      ((d.year.val - 1) % 400 / 100 * 36524 + (((d.year.val - 1) % 100 / 4 * 1461 +
      (d.year.val - 1) % 4 * 365 + 366 - 1))) := by omega
    rw [hrassoc]; omega
  have hemod :
    ((d.year.val - 1) % 400 / 100 * 36524 + ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1)) % 36524 =
    ((d.year.val - 1) % 400 / 100 * 36524 % 36524 + ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1)) % 36524 := by
    rw [← Int.emod_add_emod]
  rw [day_eq_366]
  simp [hrassoc0]
  rw [hrw1]
  rw [hrassoc1]
  simp [hrw5]
  simp [hemod]

  have hle : (((d.year.val - 1) % 100 / 4 * 1461 +
    (d.year.val - 1) % 4 * 365 + 366 - 1)) ≤ 36524 := by omega
  match eq_or_lt_of_le hle with
  | .inl hl =>
    apply Or.inl
    rw [hl]
    omega
  | .inr hr =>
    have h_of_lt :
      ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1) % 36524 =
      ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1) := by omega
    have _ : ((d.year.val - 1) % 4 * 365 + 366 - 1) < 1461 := by omega
    have hrassoc2 :
      ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1) =
      ((d.year.val - 1) % 100 / 4 * 1461 + ((d.year.val - 1) % 4 * 365 + 366 - 1)) := by omega
    apply Or.inr
    have h' :
      ((d.year.val - 1) % 4 * 365 + 366 - 1) % 1461 =
      ((d.year.val - 1) % 4 * 365 + 366 - 1) := by omega
    rw [h_of_lt, hrassoc2, ← Int.emod_add_emod]
    simp [h']
    omega

theorem OrdinalDate.toScalarDate_last_ (d : OrdinalDate) : d.toScalarDate.num100YearGroups = 4 ∨ d.toScalarDate.numSingleYears = 4 → d.day = 366
  | .inl hl => by
    have _ := d.hGe
    have _ := d.day_le_366
    dsimp [toScalarDate] at hl
    have _ : ((d.1.val - 1) / 400 * 146097 + ((d.1.val - 1) % 400 / 100 * 36524 +
      (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + ↑d.day - 1)) % 146097 =
      (d.1.val - 1) % 400 / 100 * 36524 + (d.1.val - 1) % 100 / 4 * 1461 +
      (d.1.val - 1) % 4 * 365 + ↑d.day - 1 := rearrange1 ((d.1.val - 1) / 400) (by omega) (by omega)
    have hy : ((d.1.val - 1) / 400 * 146097 + (d.1.val - 1) % 400 / 100 * 36524 +
      (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + ↑d.day - 1) % 146097 =
      (d.1.val - 1) % 400 / 100 * 36524 + (d.1.val - 1) % 100 / 4 * 1461 +
      (d.1.val - 1) % 4 * 365 + ↑d.day - 1 := by omega
    have _ := hy ▸ hl
    have _ : ((d.year.val) - 1) % 400 / 100 <= 3 := by omega
    have _ : ((d.year.val - 1) % 400 / 100 * 36524 + (d.year.val - 1) % 100 / 4 * 1461 +
      (d.year.val - 1) % 4 * 365 + ↑d.day - 1) >= 36524 := by omega
    omega



  | .inr hr => by
    dsimp [toScalarDate] at *
    have _ := d.hGe
    have _ := d.day_le_366
    have _ : ((d.1.val - 1) / 400 * 146097 + ((d.1.val - 1) % 400 / 100 * 36524 +
      (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + ↑d.day - 1)) % 146097 =
      (d.1.val - 1) % 400 / 100 * 36524 + (d.1.val - 1) % 100 / 4 * 1461 +
      (d.1.val - 1) % 4 * 365 + ↑d.day - 1 := rearrange1 ((d.1.val - 1) / 400) (by omega) (by omega)
    have hy : ((d.1.val - 1) / 400 * 146097 + (d.1.val - 1) % 400 / 100 * 36524 +
      (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + ↑d.day - 1) % 146097 =
      (d.1.val - 1) % 400 / 100 * 36524 + (d.1.val - 1) % 100 / 4 * 1461 +
      (d.1.val - 1) % 4 * 365 + ↑d.day - 1 := by omega
    have _ : ((d.year.val) - 1) % 400 / 100 <= 3 := by omega

    have hrearr := rearrange00 (r := ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1)) ((d.year.val - 1) % 400 / 100) (by

      have hj : ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1)= ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + (↑d.day - 1)):= by omega
      have hk : forall {a b c : Int}, 0 <= a → 0 <= b → 0 <= c → 0 <= a + b + c := by omega
      exact hj ▸ (hk (by omega) (by omega) (by omega))

    )
    have hassoc : ((d.year.val - 1) % 400 / 100 * 36524 + (d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1) = ((d.year.val - 1) % 400 / 100 * 36524 + ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1)) := by omega
    have hmax : (99 : Int) / 4 * 1461 + (3 : Int) * 365 + 366 - 1 = 36524 := rfl
    have hll : (d.year.val - 1) % 100 / 4 * 1461 <= 35064 := by omega

    have hlt : ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1) <= 36524 := by omega
    match eq_or_lt_of_le hlt with
    | .inl hl =>
      have _ := hl ▸ hrearr ▸ hassoc ▸ hy ▸ hr
      omega
    | .inr hr' =>
      have hrw : ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1) % 36524 = ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1) :=
        Int.emod_eq_of_lt (by omega) hr'
      have hr' := hrw ▸ hrearr ▸ hassoc ▸ hy ▸ hr
      have _ : ((d.year.val - 1) % 100 / 4 * 1461) < 36524 := by omega
      have _ : ((d.year.val - 1) % 4 * 365 + ↑d.day - 1) % 1461 / 365 = 4 := by omega
      have _ : ((d.year.val - 1) % 4 * 365 + ↑d.day - 1) < 1461 := by omega
      have hrassoc_ : ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1)
        = ((d.year.val - 1) % 100 / 4 * 1461 + ((d.year.val - 1) % 4 * 365 + ↑d.day - 1)) := by omega
      have hmodmod : ((d.year.val - 1) % 100 / 4 * 1461 + ((d.year.val - 1) % 4 * 365 + ↑d.day - 1)) % 1461
        = ((d.year.val - 1) % 100 / 4 * 1461 % 1461 + ((d.year.val - 1) % 4 * 365 + ↑d.day - 1)) % 1461 := by
        rw [← Int.emod_add_emod]
      simp at hmodmod
      have _ := hmodmod ▸ hrassoc_ ▸ hr'
      omega

theorem hlt (d : OrdinalDate) : ((d.1.val - 1) % 400 / 100 * 36524 + (d.1.val - 1) % 100 / 4 * 1461 +
            (d.1.val - 1) % 4 * 365 +
          ↑d.day -
        1) < 146097 := by
  have _ := d.hGe
  have _ := d.day_le_366
  omega

theorem hzero_le (d : OrdinalDate) : 0 <= ((d.1.val - 1) % 400 / 100 * 36524 + (d.1.val - 1) % 100 / 4 * 1461 +
            (d.1.val - 1) % 4 * 365 +
          ↑d.day -
        1) := by
  have _ := d.hGe
  have _ := d.day_le_366
  omega

theorem mod_4_eq_zero_of_numSingleYears {d : OrdinalDate} : d.toScalarDate.numSingleYears = 4 → d.year.val % 4 = 0 := fun h => by
  have h_is_leap := d.toScalarDate_last_ (.inr h)
  have h2 := d.isLeapYear_of_day_eq_366 h_is_leap
  dsimp [Year.isLeapYear] at h2
  omega

theorem mod_4_eq_zero_of_num100YearGroups {d : OrdinalDate} : d.toScalarDate.num100YearGroups = 4 → d.year.val % 4 = 0 := fun h => by
  have h_is_leap := d.toScalarDate_last_ (.inl h)
  have h2 := d.isLeapYear_of_day_eq_366 h_is_leap
  dsimp [Year.isLeapYear] at h2
  omega

theorem mod_400_eq_zero (d : OrdinalDate) : d.toScalarDate.num100YearGroups = 4 → d.year.val % 400 = 0 := fun h => by
  have heq := d.toScalarDate_last_ (.inl h)
  have _ := mod_4_eq_zero_of_num100YearGroups h
  simp [OrdinalDate.toScalarDate, ScalarDate.num100YearGroups] at h
  simp [heq] at h

  have hrassoc : ((d.1.val - 1) / 400 * 146097 + (d.1.val - 1) % 400 / 100 * 36524 +
    (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + 366 - 1) =
    ((d.1.val - 1) / 400 * 146097 + ((d.1.val - 1) % 400 / 100 * 36524 +
    (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + 366 - 1)) := by omega
  rw [hrassoc] at h
  have hx : ((d.year.val - 1) / 400 * 146097 + ((d.year.val - 1) % 400 / 100 * 36524 +
    (d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1)) % 146097 =
    (((d.year.val - 1) % 400 / 100 * 36524 + (d.year.val - 1) % 100 / 4 * 1461 +
    (d.year.val - 1) % 4 * 365 + 366 - 1)) :=
    mul_add_emod_self ((d.year.val - 1) / 400) (by omega) (by omega)
  simp [hx] at h
  have hrassoc2 : ((d.year.val - 1) % 400 / 100 * 36524 +
    (d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1) =
    ((d.year.val - 1) % 400 / 100 * 36524 + ((d.year.val - 1) % 100 / 4 * 1461 +
    (d.year.val - 1) % 4 * 365 + 366 - 1)) := by omega
  simp [hrassoc2] at h
  have hle : ((d.year.val - 1) % 100 / 4 * 1461 +
    (d.year.val - 1) % 4 * 365 + 366 - 1) ≤ 36524 := by omega
  match eq_or_lt_of_le hle with
  | .inl heq =>
    rw [heq] at h
    omega
  | .inr hlt =>
    have hdiv : ((d.year.val - 1) % 400 / 100 * 36524 +
      ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1)) / 36524 =
      ((d.year.val - 1) % 400 / 100) :=
    mul_add_div_self_left ((d.year.val - 1) % 400 / 100) hlt (by omega) (by omega)
    rw [hdiv] at h
    omega

theorem mod_100_ne_zero {d : OrdinalDate} : d.toScalarDate.numSingleYears = 4 → d.year.val % 100 ≠ 0 :=  by
  intro h hf
  have heq := d.toScalarDate_last_ (.inr h)
  have _ := mod_4_eq_zero_of_numSingleYears h
  have hrassoc : ((d.1.val - 1) / 400 * 146097 + (d.1.val - 1) % 400 / 100 * 36524 +
    (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + 366 - 1) =
    ((d.1.val - 1) / 400 * 146097 + ((d.1.val - 1) % 400 / 100 * 36524 +
    (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + 366 - 1)) := by omega
  have hx : ((d.year.val - 1) / 400 * 146097 + ((d.year.val - 1) % 400 / 100 * 36524 +
    (d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1)) % 146097 =
    (((d.year.val - 1) % 400 / 100 * 36524 + (d.year.val - 1) % 100 / 4 * 1461 +
    (d.year.val - 1) % 4 * 365 + 366 - 1)) :=
    mul_add_emod_self ((d.year.val - 1) / 400) (by omega) (by omega)
  have hrassoc2 : ((d.year.val - 1) % 400 / 100 * 36524 +
    (d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + 366 - 1) =
    ((d.year.val - 1) % 400 / 100 * 36524 + ((d.year.val - 1) % 100 / 4 * 1461 +
    (d.year.val - 1) % 4 * 365 + 366 - 1)) := by omega
  simp [heq, OrdinalDate.toScalarDate, ScalarDate.num100YearGroups] at h
  rw [hrassoc] at h
  simp [hx] at h
  simp [hrassoc2] at h
  omega

theorem case_0_ (d : OrdinalDate) : d.toScalarDate.num100YearGroups = 4 → d.toScalarDate.toOrdinalDate = d := by
  have _ := d.hGe
  have _ := d.day_le_366

  -- I'm pretty sure it's going to have to come out of this.
  intro h
  dsimp only [ScalarDate.num100YearGroups, ScalarDate.hundredGroupDays, OrdinalDate.toScalarDate, ScalarDate.toOrdinalDate] at *
  simp [h]
  simp [OrdinalDate.yearconv400]
  simp [OrdinalDate.yearconv100_part0_]

  refine OrdinalDate.eq_of_val_eq ?ofyear ?ofday
  case ofyear =>
    apply Year.eq_of_val_eq
    simp
    have hrassoc0 : ((d.year.val - 1) % 400 / 100 * 36524 + (d.year.val - 1) % 100 / 4 * 1461 +
      (d.year.val - 1) % 4 * 365 + ↑d.day - 1) % 36524 =
      ((d.year.val - 1) % 400 / 100 * 36524 + ((d.year.val - 1) % 100 / 4 * 1461 +
      (d.year.val - 1) % 4 * 365 + ↑d.day - 1)) % 36524 := by omega
    have hrw0 : ((d.year.val - 1) % 400 / 100 * 36524 + ((d.year.val - 1) % 100 / 4 * 1461 +
      (d.year.val - 1) % 4 * 365 + ↑d.day - 1)) % 36524 =
      ((d.year.val - 1) % 400 / 100 * 36524 % 36524 + ((d.year.val - 1) % 100 / 4 * 1461 +
      (d.year.val - 1) % 4 * 365 + ↑d.day - 1)) % 36524 := by rw [← Int.emod_add_emod]
    have hrw0_ := rearrange00
      (p := (d.year.val - 1) % 400 / 100 )
      (r := ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1))
      (by omega)
    rw [hrassoc0]
    rw [hrw0_]
    have hle : ((d.year.val - 1) % 100 / 4 * 1461 +
      (d.year.val - 1) % 4 * 365 + ↑d.day - 1) ≤ 36524 := by omega
    have h00 : (d.year.val - 1) / 400 * 400 = d.year.val - 400 →
      (d.year.val - 1) / 400 * 400 + 400 = d.year.val := by omega

    have hrassoc2 : ((d.1.val - 1) / 400 * 146097 + (d.1.val - 1) % 400 / 100 * 36524 +
      (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + ↑d.day - 1) =
      ((d.1.val - 1) / 400 * 146097 + ((d.1.val - 1) % 400 / 100 * 36524 +
      (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + ↑d.day - 1)) := by omega
    have h000 := mul_add_emod_self ((d.1.val - 1) / 400) (X := 146097) (hzero_le d) (hlt d)
    have h001 := h000 ▸ hrassoc2 ▸ h
    have mod_eq_zero : d.year.val % 400 = 0 := mod_400_eq_zero d h
    have lem {a : Int} (_ : a % 400 = 0): (a - 1) / 400 * 400 + 400 = a / 400 * 400 := by
      omega
    have lem_app := lem mod_eq_zero
    have finisher := Int.ediv_mul_cancel_of_emod_eq_zero mod_eq_zero

    match eq_or_lt_of_le hle with
    | .inl heq =>
      simp [heq]
      rw [lem_app]
      exact finisher


    | .inr hlt =>
      have hz : ((d.year.val - 1) % 100 / 4 * 1461 +
        (d.year.val - 1) % 4 * 365 + ↑d.day - 1) % 36524 = 0 := by omega
      simp [hz]
      rw [lem_app]
      exact finisher
  case ofday =>
    simp
    exact (d.toScalarDate_last_ (.inl h)).symm


theorem case_1_ (d : OrdinalDate) : d.toScalarDate.numSingleYears = 4 → d.toScalarDate.toOrdinalDate = d := by
  have _ := d.hGe

  intro h0
  have _ : ¬d.year.val % 100 = 0 := mod_100_ne_zero h0

  have h_day_eq := d.toScalarDate_last_ (.inr h0)

  have h_is_leap := d.isLeapYear_of_day_eq_366 h_day_eq
  simp [Year.isLeapYear] at h_is_leap

  have h1 : d.toScalarDate.num100YearGroups <= 3 ∧ 0 <= d.toScalarDate.num100YearGroups := by
    dsimp [ScalarDate.num100YearGroups, ScalarDate.numSingleYears] at *
    omega

  have h2 : d.toScalarDate.num100YearGroups ≠ 4 := by omega
  dsimp only [ScalarDate.numSingleYears, ScalarDate.num100YearGroups, ScalarDate.hundredGroupDays, OrdinalDate.toScalarDate, ScalarDate.toOrdinalDate] at *

  simp [h2, h0]
  simp [OrdinalDate.yearconv400]
  simp [OrdinalDate.yearconv100_part0_]

  refine OrdinalDate.eq_of_val_eq ?ofyear ?ofday
  case ofyear =>
    apply Year.eq_of_val_eq
    simp
    have hrassoc0 : ((d.year.val - 1) % 400 / 100 * 36524 +
      (d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1) % 36524 =
      ((d.year.val - 1) % 400 / 100 * 36524 + ((d.year.val - 1) % 100 / 4 * 1461 +
      (d.year.val - 1) % 4 * 365 + ↑d.day - 1)) % 36524 := by omega
    have hrw0 : ((d.year.val - 1) % 400 / 100 * 36524 +
      ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1)) % 36524 =
      ((d.year.val - 1) % 400 / 100 * 36524 % 36524 + ((d.year.val - 1) % 100 / 4 * 1461 +
      (d.year.val - 1) % 4 * 365 + ↑d.day - 1)) % 36524 := by rw [← Int.emod_add_emod]
    have hrw0_ := rearrange00
      (p := (d.year.val - 1) % 400 / 100 )
      (r := ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1))
      (by omega)
    rw [hrassoc0]
    rw [hrw0_]
    have hle : ((d.year.val - 1) % 100 / 4 * 1461 +
      (d.year.val - 1) % 4 * 365 + ↑d.day - 1) ≤ 36524 := by omega
    have hrassoc2 : ((d.year.val - 1) % 400 / 100 * 36524 + (d.year.val - 1) % 100 / 4 * 1461 +
      (d.year.val - 1) % 4 * 365 + ↑d.day - 1) = ((d.year.val - 1) % 400 / 100 * 36524 +
      ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1)) := by omega
    simp [hrassoc2]
    have hmod4 := mod_4_eq_zero_of_numSingleYears h0
    have _ : (d.year.val - 1) % 4 ≠ 0 := by omega


    match eq_or_lt_of_le hle with
    | .inl heq =>

      simp [heq]
      simp [h_day_eq] at *
      have lem0 (a : Int) : (a * 36524 + 36524) / 36524 = a + 1 := by omega
      have hqq := lem0 ((d.year.val - 1) % 400 / 100)
      simp [hqq]
      omega

    | .inr hlt =>
      have hx : ((d.year.val - 1) % 400 / 100 * 36524 + ((d.year.val - 1) % 100 / 4 * 1461 +
        (d.year.val - 1) % 4 * 365 + ↑d.day - 1)) / 36524 = (d.year.val - 1) % 400 / 100 :=
        mul_add_div_self_left ((d.year.val - 1) % 400 / 100) hlt (by decide) (by omega)
      simp [hx]
      simp [h_day_eq] at *
      omega

  case ofday =>
    simp
    -- There should be a lemma for this one somewhere I think.
    exact (d.toScalarDate_last_ (.inr h0)).symm



theorem case_2_ (d : OrdinalDate) :
  d.toScalarDate.num100YearGroups ≠ 4
  → d.toScalarDate.numSingleYears ≠ 4
  → d.toScalarDate.toOrdinalDate = d := by
  have _ := d.hGe
  have hle := d.day_le_366
  -- From the fact that it's not the last day of a leap year.

  intro h0 h1
  have _ : d.day ≠ 366 := fun hf =>
    match OrdinalDate.toScalarDate_ne_366 hf with
    | .inl hl => h0 hl
    | .inr hr => h1 hr

  dsimp only [ScalarDate.numSingleYears, ScalarDate.num100YearGroups, ScalarDate.hundredGroupDays, OrdinalDate.toScalarDate, ScalarDate.toOrdinalDate] at *
  simp [h0, h1]
  have hlt : (d.1.val - 1) % 100 / 4 * 1461 + (d.1.val - 1) % 4 * 365 + ↑d.day - 1 < 36524 := by omega
  have hx := OrdinalDate.yearconv4_part0 hlt
  simp [hx]
  simp [OrdinalDate.yearconv100_part0_]
  simp [OrdinalDate.yearconv400]
  have h001 : ((d.year.val - 1) % 4 * 365 + ↑d.day - 1) < 1461 := by omega
  have h_rearr1 : ((((d.year.val - 1) % 100 / 4 * 1461 +
    ((d.year.val - 1) % 4 * 365 + ↑d.day - 1)) )) % 1461 =
    (((d.year.val - 1) % 4 * 365 + ↑d.day - 1) )  := by
    omega
  have heq1 : ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 + ↑d.day - 1) % 1461 =
    (((d.year.val - 1) % 100 / 4 * 1461 + ((d.year.val - 1) % 4 * 365 + ↑d.day - 1))) % 1461 := by omega
  simp [heq1]
  simp [h_rearr1]

  have h002 : (↑d.day - 1) < 365 := by omega
  have h_rearr2 : ((d.year.val - 1) % 4 * 365 + ↑d.day - 1) % 365 =  ↑d.day - 1  := by
    omega
  simp [h_rearr2]


  refine OrdinalDate.eq_of_val_eq ?ofyear ?ofday
  case ofyear =>
    apply Year.eq_of_val_eq
    simp
    have h0xxx : ((d.year.val - 1) % 100 / 4 * 1461 + (d.year.val - 1) % 4 * 365 +
      ↑d.day - 1) / 1461 = (d.year.val - 1) % 100 / 4 := by
      have _ := div_mul_add_eq_of
        ((d.year.val - 1) % 100 / 4)
        (by assumption)
        (show 1 < 1461 by decide)
        (by omega)
      omega
    have h1xxx : ((d.year.val - 1) % 400 / 100 * 36524 + (d.year.val - 1) % 100 / 4 * 1461 +
      (d.year.val - 1) % 4 * 365 + ↑d.day - 1) / 36524 = (d.year.val - 1) % 400 / 100 := by
      have _ := div_mul_add_eq_of
        ((d.year.val - 1) % 400 / 100)
        (by assumption)
        (show 1 < 36524 by decide)
        (by omega)
      omega
    simp [h0xxx]
    simp [h1xxx]
    have xyz : ((d.year.val - 1) % 4 * 365 + ↑d.day - 1) / 365 = ((d.year.val - 1) % 4) := by
      have _ : ((d.year.val - 1) % 4 * 365 + (↑d.day - 1)) / 365 = ((d.year.val - 1) % 4) :=
        div_mul_add_eq_of
          ((d.year.val - 1) % 4) (by omega) (show 1 < 365 by decide) (have _ := d.hGe; by omega)
      omega
    simp [xyz]

    have hrw (a b : Int) : a = b-1 → a+1 = b := by omega
    apply hrw
    have hassoc : (d.year.val - 1) / 400 * 400 + (d.year.val - 1) % 400 / 100 * 100 +
      (d.year.val - 1) % 100 / 4 * 4 + (d.year.val - 1) % 4 =
      (d.year.val - 1) / 400 * 400 + ((d.year.val - 1) % 400 / 100 * 100 +
      ((d.year.val - 1) % 100 / 4 * 4 + (d.year.val - 1) % 4)) := by omega
    rw [hassoc]

    have hdvd0 := Int.emod_emod_of_dvd (n := d.1.val - 1) (m := 4) (k := 100) (by omega)
    rw [← hdvd0]
    have hmod0 := Int.ediv_add_emod'  ((d.year.val - 1) % 100) 4
    rw [hmod0]
    have hdvd1 := Int.emod_emod_of_dvd (n := d.1.val - 1) (m := 100) (k := 400) (by omega)
    rw [← hdvd1]
    have hmod1 := Int.ediv_add_emod'  ((d.year.val - 1) % 400) 100
    rw [hmod1]
    have hmod2 := Int.ediv_add_emod'  (d.year.val - 1) 400
    exact hmod2

  case ofday =>
    simp
    done


namespace OrdinalDate

theorem toScalarDate_toOrdinalDate_inv (d : OrdinalDate) : d.toScalarDate.toOrdinalDate = d :=
  if h0 : d.toScalarDate.num100YearGroups = 4
  then case_0_ d h0
  else if h1 : d.toScalarDate.numSingleYears = 4
  then case_1_ d h1
  else case_2_ d h0 h1

theorem toYmd_cases (d : OrdinalDate) :
  (d.isDayInMonth january ∧ d.toYmd.year = d.year ∧ d.toYmd.month = january ∧ d.toYmd.day = d.day)
  ∨ (d.isDayInMonth february ∧ d.toYmd.year = d.year ∧ d.toYmd.month = february ∧ d.toYmd.day = d.day - (january.lastDayOf d.year))
  ∨ (d.isDayInMonth march ∧ d.toYmd.year = d.year ∧ d.toYmd.month = march ∧ d.toYmd.day = d.day - (february.lastDayOf d.year))
  ∨ (d.isDayInMonth april ∧ d.toYmd.year = d.year ∧ d.toYmd.month = april ∧ d.toYmd.day = d.day - (march.lastDayOf d.year))
  ∨ (d.isDayInMonth may ∧ d.toYmd.year = d.year ∧ d.toYmd.month = may ∧ d.toYmd.day = d.day - (april.lastDayOf d.year))
  ∨ (d.isDayInMonth june ∧ d.toYmd.year = d.year ∧ d.toYmd.month = june ∧ d.toYmd.day = d.day - (may.lastDayOf d.year))
  ∨ (d.isDayInMonth july ∧ d.toYmd.year = d.year ∧ d.toYmd.month = july ∧ d.toYmd.day = d.day - (june.lastDayOf d.year))
  ∨ (d.isDayInMonth august ∧ d.toYmd.year = d.year ∧ d.toYmd.month = august ∧ d.toYmd.day = d.day - (july.lastDayOf d.year))
  ∨ (d.isDayInMonth september ∧ d.toYmd.year = d.year ∧ d.toYmd.month = september ∧ d.toYmd.day = d.day - (august.lastDayOf d.year))
  ∨ (d.isDayInMonth october ∧ d.toYmd.year = d.year ∧ d.toYmd.month = october ∧ d.toYmd.day = d.day - (september.lastDayOf d.year))
  ∨ (d.isDayInMonth november ∧ d.toYmd.year = d.year ∧ d.toYmd.month = november ∧ d.toYmd.day = d.day - (october.lastDayOf d.year))
  ∨ (d.isDayInMonth december ∧ d.toYmd.year = d.year ∧ d.toYmd.month = december ∧ d.toYmd.day = d.day - (november.lastDayOf d.year))
  :=
  if _ : d.day <= january.lastDayOf d.year
  then by
    simp [toYmd, *]; exact d.hGe
  else if _ : d.day <= february.lastDayOf d.year
  then by
    simp [toYmd, *]; dsimp only [lastDayOf, firstDayOf] at *; omega
  else if _ : d.day <= march.lastDayOf d.year
  then by
    simp [toYmd, *]; dsimp only [lastDayOf, firstDayOf] at *; omega
  else if _ : d.day <= april.lastDayOf d.year
  then by
    simp [toYmd, *]; dsimp only [lastDayOf, firstDayOf] at *; omega
  else if _ : d.day <= may.lastDayOf d.year
  then by
    simp [toYmd, *]; dsimp only [lastDayOf, firstDayOf] at *; omega
  else if _ : d.day <= june.lastDayOf d.year
  then by
    simp [toYmd, *]; dsimp only [lastDayOf, firstDayOf] at *; omega
  else if _ : d.day <= july.lastDayOf d.year
  then by
    simp [toYmd, *]; dsimp only [lastDayOf, firstDayOf] at *; omega
  else if _ : d.day <= august.lastDayOf d.year
  then by
    simp [toYmd, *]; dsimp only [lastDayOf, firstDayOf] at *; omega
  else if _ : d.day <= september.lastDayOf d.year
  then by
    simp [toYmd, *]; dsimp only [lastDayOf, firstDayOf] at *; omega
  else if _ : d.day <= october.lastDayOf d.year
  then by
    simp [toYmd, *]; dsimp only [lastDayOf, firstDayOf] at *; omega
  else if _ : d.day <= november.lastDayOf d.year
  then by
    simp [toYmd, *]; dsimp only [lastDayOf, firstDayOf] at *; omega
  else by
    simp [toYmd, *]
    exact ⟨by dsimp only [firstDayOf, lastDayOf] at *; omega, d.hLe⟩

end OrdinalDate

namespace Ymd

--@[simp]
theorem toOrdinalDate_year_eq (ymd : Ymd) : (ymd.toOrdinalDate).year = ymd.year := by
  simp [toOrdinalDate]; split <;> simp

def toOrdinalDate_eq_disj (ymd : Ymd) :
  (ymd.month = january ∧ ymd.toOrdinalDate.year = ymd.year ∧ ymd.toOrdinalDate.day = ymd.day)
  ∨ (ymd.month = february ∧ ymd.toOrdinalDate.year = ymd.year ∧ ymd.toOrdinalDate.day = ymd.day + january.lastDayOf ymd.year)
  ∨ (ymd.month = march ∧ ymd.toOrdinalDate.year = ymd.year ∧ ymd.toOrdinalDate.day = ymd.day + february.lastDayOf ymd.year)
  ∨ (ymd.month = april ∧ ymd.toOrdinalDate.year = ymd.year ∧ ymd.toOrdinalDate.day = ymd.day + march.lastDayOf ymd.year)
  ∨ (ymd.month = may ∧ ymd.toOrdinalDate.year = ymd.year ∧ ymd.toOrdinalDate.day = ymd.day + april.lastDayOf ymd.year)
  ∨ (ymd.month = june ∧ ymd.toOrdinalDate.year = ymd.year ∧ ymd.toOrdinalDate.day = ymd.day + may.lastDayOf ymd.year)
  ∨ (ymd.month = july ∧ ymd.toOrdinalDate.year = ymd.year ∧ ymd.toOrdinalDate.day = ymd.day + june.lastDayOf ymd.year)
  ∨ (ymd.month = august ∧ ymd.toOrdinalDate.year = ymd.year ∧ ymd.toOrdinalDate.day = ymd.day + july.lastDayOf ymd.year)
  ∨ (ymd.month = september ∧ ymd.toOrdinalDate.year = ymd.year ∧ ymd.toOrdinalDate.day = ymd.day + august.lastDayOf ymd.year)
  ∨ (ymd.month = october ∧ ymd.toOrdinalDate.year = ymd.year ∧ ymd.toOrdinalDate.day = ymd.day + september.lastDayOf ymd.year)
  ∨ (ymd.month = november ∧ ymd.toOrdinalDate.year = ymd.year ∧ ymd.toOrdinalDate.day = ymd.day + october.lastDayOf ymd.year)
  ∨ (ymd.month = december ∧ ymd.toOrdinalDate.year = ymd.year ∧ ymd.toOrdinalDate.day = ymd.day + november.lastDayOf ymd.year)
  := by
  dsimp only [Ymd.toOrdinalDate]; split <;> simp [*]

end Ymd

namespace OrdinalDate
theorem toYmd_year_eq (d : OrdinalDate) : d.toYmd.year = d.year := by
  rcases d.toYmd_cases with
  h | h | h | h | h | h | h | h | h | h | h | h
  all_goals exact h.right.left

theorem toYmd_mono (d₁ d₂ : OrdinalDate) : d₁ <= d₂ → d₁.toYmd <= d₂.toYmd := by
  intro hLe
  cases lt_or_eq_of_le hLe with
  | inr hEq => exact hEq ▸ d₁.toYmd.le_refl
  | inl hlt =>
    rw [lt_def'] at hlt
    rw [Ymd.le_def', d₁.toYmd_year_eq, d₂.toYmd_year_eq]

    rcases hlt with yearLt | ⟨yearsEq, dayLe⟩
    -- year1 < year2
    . exact Or.inl ‹_›
    .
      simp only [yearsEq, true_and]
      apply Or.inr
      rcases d₁.toYmd_cases with
      h | h | h | h | h | h | h | h | h | h | h | h
      all_goals (
        rcases d₂.toYmd_cases with
         h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h';
          all_goals (
           first
           |
            apply Or.inr
            refine And.intro ?l ?r
            case l => rw [h.right.right.left, h'.right.right.left]; done
            case r =>
              rw [yearsEq] at *
              omega
              done
           |
              apply Or.inl
              rw [h.right.right.left, h'.right.right.left]
              decide
              done
           |
              have hl := h.left
              have hr := h'.left
              dsimp only [isDayInMonth, isDayOf, firstDayOf, lastDayOf] at hl hr
              rw [yearsEq] at *
              by_cases hleap: d₂.year.isLeapYear <;> (simp [hleap] at *; omega)
              done
          )
      )

set_option hygiene false in
macro "rep" month:ident : tactic =>
  `(tactic|
    split <;> (
      first
      | rw [h.right.right.left] at *; contradiction; done
      |
        have _ : d.day > ($month).lastDayOf d.year := by
          have _ := h.left.left; simp only [firstDayOf, lastDayOf] at *; omega
        have h_cancel : d.day - (($month).lastDayOf d.year) + (($month).lastDayOf d.year) = d.day := by
          omega
        simp only [h.right.left, h.right.right.right, lastDayOf, h_cancel]
    )
  )

theorem toYmd_eq (d : OrdinalDate) : d.toYmd.toOrdinalDate = d := by
  dsimp only [Ymd.toOrdinalDate]
  rcases d.toYmd_cases with
  h | h | h | h | h | h | h | h | h | h | h | h
  . split <;> (first | rw [h.right.right.left] at *; contradiction; done | simp [*]; done)
  . rep january
  . rep february
  . rep march
  . rep april
  . rep may
  . rep june
  . rep july
  . rep august
  . rep september
  . rep october
  . rep november

end OrdinalDate

namespace Ymd
theorem toOrdinalDate_eq (ymd : Ymd) : ymd.toOrdinalDate.toYmd = ymd := by
  rcases ymd.toOrdinalDate_eq_disj with
  h | h | h | h | h | h | h | h | h | h | h | h
  all_goals (
    rcases (ymd.toOrdinalDate).toYmd_cases with
    h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h' | h'

    all_goals (first
      | (apply Ymd.eq_of_val_eq <;> simp [*]); done
      |
        have hl := h.right.right ▸ h'.left.left
        have hle := h.left ▸ ymd.dayLe
        dsimp only [firstDayOf] at hl
        dsimp only [numDays] at hle
        omega
        done

      |
        have ht := h.right.right
        have hl := h'.left.left
        have hx := h.left ▸ ymd.dayLe
        dsimp only [numDays] at hx
        dsimp [OrdinalDate.isDayInMonth, isDayOf] at hl
        dsimp [lastDayOf] at ht
        rw [ht] at hl
        rw [h.right.left] at hl
        by_cases hleap: ymd.year.isLeapYear <;> (simp [hleap] at hl hx; omega)
        done
      |
        have ht := h.right.right
        have hf := h'.left.right

        dsimp only [OrdinalDate.isDayInMonth, isDayOf, lastDayOf] at hf
        dsimp only [lastDayOf] at ht
        have _ : ymd.day >= 1 := ymd.dayGe
        simp [h.right.left] at *
        by_cases hleap: ymd.year.isLeapYear

        simp [hleap] at *
        rw [ht] at hf

        omega
        omega
    )
  )

theorem toOrdinalDate_mono (ymd₁ ymd₂ : Ymd) : ymd₁ ≤ ymd₂ → ymd₁.toOrdinalDate ≤ ymd₂.toOrdinalDate := by
  intro hLe
  cases Ymd.lt_or_eq_of_le hLe with
  | inr hEq => exact hEq ▸ ymd₁.toOrdinalDate.le_refl
  | inl hlt =>
    rw [lt_def'] at hlt
    rw [OrdinalDate.le_def', toOrdinalDate_year_eq ymd₁, toOrdinalDate_year_eq ymd₂]
    rcases hlt with yearLt | ⟨yearsEq, monthLt⟩ | ⟨yearsEq, monthsEq, dayLt⟩
    -- year1 < year2
    case inl.inl => exact Or.inl yearLt
    -- day1 < day2
    case inl.inr.inr.intro.intro =>
      refine .inr (And.intro yearsEq ?_)
      simp only [Ymd.toOrdinalDate]
      split; all_goals (
        split; all_goals (
          first
          | simp [yearsEq]; omega; done
          | exact False.elim <| Month.mk_contra ymd₁.month ymd₂.month ‹_› ‹_› monthsEq
        )
      )
    -- month1 < month2
    case inl.inr.inl.intro =>
      refine Or.inr (And.intro yearsEq ?rrr)
      simp [Ymd.toOrdinalDate, -lastDayOf]
      split; all_goals (
        split; all_goals (
          first
          | (exfalso; exact (Month.not_lt_of_gt' ymd₁.month ymd₂.month _ _ ‹_› ‹_› (by decide) ‹_›)); done
          | (exfalso; exact (Month.lt_irrefl' ymd₁.month ymd₂.month _ ‹_› ‹_›) ‹_›); done
          |
            have hm : ymd₁.month = _ := ‹_›
            have hle := yearsEq ▸ hm ▸ ymd₁.dayLe
            have _ := ymd₂.dayGe
            simp only [numDays] at hle
            simp [numDays, hle, yearsEq]
            by_cases hleap: ymd₂.year.isLeapYear <;> (simp [hleap] at *; omega)
            done
        )
      )

end Ymd

namespace Ymd

theorem toScalarDate_toYmd_inv (y : Ymd) : y.toScalarDate.toYmd = y := by
  dsimp [toScalarDate, ScalarDate.toYmd]
  have h0 : y.toOrdinalDate.toScalarDate.toOrdinalDate = y.toOrdinalDate := y.toOrdinalDate.toScalarDate_toOrdinalDate_inv
  have h1 := y.toOrdinalDate_eq
  rw [h0, h1]


theorem toScalarDate_mono (y₁ y₂: Ymd) : y₁ ≤ y₂ → y₁.toScalarDate ≤ y₂.toScalarDate := fun h => by
  have h0 := toOrdinalDate_mono y₁ y₂ h
  have h1 := OrdinalDate.toScalarDate_mono (y₁.toOrdinalDate) y₂.toOrdinalDate h0
  exact h1

end Ymd

namespace ScalarDate

theorem toYmd_toScalarDate_inv (d : ScalarDate) : d.toYmd.toScalarDate = d := by
  dsimp [toYmd, Ymd.toScalarDate]
  have h0 : d.toOrdinalDate.toYmd.toOrdinalDate = d.toOrdinalDate := d.toOrdinalDate.toYmd_eq
  have h1 : d.toOrdinalDate.toScalarDate = d := d.toOrdinalDate_toScalarDate_inv
  rw [h0, h1]

theorem toYmd_monotonic (d₁ d₂: ScalarDate) : d₁ ≤ d₂ → d₁.toYmd ≤ d₂.toYmd := fun h => by
  have h0 := toOrdinalDate_mono d₁ d₂ h
  have h1 := OrdinalDate.toYmd_mono d₁.toOrdinalDate d₂.toOrdinalDate h0
  exact h1

end ScalarDate
