import Mathlib.Data.Int.Defs
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Basic
import Mathlib.Init.Order.Defs
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Basic
import Mathlib.Init.Data.Int.Order
import Mathlib.Logic.Equiv.Basic
import Mathlib.Init.Data.Int.Order
import Lean.Data.Json

theorem h100 : ((146096 : Int) / 36524) * 100 = 400 := by decide
theorem h4 : ((146096 : Int) % 36524) / 1461 * 4 = 0 := by decide
theorem h1 : ((Int.fmod 146096 36524) % 1461) / 365 = 0 := by decide
theorem hdiv : (1460 : Int) / 365 = 4 := by decide
theorem hdiv' : ((146096 : Int) % 36524) / 365 = 0 := by decide
theorem pos36524 : (0 : Int) < 36524 := by decide
theorem pos1461 : (0 : Int) < 1461 := by decide
theorem pos1460 : (0 : Int) < 1460 := by decide
theorem pos365 : (0 : Int) < 365 := by decide
theorem pos146097 : (0 : Int) < 146097 := by decide
theorem pos4 : (0 : Int) < 4 := by decide
theorem pos100 : (0 : Int) < 100 := by decide
theorem pos400 : (0 : Int) < 400 := by decide

theorem not_lt_and_gt {day lo hi : Nat} (day_lt_lo : (day < lo)) (lo_lt_hi : lo < hi) : ¬hi < day :=
  fun hi_lt_day => lt_asymm (lt_trans lo_lt_hi hi_lt_day) day_lt_lo

theorem not_le_and_gt {day lo hi : Nat} (day_le_lo : (day <= lo)) (lo_lt_hi : lo < hi) : ¬hi < day :=
  fun hi_lt_day => lt_asymm (lt_of_lt_of_le hi_lt_day day_le_lo) lo_lt_hi

theorem not_le_and_ge_of_lt {day lo hi : Nat} (h0 : day <= lo) (h1 : lo < hi) : ¬hi <= day :=
  fun hi_le_day => absurd hi_le_day (not_le_of_gt <| lt_of_le_of_lt h0 h1)

theorem Nat.lt_of_succ_le_sub {m n l : Nat} (h : l.succ <= m - n) : n < m :=
  Nat.lt_of_sub_eq_succ (Nat.succ_pred (not_eq_zero_of_lt h)).symm

theorem Nat.lt_of_succ_le_sub' {m n l : Nat} (h0 : 0 < l) (h : l <= m - n) : n < m := by
  have h0 : l.pred.succ = l := Nat.succ_pred (not_eq_zero_of_lt h0)
  rw [<- h0] at h
  exact Nat.lt_of_succ_le_sub h

theorem Int.of_nat_nonneg (n : ℕ) : 0 ≤ Int.ofNat n := by
  simp

-- theorem Int.mod_nonneg (a : ℤ) {b : ℤ} : b ≠ 0 → 0 ≤ a % b := sorry

-- theorem Int.mod_lt_of_pos (a : ℤ) {b : ℤ} (H : 0 < b) : a % b < b := sorry

-- @[simp] theorem Int.zero_mod (b : ℤ) : 0 % b = 0 := sorry

-- theorem Int.le_sub_one_iff {a b : ℤ} : a ≤ b - 1 ↔ a < b := sorry

-- theorem Int.lt_add_one_iff {a b : ℤ} : a < b + 1 ↔ a ≤ b := sorry

--@[simp]
--theorem Int.mul_div_cancel (a : ℤ) {b : ℤ} (H : b ≠ 0) : a * b / b = a := sorry

theorem int.div_add_mod' (m k : ℤ) : m / k * k + m % k = m :=
  sorry

theorem Int.div_eq_zero_of_lt' {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a / b = 0
:= by
  rw [←div_eq_ediv]
  apply Int.div_eq_zero_of_lt H1 H2
where
  div_eq_ediv : Int.div a b = a / b := by
    simp [HDiv.hDiv, Div.div]
    apply Int.div_eq_ediv
    · assumption
    · apply Int.le_of_lt
      apply Int.lt_of_le_of_lt H1 H2

--@[simp]
--theorem Int.zero_div : ∀ (d : Int), 0 / d = 0 := sorry

theorem Int.fmod_nonneg_of_pos_mod : ∀ (x : Int) {m : Int}, (h : 0 < m) → 0 <= x.fmod m
| _, Int.negSucc _, hm => by cases hm; done
| _, Int.ofNat 0, hm => by cases hm; done
| Int.ofNat 0, Int.ofNat (_m+1), _hm => by simp [Int.fmod]
| Int.ofNat (x+1), Int.ofNat (m+1), _hm => by
  simp [Int.fmod, -Int.ofNat_eq_cast]
  apply Int.ofNat_zero_le
| Int.negSucc xNat, Int.ofNat (mNat+1), hm => by
  refine' fmod_nonneg' _ hm

@[simp]
theorem Int.fdiv_pos_eq_div : ∀ {a b : Int}, 0 <= a → 0 <= b → Int.fdiv a b = a / b
| .ofNat 0, .ofNat b_n, _ha, _hb => by simp [Int.fdiv]
| .negSucc _, _, ha, _hb => by cases ha
| _, .negSucc _, _ha, hb => by cases hb
| .ofNat (a_n + 1), .ofNat b_n, _ha, _hb => by
  simp [Int.fdiv, -Int.ofNat_eq_cast]

@[simp]
theorem Int.fmod_pos_eq_mod : ∀ {a b : Int}, 0 <= a → 0 <= b → a.fmod b = a % b
| .ofNat 0, .ofNat b_n, _ha, _hb => by simp [Int.fmod]
| .negSucc _, _, ha, _hb => by cases ha
| _, .negSucc _, _ha, hb => by cases hb
| .ofNat (a_n + 1), .ofNat b_n, _ha, _hb => by
  simp [Int.fmod, -Int.ofNat_eq_cast]

@[simp]
theorem Int.fmod_fmod_eq (a : Int) {m₀ m₁ : Int} (h : 0 < m₀) (h' : 0 <= m₁) :
  (a.fmod m₀).fmod m₁ = (a.fmod m₀) % m₁ :=
    @Int.fmod_pos_eq_mod (a.fmod m₀) m₁ (Int.fmod_nonneg_of_pos_mod a h) h'

@[simp]
theorem Int.fdiv_fmod_eq_fmod_div (a : Int) {m d : Int} (h : 0 < m) (h' : 0 < d) :
  (a.fmod m).fdiv d = (a.fmod m) / d :=
  @fdiv_pos_eq_div (a.fmod m) d (Int.fmod_nonneg_of_pos_mod _ h) (le_of_lt h')

@[simp]
theorem Int.fdiv_mod_eq_mod_div (a : Int) {m d : Int} (h : 0 < m) (h' : 0 < d) :
  (a % m).fdiv d = (a % m) / d :=
  @fdiv_pos_eq_div (a % m) d (emod_nonneg a <| Int.ne_of_gt h) (le_of_lt h')


@[simp]
theorem Int.fmodmod (a : Int) {m₀ m₁ m₂ : Int} (_h0 : 0 < m₀) (h1 : 0 < m₁) (h2 : 0 < m₂) :
  ((a.fmod m₀) % m₁).fmod m₂ = (a.fmod m₀) % m₁ % m₂ :=
  @Int.fmod_pos_eq_mod (a.fmod m₀ % m₁) m₂ (emod_nonneg _ (ne_of_gt h1)) (le_of_lt h2)

@[simp]
theorem Int.mod_fmod_eq_mod_mod {a m₀ m₁ : Int} (h0 : 0 < m₀) (h1 : 0 <= m₁) :
  (a % m₀).fmod m₁ = (a % m₀) % m₁ :=
    Int.fmod_pos_eq_mod (emod_nonneg _ (ne_of_lt h0).symm) h1

theorem fdiv_neg_eq
  {a_n b_n : Nat}
  {a b : Int}
  (h_a : a = Int.negSucc a_n)
  (h_b : b = Int.ofNat b_n.succ) : Int.fdiv a b = Int.negSucc (a_n / b_n.succ) := by
  simp [Int.fdiv, h_a]
  rw [h_b]
  done

--theorem Int.div_add_mod (a b : ℤ) : b * (a / b) + a % b = a := sorry

theorem Int.fmod_lt : ∀ (x : Int) {m : Int}, (h : 0 < m) → x.fmod m < m
| Int.ofNat 0, Int.ofNat _mn, hm => hm
| Int.ofNat (xn+1), Int.ofNat mn, hm => by
  simp [Int.fmod]
  exact emod_lt_of_pos (↑xn + 1) hm

  --split
  --next => exact hm
  --next c _ _ _ g =>
  --  simp [Int.le_def] at *
  --  rw [g]
  --  exact Nat.mod_lt c (Int.ofNat_lt.mp (g ▸ hm))
  --next f g => cases g
  --next f g => cases f
  --next f g => cases f
| Int.negSucc x, Int.ofNat m, hm => by
  simp [Int.fmod, Int.subNatNat]
  have hh : (x % m).succ <= m := @Nat.mod_lt x m (Int.ofNat_lt.mp hm)
  simp [Nat.sub_eq_zero_of_le hh]
  refine' Nat.sub_lt_of_pos_le (Nat.succ_pos (x % m)) hh
| _, Int.negSucc _, hm => by cases hm; done

theorem ne_neg_succ_of_zero_le {a : Int} {b : Nat} (h : 0 <= a) : ¬(a = Int.negSucc b) := fun h' => by
  cases a with
  | ofNat _ => cases h'
  | negSucc _ => cases h

theorem ne_of_nat_of_lt_zero {a : Int} {b : Nat} (h : a < 0) : ¬(a = Int.ofNat b) := fun h' => by
  cases a with
  | ofNat _ => cases h
  | negSucc _ => cases h'

theorem Int.add_mul_div_left (a : ℤ) {b : ℤ} (c : ℤ) (H : b ≠ 0) :
  (a + b * c) / b = a / b + c
:= Int.add_mul_ediv_left a c H

theorem Int.add_mul_div_right (a b : Int) {c : Int} (H : c ≠ 0) :
  (a + b * c) / c = a / c + b
:= Int.add_mul_ediv_right a b H

theorem div_eq_zero_of_lt : ∀ {a b : Int}, 0 <= a → 0 <= b → a < b → a / b = 0
| .ofNat a, .ofNat b, ha, hb, hlt => by
  have hx : a < b := by exact (@Int.ofNat_le (a+1) b).mp hlt
  have hy := Nat.div_eq_of_lt hx
  simp [HDiv.hDiv, Div.div, Int.div] at *
  exact Int.natAbs_eq_zero.mp hy
| .ofNat a, .negSucc b, _ha, hb, _hlt => by cases hb
| .negSucc a, .ofNat b, ha, _hb, _hlt => by cases ha
| .negSucc _, .negSucc _, ha, _hb, _hlt => by cases ha

theorem neither_lem (a b c : Int) (h0 : 0 <= (a * b)) (h1 : 0 <= c) (hb : 0 < b) (h : c < b) : ((a * b) + c).fdiv b = a := by
  have hsum : 0 <= (a * b + c) := Int.add_nonneg h0 h1
  simp [Int.fdiv_pos_eq_div hsum (le_of_lt hb)]
  have hdiv : (a * b + c) / b = a := by
    have hdiv' := Int.add_mul_div_right c a (ne_of_lt hb).symm
    rwa [add_comm, div_eq_zero_of_lt h1 (le_of_lt hb) h, zero_add] at hdiv'
  exact hdiv

theorem Nat.div_le_div_right' {n m : Nat} (h : n ≤ m) {k : Nat} :
  n / k ≤ m / k
:= Nat.div_le_div_right h

theorem Int.not_of_nat_le_neg_succ (a b : Nat) : ¬(Int.ofNat a <= Int.negSucc b) := fun h => by
  exact absurd (lt_of_le_of_lt h (Int.negSucc_lt_zero b)) (not_lt_of_ge (Int.ofNat_zero_le a))

theorem Int.neg_succ_monotone {x y : Nat} (h : x >= y) : Int.negSucc x <= Int.negSucc y := by
  simp [Int.le_def, Int.nonneg_def, Int.sub_eq_add_neg]
  have h0 : - negSucc x = (x.succ) := PLift.down_up (- negSucc x)
  simp [h0, -Int.ofNat_eq_cast]
  refine Exists.intro ((x + 1) - (y + 1)) ?h
  have h1 : negSucc y + ((↑x) +1) = subNatNat (x+1) (Nat.succ y) := Int.negSucc_add_ofNat y (x + 1)
  simp only [h1]
  apply Int.subNatNat_of_le
  apply Nat.succ_le_succ
  exact h

theorem Int.neg_succ_monotone_rev {x y : Nat} : Int.negSucc x <= Int.negSucc y → x >= y := by
  simp [Int.le_def, Int.nonneg_def, Int.sub_eq_add_neg]
  have h0 : - negSucc x = (x.succ) := PLift.down_up (- negSucc x)
  simp [h0]
  intro sum
  have h1 : negSucc y + ((↑x) +1) = subNatNat (x+1) (Nat.succ y) := Int.negSucc_add_ofNat y (x + 1)
  simp [h1]
  intro h2
  apply le_of_not_gt
  intro h3
  have h4 := Int.subNatNat_of_lt (Nat.succ_lt_succ h3)
  rw [h2] at h4
  cases h4

theorem Int.fdiv_le_div_right {n₁ n₂ de : Int} (h : n₁ <= n₂) (hde : 0 <= de) : n₁.fdiv de <= n₂.fdiv de := by
  simp [Int.fdiv]
  split
  next =>
    split
    · simp
    · exact ediv_nonneg h hde
    · cases hde
    · exact le_refl _
    · cases hde
      cases h
    · apply Int.ofNat_le.mpr; simp
  next a _ =>
    split
    · apply Int.ofNat_le.mpr; simp [Nat.eq_zero_of_le_zero (Int.ofNat_le.mp h)]
    · next s _ r =>
      simp [(show a = s by cases r; rfl)]
      have has : s = a := by cases r; rfl
      have :=  Nat.div_le_div_right' (Int.ofNat_le.mp h) (k := s)
      -- simp [has, this]
      sorry
    · next r => cases r
    repeat exact (absurd h (Int.not_of_nat_le_neg_succ _ _))
  next => cases hde
  next =>
    split
    · exact le_refl _
    · apply Int.ofNat_le.mpr; exact Nat.zero_le _
    · next t => cases t
    · exact le_refl _
    repeat (next t => cases t)
  next a b =>
    split
    next => exact le_of_lt (Int.negSucc_lt_zero (a / b.succ))
    next s t => exact le_trans (le_of_lt (Int.negSucc_lt_zero _)) (Int.ofNat_zero_le (_ / _))
    next t => cases t
    next => exact le_of_lt (Int.negSucc_lt_zero (a / b.succ))
    next s t =>
      simp [(show b.succ = s.succ by cases t; rfl)]
      apply Int.neg_succ_monotone (Nat.div_le_div_right (Int.neg_succ_monotone_rev h))
    next t => cases t
  next=> cases hde


theorem Int.add_right_nonneg {x n : Int} (h : 0 <= x) (h' : 0 <= n) : 0 <= x + n :=
  Int.add_nonneg h h'

theorem Int.toNat_le_of_le_of_nonneg : ∀ {x : Int} {y : Nat}, 0 <= x → x <= y → x.toNat <= y
| .ofNat n, y, h1, h2 => by
  simp [Int.ofNat_eq_cast] at h2
  simp [Int.toNat, h2]
| .negSucc _, _, h1, h2 => by cases h1

theorem Int.div_le_of_le_mul {a b c : ℤ} (H : 0 < c) (H' : a ≤ b * c) : a / c ≤ b := sorry
theorem Int.div_lt_of_lt_mul {a b c : ℤ} (H : 0 < c) (H' : a < b * c) : a / c < b := sorry
theorem Int.mul_lt_of_lt_div {a b c : ℤ} (H : 0 < c) (H3 : a < b / c) : a * c < b := sorry
theorem Int.lt_mul_of_div_lt {a b c : ℤ} (H1 : 0 < c) (H2 : a / c < b) : a < b * c := sorry

theorem Int.mul_le_of_le_div {a b c : Int} (H1 : 0 < c) (H2 : a ≤ b / c) : a * c ≤ b := sorry

theorem Int.mul_le_of_le_fdiv {n d q : Int} (hn : 0 <= n) (hd : 0 < d) (hq : 0 < q) (h : n.fdiv d = q) : q * d <= n := by
  simp [fdiv_pos_eq_div hn (le_of_lt hd)] at h
  exact Int.mul_le_of_le_div hd (le_of_eq h.symm)

@[simp] theorem Int.add_mod_self {a b : Int} : (a + b) % b = a % b := sorry

--@[simp] theorem Int.mul_mod_left (a b : Int) : a * b % b = 0 := sorry

@[simp] theorem Int.mul_mod (a b n : Int) : a * b % n = a % n * (b % n) % n := sorry

@[simp] theorem Int.add_mul_mod_self {a b c : ℤ} : (a + b * c) % c = a % c := sorry

--@[simp] theorem Int.mod_eq_zero_lemma (a b c m : Int) : (((a * m) + (b * m)) + c * m) % m = 0 := by simp

@[simp] theorem Int.mod_eq_zero_lemma' (a b c m : Int) : (((a * m) + (b * m)) + c) % m = c % m := by
  simp [(Int.add_mul a b m).symm, add_comm ((a + b) * m) c]

--@[simp] theorem Int.mod_eq_of_lt {a b : ℤ} (H1 : 0 ≤ a) (H2 : a < b) : a % b = a := sorry

--theorem Int.div_nonneg {a b : ℤ} (Ha : 0 ≤ a) (Hb : 0 ≤ b) : 0 ≤ a / b := sorry

theorem Int.add_pos_ne_zero_of_nonneg {a b : Int} (h : 0 <= a) (h' : 0 < b) : a + b ≠ 0 := fun hf => by
  have hle : a <= a + b := Int.le_add_of_nonneg_right (le_of_lt h')
  rw [le_antisymm (hf ▸ hle) h] at hf
  simp at hf
  rw [hf] at h'
  exact False.elim $ lt_irrefl _ h'

theorem Int.div_mod_unique {a b r q : ℤ} (h : 0 < b) :
  a / b = q ∧ a % b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < b :=
    sorry

theorem Int.div_pigeonhole {x lower c : Int} (_hx : 0 <= x) (_hlower : 0 < lower) (hc : 0 < c) : c * lower < x → x < c * (lower + 1) → (x / c) = lower := fun h1 h2 => by
  rw [mul_comm] at h2
  have div_lt_plus_one := Int.div_lt_of_lt_mul hc h2
  apply by_contradiction
  intro hne
  cases lt_or_gt_of_ne hne with
  | inl hl =>
    rw [mul_comm] at h1
    exact False.elim ((lt_asymm h1) (Int.lt_mul_of_div_lt hc hl))
  | inr hr =>
    have h_div_le : (x / c) <= lower := Int.le_of_add_le_add_right (Int.div_lt_of_lt_mul hc h2)
    cases lt_or_eq_of_le h_div_le with
    | inl hlx =>
      rw [mul_comm] at h1
      exact False.elim ((lt_asymm h1) (Int.lt_mul_of_div_lt hc hlx))
    | inr hrx => exact False.elim (hne hrx)

@[simp]
theorem Int.add_mul_div_eq (n : Int) {x denom : Int} :
  denom ≠ 0 → 0 <= x → x < denom → (n * denom + x) / denom = n := fun hne hle hlt => by
  rw [add_comm, mul_comm]
  have hx := Int.add_mul_div_left x n hne
  have hx' : x / denom = 0 := Int.div_eq_zero_of_lt' hle hlt
  rw [hx'] at hx
  simp [zero_add] at hx
  assumption

@[simp]
theorem Int.add_mul_div_eq' (n : Int) {x denom : Int} :
  denom ≠ 0 → 0 <= x → x < denom → (denom * n + x) / denom = n := by
  rw [mul_comm]; exact add_mul_div_eq n

@[simp]
theorem Int.add_mul_div_eq'' (n : Int) {x denom : Int} :
  denom ≠ 0 → 0 <= x → x < denom → (x + n * denom) / denom = n := by
  rw [add_comm]; exact add_mul_div_eq n

@[simp]
theorem Int.add_mul_div_eq''' (n : Int) {x denom : Int} :
  denom ≠ 0 → 0 <= x → x < denom → (x + denom * n) / denom = n := by
  rw [add_comm, mul_comm]; exact add_mul_div_eq n

theorem toOrdinalDate_helper1 : ∀ {x : Int}, 1 <= x → 1 <= x.toNat
| Int.negSucc _, h => by cases h
| Int.ofNat xN, h => by
  apply Classical.byContradiction
  intro h'
  have h_eq_zero : xN = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (lt_of_not_ge h') : xN <= 0)
  rw [h_eq_zero] at h
  cases h

instance {n : Nat} : Lean.ToJson (Fin n) where
  toJson fin :=
    Lean.Json.mkObj [("val", Lean.ToJson.toJson fin.val)]

instance {n : Nat} : Lean.FromJson (Fin n) where
  fromJson? j := do
    let (val : Nat) ← (Lean.fromJson? (← j.getObjVal? "val"))
    if h : val < n
    then return Fin.mk val h
    else Except.error s!"Fin.val out of range: {val} is not less than {n}"

/-
In general, we're only concerned with si powers LE zero,
because we need to remain coherent with one-second resolutions.
For any si pow > 0, you end up losing information. E.g. adding a single
leap second to a DateTime that's in (10^1) resolution is no longer
a simple operation.
-/
abbrev NegSiPow := { z : Int // z <= 0 }
abbrev SiPow := Int

instance : OfNat NegSiPow 0 where
  ofNat := ⟨0, by decide⟩

instance : Coe NegSiPow SiPow where
  coe p := p.val

def minLeft (x : NegSiPow) (y : Int) : NegSiPow :=
  ⟨min x.val y, Int.le_trans (min_le_left x.val y) x.property⟩

theorem minLeft_eq  (x : NegSiPow) (y : Int) : (minLeft x y).val = min x.val y := rfl

theorem minLeft_le (x : NegSiPow) (y : Int) : (minLeft x y) <= x := by
  simp only [minLeft]
  exact min_le_left x.val y

theorem minLeft_eq' (x : NegSiPow) (y : Int) : (minLeft (minLeft x y) (min (↑x) y)) = (minLeft x y) :=
  have h0 : (minLeft (minLeft x y) (min (↑x) y)).val = (minLeft x y).val := by exact min_self (min (↑x) y)
  Subtype.val_inj.mp h0

def minRight (y : Int) (x : NegSiPow) : NegSiPow := minLeft x y

theorem minRight_eq (x : NegSiPow) (y : Int) : (minRight y x).val = min x.val y := rfl
