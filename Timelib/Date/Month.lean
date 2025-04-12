import Timelib.Date.Year

namespace Timelib

/--
A month is a natural number in the interval [1, 12], with the natural
interpretation (1 = January, .., 12 = December). We do not use a shifted
calendar.
-/
@[ext]
structure Month where
  val : Nat
  oneLe : 1 <= val
  isLe : val <= 12
deriving Repr, DecidableEq, Ord

namespace Month

@[match_pattern, reducible] def january   : Month := ⟨1, by decide, by decide⟩
@[match_pattern, reducible] def february  : Month := ⟨2, by decide, by decide⟩
@[match_pattern, reducible] def march     : Month := ⟨3, by decide, by decide⟩
@[match_pattern, reducible] def april     : Month := ⟨4, by decide, by decide⟩
@[match_pattern, reducible] def may       : Month := ⟨5, by decide, by decide⟩
@[match_pattern, reducible] def june      : Month := ⟨6, by decide, by decide⟩
@[match_pattern, reducible] def july      : Month := ⟨7, by decide, by decide⟩
@[match_pattern, reducible] def august    : Month := ⟨8, by decide, by decide⟩
@[match_pattern, reducible] def september : Month := ⟨9, by decide, by decide⟩
@[match_pattern, reducible] def october   : Month := ⟨10, by decide, by decide⟩
@[match_pattern, reducible] def november  : Month := ⟨11, by decide, by decide⟩
@[match_pattern, reducible] def december  : Month := ⟨12, by decide, by decide⟩

@[simp]
abbrev toNat (m : Month) : Nat := m.val

instance : OfNat Month (nat_lit 1) := ⟨january⟩
instance : OfNat Month (nat_lit 2) := ⟨february⟩
instance : OfNat Month (nat_lit 3) := ⟨march⟩
instance : OfNat Month (nat_lit 4) := ⟨april⟩
instance : OfNat Month (nat_lit 5) := ⟨may⟩
instance : OfNat Month (nat_lit 6) := ⟨june⟩
instance : OfNat Month (nat_lit 7) := ⟨july⟩
instance : OfNat Month (nat_lit 8) := ⟨august⟩
instance : OfNat Month (nat_lit 9) := ⟨september⟩
instance : OfNat Month (nat_lit 10) := ⟨october⟩
instance : OfNat Month (nat_lit 11) := ⟨november⟩
instance : OfNat Month (nat_lit 12) := ⟨december⟩

theorem toNat.injective (m₁ m₂ : Month) (h : m₁.toNat = m₂.toNat) : m₁ = m₂ := by
  cases m₁ <;> (cases m₂ <;> (cases h; try rfl))

instance : LE Month where
  le := InvImage Nat.le Month.toNat

instance : LT Month where
  lt := InvImage Nat.lt Month.toNat

theorem le_def {m m' : Month} : (m <= m') = (m.toNat <= m'.toNat) := rfl
theorem lt_def {m m' : Month} : (m < m') = (m.toNat < m'.toNat) := rfl

instance instDecidableLE (m m' : Month) : Decidable (m <= m') := inferInstanceAs (Decidable (m.toNat <= m'.toNat))
instance instDecidableLT (m m' : Month) : Decidable (m < m') := inferInstanceAs (Decidable  (m.toNat < m'.toNat))

theorem lt_trichotomy (y₁ y₂ : Month) : (y₁ < y₂) ∨ y₁ = y₂ ∨ (y₂ < y₁) := by
  rcases Nat.lt_trichotomy y₁.val y₂.val with a | b | c
  . exact Or.inl (lt_def ▸ a)
  . exact Or.inr (Or.inl (Month.mk.injEq y₁.val _ _ y₂.val _ _ ▸ b))
  . exact Or.inr (Or.inr (lt_def ▸ c))

instance : Ord Month := ⟨fun m₁ m₂ => compareOfLessAndEq m₁ m₂⟩

theorem lt_irrefl (m : Month) : ¬(m < m) := by
  simp only [lt_def, Nat.lt_irrefl, not_false_eq_true]

theorem lt_irrefl' (m₁ m₂ m₃ : Month) : m₁ = m₃ → m₂ = m₃ → ¬m₁ < m₂ := by
  simp (config := { contextual := true }) only [lt_def, Nat.lt_irrefl, not_false_eq_true,
    implies_true]

theorem ne_of_lt {m₁ m₂ : Month} : m₁ < m₂ → m₁ ≠ m₂ := by
  intro h1 h2
  simp only [h2, lt_def, toNat] at h1
  exact False.elim (Nat.lt_irrefl _ h1)

theorem mk_contra (a b : Month) {x y : Month} : a = x → b = y → a = b → (_ : x ≠ y := by decide) → False:= by
  intro h0 h1 h2 h3
  apply h3
  rwa [← h0, ← h1]

theorem le_total (a b : Month) : a ≤ b ∨ b ≤ a := Nat.le_total a.val b.val

theorem not_lt_of_gt {m₁ m₂ : Month} : m₁ < m₂ → ¬(m₂ < m₁) := by
  simp only [lt_def]
  exact Nat.not_lt_of_gt

theorem not_le_of_gt {m₁ m₂ : Month} : m₁ < m₂ → ¬(m₂ <= m₁) := by
  simp [lt_def, le_def]

theorem not_lt_of_ge {m₁ m₂ : Month} : m₁ >= m₂ → ¬(m₁ < m₂) := by
  simp [lt_def, le_def]

theorem not_lt_of_gt' (a b x y : Month) : a = x → b = y → y < x → ¬a < b := by
  intro h0 h1
  simp only [← h0, ← h1, lt_def, Nat.not_lt]
  exact Nat.le_of_succ_le

abbrev numDays (year : Year) : Month → Nat
| february => if year.isLeapYear then 29 else 28
| april | june | september | november => 30
| _ => 31

abbrev numDaysLeap : Month → Nat
| february => 29
| april | june | september | november => 30
| _ => 31

abbrev numDaysNonLeap : Month → Nat
| february => 28
| april | june | september | november => 30
| _ => 31

theorem numDays_eq (y : Year) (m : Month) :
  y.isLeapYear ∧ m.numDays y = m.numDaysLeap
  ∨ ¬y.isLeapYear ∧ m.numDays y = m.numDaysNonLeap :=
  if h: y.isLeapYear
  then by simp [h, numDays, numDaysLeap]
  else by simp [h, numDays, numDaysLeap]

def casesOn'.{u}
      {motive : Month → Sort u}
      (m : Month)
      (h_jan : motive january)
      (h_feb : motive february)
      (h_mar : motive march)
      (h_apr : motive april)
      (h_may : motive may)
      (h_jun : motive june)
      (h_jul : motive july)
      (h_aug : motive august)
      (h_sep : motive september)
      (h_oct : motive october)
      (h_nov : motive november)
      (h_dec : motive december)
      : motive m :=
  match m with
  | ⟨1, _, _⟩ => h_jan
  | ⟨2, _, _⟩ => h_feb
  | ⟨3, _, _⟩ => h_mar
  | ⟨4, _, _⟩ => h_apr
  | ⟨5, _, _⟩ => h_may
  | ⟨6, _, _⟩ => h_jun
  | ⟨7, _, _⟩ => h_jul
  | ⟨8, _, _⟩ => h_aug
  | ⟨9, _, _⟩ => h_sep
  | ⟨10, _, _⟩ => h_oct
  | ⟨11, _, _⟩ => h_nov
  | ⟨12, _, _⟩ => h_dec

theorem not_lt_january (m : Month) : ¬m < january := by
  cases m using casesOn' <;> simp [lt_def, le_def, Month.toNat]

--@[reducible]
abbrev nextWrapping (m : Month) : Month := ⟨(m.val % 12) + 1, by omega, by omega⟩

def isNext (m' m: Month) := m'.val = m.val + 1

theorem numDays_pos (month : Month) (year : Year) : 0 < month.numDays year := by
  simp only [Month.numDays]
  by_cases hy : year.isLeapYear
  case pos => split <;> simp [hy, if_true]
  case neg => split <;> simp [hy, if_false]

theorem numDays_lt_numDaysInGregorianYear (month : Month) (year : Year) : month.numDays year < year.numDaysInGregorianYear := by
  simp only [Month.numDays, Year.numDaysInGregorianYear]
  by_cases hy : year.isLeapYear
  case pos => split <;> simp [hy, if_true]
  case neg => split <;> simp [hy, if_false]

theorem numDays_le_31 (month : Month) (year : Year) : month.numDays year <= 31 := by
  simp only [Month.numDays, Year.numDaysInGregorianYear]
  by_cases hy : year.isLeapYear
  case pos =>
    split
    simp [hy, if_true]
    all_goals decide
  case neg =>
    split
    simp [hy, if_false]
    all_goals decide

theorem numDays_le_trans (month : Month) (year : Year) (n : Nat) (h : 31 <= n := by omega) : month.numDays year <= n :=
  Nat.le_trans (numDays_le_31 month year) h

theorem notDecember : forall (m : Month), m ≠ december → m.val <= 11 := by
  intro m h; cases m using casesOn'; all_goals simp [h]; try contradiction

@[reducible] def next' (m : Month) : Month :=
  if h: m = december then january
  else ⟨m.val + 1, by omega, by have h' := notDecember m h; omega⟩

theorem next_next' : forall (m : Month), m.nextWrapping = m.next' := by
  intro m
  cases m using casesOn'; all_goals simp [nextWrapping, next']

@[simp]
abbrev firstDayOf (y : Year) : Month → Nat
  | january => 1
  | february => 32
  | march => 60 + ite y.isLeapYear 1 0
  | april => 91 + ite y.isLeapYear 1 0
  | may => 121 + ite y.isLeapYear  1 0
  | june => 152 + ite y.isLeapYear 1 0
  | july => 182 + ite y.isLeapYear 1 0
  | august => 213 + ite y.isLeapYear 1 0
  | september => 244 + ite y.isLeapYear 1 0
  | october => 274 + ite y.isLeapYear 1 0
  | november => 305 + ite y.isLeapYear 1 0
  | december => 335 + ite y.isLeapYear 1 0

@[simp]
abbrev lastDayOf (y : Year) : Month → Nat
  | january => 31
  | february => 59 + ite y.isLeapYear 1 0
  | march => 90 + ite y.isLeapYear 1 0
  | april => 120 + ite y.isLeapYear 1 0
  | may => 151 + ite y.isLeapYear  1 0
  | june => 181 + ite y.isLeapYear 1 0
  | july => 212 + ite y.isLeapYear 1 0
  | august => 243 + ite y.isLeapYear 1 0
  | september => 273 + ite y.isLeapYear 1 0
  | october => 304 + ite y.isLeapYear 1 0
  | november => 334 + ite y.isLeapYear 1 0
  | december => 365 + ite y.isLeapYear 1 0

/- These specialized ones are for an `Array.ofFn` csimp -/
@[simp]
abbrev lastDayOfLeap : Month → Nat
  | january => 31
  | february => 60
  | march => 91
  | april => 121
  | may => 152
  | june => 182
  | july => 213
  | august => 244
  | september => 274
  | october => 305
  | november => 335
  | december => 366

@[simp]
abbrev lastDayOfNonLeap : Month → Nat
  | january => 31
  | february => 59
  | march => 90
  | april => 120
  | may => 151
  | june => 181
  | july => 212
  | august => 243
  | september => 273
  | october => 304
  | november => 334
  | december => 365

theorem lastDayOf_eq (y : Year) (m : Month) :
  y.isLeapYear ∧ m.lastDayOf y = m.lastDayOfLeap
  ∨ ¬y.isLeapYear ∧ m.lastDayOfNonLeap = m.lastDayOfNonLeap :=
  if h: y.isLeapYear
  then by simp [h, lastDayOf, lastDayOfLeap]
  else by simp [h, lastDayOf, lastDayOfNonLeap]

theorem lastDayOf_le (y : Year) (m : Month) : m.lastDayOf y <= y.numDaysInGregorianYear := by
 by_cases h_leap : y.isLeapYear
 all_goals
   simp [lastDayOf, h_leap, ↓reduceIte]
   split; all_goals (simp [Year.numDaysInGregorianYear, h_leap])

@[simp]
abbrev isDayOf (y : Year) (m : Month) (d : Nat) : Prop :=
  m.firstDayOf y <= d ∧ d <= m.lastDayOf y

theorem le_lastDayOf_of_le_numDays (y : Year) (m : Month) (d : Nat) : d <= m.numDays y → d <= m.lastDayOf y :=
  match m with
  | january | february | march | april | may | june
  | july | august | september | october | november | december => by
    dsimp [lastDayOf, numDays] <;> (by_cases hleap: y.isLeapYear <;> (simp [hleap]; (try intro _; omega)))

theorem first_lt_last (y : Year) (m : Month) : m.firstDayOf y < m.lastDayOf y := by
  dsimp [firstDayOf, lastDayOf]
  cases m using casesOn' <;> (simp; try omega)

theorem lastDayOf_january_eq (y : Year) : january.lastDayOf y = 31 := by
  by_cases hLeap: y.isLeapYear; all_goals (simp [hLeap, lastDayOf])

@[simp]
theorem numDays_january_eq (y : Year) : january.numDays y = 31 := by
  by_cases hLeap: y.isLeapYear; all_goals (simp [hLeap])

theorem okJanuary (y : Year) : (lastDayOf y january) + 1 = (firstDayOf y february) := by
  by_cases h: y.isLeapYear <;> simp [h]

theorem okFebruary (y : Year) : (lastDayOf y february) + 1 = (firstDayOf y march) := by
  by_cases h: y.isLeapYear <;> simp [h]

theorem okMarch (y : Year) : (lastDayOf y march) + 1 = (firstDayOf y april) := by
  by_cases h: y.isLeapYear <;> simp [h]

theorem okApril (y : Year) : (lastDayOf y april) + 1 = (firstDayOf y may) := by
  by_cases h: y.isLeapYear <;> simp [h]

theorem lastFirstOk (y : Year) (m : Month) : ((lastDayOf y m) + 1) % y.numDaysInGregorianYear = (firstDayOf y (m.nextWrapping)) := by
  cases m using Month.casesOn' <;> (by_cases h: y.isLeapYear <;> simp [Year.numDaysInGregorianYear, h])

theorem lastFirstOk' (y : Year) (m : Month) : ((firstDayOf y m) + (m.numDays y)) % y.numDaysInGregorianYear = (firstDayOf y (m.nextWrapping)) := by
  cases m using Month.casesOn' <;> (by_cases h: y.isLeapYear <;> simp [Year.numDaysInGregorianYear, Month.numDays, h])

theorem last_december_eq (y : Year) : (december.lastDayOf y) = y.numDaysInGregorianYear := by
  by_cases h: y.isLeapYear <;> simp [h, Year.numDaysInGregorianYear]

theorem val_eq_1_iff_january (m : Month) : m.val = 1 ↔ m = january := by
  refine Iff.intro ?mp ?mpr
  case mp => exact fun a => toNat.injective m january a
  case mpr => intro h; rw [h]; done

def lastDayRec (year : Year) : Month → Nat
  | m@⟨1, _, _⟩ => numDays year m
  | m@⟨n+1+1, _, _⟩ => (numDays year m) + (lastDayRec year ⟨n+1, by omega, by omega⟩)

def firstDayRec (year : Year) : Month → Nat
  | ⟨1, _, _⟩ => 1
  | m@⟨n+1+1, _, _⟩ => 1 + (lastDayRec year ⟨n+1, by omega, by omega⟩)

theorem isJanuary (m : Month) : m ≠ january → m.val ≠ 1 := by
  intro h0 h1; exact h0 (show m = january by rwa [Month.mk.injEq])

theorem notJanuary {m : Month} : m ≠ january → m.val > 1 := by
  intro h0; have _ := isJanuary m h0; have _ := m.oneLe; omega

def pred : (m : Month) → (m ≠ january) → Month
  | ⟨m, h0, h1⟩, h => ⟨m - 1, have _ : m > 1 := notJanuary h; by omega, by omega⟩

def lastDayRec' (y : Year) (m : Month): Nat :=
    if h: m = january
    then m.numDays y
    else
      have _ : 1 < m.val := notJanuary h
      have _ : m.val <= 12 := m.isLe
      (m.numDays y) + (lastDayRec' y ⟨m.val - 1, by omega, by omega⟩)

def firstDayRec' (m : Month) (y : Year) : Nat :=
  if h : m = january
  then 1
  else
    have := notJanuary h
    have := m.isLe
    1 + (lastDayRec' y ⟨m.val - 1, by omega, by omega⟩)

@[reducible, simp]
def isDayOfRec (y : Year) (m : Month) (ordinalDay : Nat) : Prop :=
  m.firstDayRec y <= ordinalDay ∧ ordinalDay <= m.lastDayRec y

theorem lastDayRec_eq_lastDayOf: lastDayRec = lastDayOf :=
  funext <| fun y => funext <| fun m => by
    cases m using casesOn' <;>
      by_cases h': y.isLeapYear; all_goals simp [lastDayRec, lastDayOf, h', numDays]

theorem lastDayRec'_eq_lastDayOf: lastDayRec' = lastDayOf := by
  apply funext
  intro y
  apply funext
  intro m
  by_cases h: y.isLeapYear
  case pos =>
    cases m using casesOn'
    all_goals simp [lastDayRec', lastDayOf, h, numDays]
    done
  case neg =>
    cases m using casesOn'
    all_goals simp [lastDayRec', lastDayOf, h, numDays]
    done

theorem lastDayRec_le (y : Year) (m : Month) : lastDayRec y m <= y.numDaysInGregorianYear := by
  rw [lastDayRec_eq_lastDayOf]; exact lastDayOf_le y m

theorem pred_ne_december (m : Month) : m.val - 1 = 12 → False := by
  have _ := m.isLe; omega

end Month
