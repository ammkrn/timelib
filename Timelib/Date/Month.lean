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
import Timelib.Date.Year

open Lean

/-
This ends up being easier to use than a Nat restricted to `1 <= n <= 12`,
because we can define functions using the recursor without having to discharge
the edge cases of 0 and n > 12
-/
inductive Month
| january
| february
| march
| april
| may
| june
| july
| august
| september
| october
| november
| december
deriving Repr

@[reducible]
def Month.toNat : Month → Nat
| january => 1
| february => 2
| march => 3
| april => 4
| may => 5
| june => 6
| july => 7
| august => 8
| september => 9
| october => 10
| november => 11
| december => 12

instance : OfNat Month (nat_lit 1) := ⟨Month.january⟩ 
instance : OfNat Month (nat_lit 2) := ⟨Month.february⟩ 
instance : OfNat Month (nat_lit 3) := ⟨Month.march⟩ 
instance : OfNat Month (nat_lit 4) := ⟨Month.april⟩ 
instance : OfNat Month (nat_lit 5) := ⟨Month.may⟩ 
instance : OfNat Month (nat_lit 6) := ⟨Month.june⟩ 
instance : OfNat Month (nat_lit 7) := ⟨Month.july⟩ 
instance : OfNat Month (nat_lit 8) := ⟨Month.august⟩ 
instance : OfNat Month (nat_lit 9) := ⟨Month.september⟩ 
instance : OfNat Month (nat_lit 10) := ⟨Month.october⟩
instance : OfNat Month (nat_lit 11) := ⟨Month.november⟩ 
instance : OfNat Month (nat_lit 12) := ⟨Month.december⟩ 

def Month.ofNat? : Nat → Option Month
| 1 => some 1
| 2 => some 2
| 3 => some 3
| 4 => some 4
| 5 => some 5
| 6 => some 6
| 7 => some 7
| 8 => some 8
| 9 => some 9
| 10 => some 10
| 11 => some 11
| 12 => some 12
| _ => none

instance : ToJson Month where
  toJson := ToJson.toJson ∘ Month.toNat

instance : FromJson Month where 
  fromJson? j := do
    let n ← j.getNat?
    match Month.ofNat? n with
    | none => throw s!"Month must be between 1 and 12; got {n}"
    | some m => .ok m

theorem Month.toNat.injective (m₁ m₂ : Month) (h : m₁.toNat = m₂.toNat) : m₁ = m₂ := by
  cases m₁ <;> (cases m₂ <;> (cases h; try rfl))

instance : LE Month where
  le := InvImage Nat.le Month.toNat

instance : LT Month where
  lt := InvImage Nat.lt Month.toNat

theorem Month.le_def {m m' : Month} : (m <= m') = (m.toNat <= m'.toNat) := rfl
theorem Month.lt_def {m m' : Month} : (m < m') = (m.toNat < m'.toNat) := rfl

instance instDecidableLEMonth (m m' : Month) : Decidable (m <= m') := inferInstanceAs (Decidable (m.toNat <= m'.toNat))
instance instDecidableLTMonth (m m' : Month) : Decidable (m < m') := inferInstanceAs (Decidable  (m.toNat < m'.toNat))

instance : LinearOrder Month where
  le_refl (a) := le_refl a.toNat
  le_trans (a b c) := Nat.le_trans
  lt_iff_le_not_le (a b) := Nat.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by 
    apply Month.toNat.injective
    exact le_antisymm h1 h2
  le_total := by simp [Month.le_def, le_total]
  decidable_le := inferInstance

instance : Ord Month := ⟨fun m₁ m₂ => compareOfLessAndEq m₁ m₂⟩

@[reducible] def Month.numDays (year : Year) : ∀ (month : Month), Nat
| february => if year.isLeapYear then 29 else 28
| april => 30
| june => 30
| september => 30
| november => 30
| _ => 31

theorem Month.numDays_pos (month : Month) (year : Year) : 0 < month.numDays year := by
  simp only [Month.numDays]
  by_cases hy : year.isLeapYear
  case pos => split <;> simp [hy, if_true]
  case neg => split <;> simp [hy, if_false]

theorem Month.numDays_lt_numDaysInGregorianYear (month : Month) (year : Year) : month.numDays year < year.numDaysInGregorianYear := by
  simp only [Month.numDays, Year.numDaysInGregorianYear]
  by_cases hy : year.isLeapYear
  case pos => split <;> simp [hy, if_true]
  case neg => split <;> simp [hy, if_false]

theorem Month.numDays_lt_31 (month : Month) (year : Year) : month.numDays year <= 31 := by
  simp only [Month.numDays, Year.numDaysInGregorianYear]
  by_cases hy : year.isLeapYear
  case pos => split <;> simp [hy, if_true]
  case neg => split <;> simp [hy, if_false]
