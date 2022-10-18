import Lean.Data.Json
import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Equiv.Basic
import Mathlib.Init.Data.Int.Order

open Lean

structure ScalarDate where
  day : Int
deriving Repr, ToJson, FromJson

theorem ScalarDate.val_eq_of_eq : ∀ {d₁ d₂ : ScalarDate} (h : d₁ = d₂), d₁.day = d₂.day
| ⟨_⟩, _, rfl => rfl

theorem ScalarDate.eq_of_val_eq : ∀ {d₁ d₂ : ScalarDate} (h : d₁.day = d₂.day), d₁ = d₂
| ⟨_⟩, _, rfl => rfl

instance : LE ScalarDate where
  le := InvImage Int.le ScalarDate.day

instance : LT ScalarDate where
  lt := InvImage Int.lt ScalarDate.day

theorem ScalarDate.le_def {d₁ d₂ : ScalarDate} : (d₁ <= d₂) = (d₁.day <= d₂.day) := rfl
theorem ScalarDate.lt_def {d₁ d₂ : ScalarDate} : (d₁ < d₂) = (d₁.day < d₂.day) := rfl

instance instDecidableLEScalarDate (d₁ d₂ : ScalarDate) : Decidable (d₁ <= d₂) := inferInstanceAs (Decidable (d₁.day <= d₂.day))
instance instDecidableLTScalarDate (d₁ d₂ : ScalarDate) : Decidable (d₁ < d₂) := inferInstanceAs (Decidable (d₁.day < d₂.day))

instance : LinearOrder ScalarDate where
  le_refl (a) := le_refl a.day
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le
  le_antisymm (a b h1 h2) := by
    apply ScalarDate.eq_of_val_eq
    exact le_antisymm h1 h2
  le_total := by simp [ScalarDate.le_def, le_total]
  decidable_le := inferInstance

instance : Ord ScalarDate := ⟨fun d₁ d₂ => compareOfLessAndEq d₁ d₂⟩

def Int.rataDie (scalarScalarDate : Int) : Int := Int.fmod scalarScalarDate 7

@[reducible, simp]
abbrev ScalarDate.dayOfWeek (d : ScalarDate) : Int := d.day.rataDie

abbrev sunday : Nat := 0
abbrev monday : Nat := 1
abbrev tuesday : Nat := 2
abbrev wednesday : Nat := 3
abbrev thursday : Nat := 4
abbrev friday : Nat := 5
abbrev saturday : Nat := 6

abbrev ScalarDate.isSunday (d : ScalarDate) : Bool := d.dayOfWeek = sunday
abbrev ScalarDate.isMonday (d : ScalarDate) : Bool := d.dayOfWeek = monday
abbrev ScalarDate.isTuesday (d : ScalarDate) : Bool := d.dayOfWeek = tuesday
abbrev ScalarDate.isWednesday (d : ScalarDate) : Bool := d.dayOfWeek = wednesday
abbrev ScalarDate.isThursday (d : ScalarDate) : Bool := d.dayOfWeek = thursday
abbrev ScalarDate.isFriday (d : ScalarDate) : Bool := d.dayOfWeek = friday
abbrev ScalarDate.isSaturday (d : ScalarDate) : Bool := d.dayOfWeek = saturday

def ScalarDate.addDays : ScalarDate → Nat → ScalarDate
| ⟨d⟩, ds => ⟨d + ds⟩

def ScalarDate.subDays : ScalarDate → Nat → ScalarDate
| ⟨d⟩, ds => ⟨d - ds⟩

instance : Inhabited ScalarDate where 
  default := ScalarDate.mk 0