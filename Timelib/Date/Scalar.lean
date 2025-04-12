namespace Timelib

/--
Represents a date in the proleptic Gregorian calendar as a single integer. The epoch
of the proleptic Gregorian calendar is 1 January of the year 1, it is *not* 0-based.

+ A positive value represents the number of days SINCE the epoch.

+ A negative value represents the number of days UNTIL the epoch.

For performance reasons, users should favor this type over e.g. Ymd
-/
@[ext]
structure ScalarDate where
  day : Int
deriving Repr, DecidableEq

namespace ScalarDate

instance : Inhabited ScalarDate where
  default := ScalarDate.mk 0

theorem val_eq_of_eq : ∀ {d₁ d₂ : ScalarDate} (_ : d₁ = d₂), d₁.day = d₂.day
| ⟨_⟩, _, rfl => rfl

theorem eq_of_val_eq : ∀ {d₁ d₂ : ScalarDate} (_ : d₁.day = d₂.day), d₁ = d₂
| ⟨_⟩, _, rfl => rfl

theorem ne_of_val_ne : ∀ {d₁ d₂ : ScalarDate} (_ : d₁.day ≠ d₂.day), d₁ ≠ d₂
| ⟨_⟩, _, ne => fun a => ne (congrArg day a)

instance instLE : LE ScalarDate where
  le := InvImage Int.le ScalarDate.day

instance instLT : LT ScalarDate where
  lt := InvImage Int.lt ScalarDate.day

theorem le_def {d₁ d₂ : ScalarDate} : (d₁ <= d₂) = (d₁.day <= d₂.day) := rfl
theorem lt_def {d₁ d₂ : ScalarDate} : (d₁ < d₂) = (d₁.day < d₂.day) := rfl

instance instDecidableLEScalarDate (d₁ d₂ : ScalarDate) : Decidable (d₁ <= d₂) := inferInstanceAs (Decidable (d₁.day <= d₂.day))
instance instDecidableLTScalarDate (d₁ d₂ : ScalarDate) : Decidable (d₁ < d₂) := inferInstanceAs (Decidable (d₁.day < d₂.day))

instance instOrd : Ord ScalarDate := ⟨fun d₁ d₂ => compareOfLessAndEq d₁ d₂⟩

theorem le_refl (d : ScalarDate) : d ≤ d := by simp only [le_def, Int.le_refl]

theorem lt_or_eq_of_le {d₁ d₂ : ScalarDate} : d₁ <= d₂ → d₁ < d₂ ∨ d₁ = d₂ :=
  fun hle =>
    if h : d₁ = d₂
    then .inr ‹_›
    else by
      have hne : d₁.day ≠ d₂.day := fun he => h (eq_of_val_eq he)
      have h' := Int.lt_iff_le_and_ne.mpr ⟨hle, hne⟩
      simp [lt_def, h']

def rataDie (scalarDateDay : Int) : Int := Int.fmod scalarDateDay 7

abbrev dayOfWeek (d : ScalarDate) : Int := rataDie d.day

abbrev sunday : Nat := 0
abbrev monday : Nat := 1
abbrev tuesday : Nat := 2
abbrev wednesday : Nat := 3
abbrev thursday : Nat := 4
abbrev friday : Nat := 5
abbrev saturday : Nat := 6

abbrev isSunday (d : ScalarDate) : Bool := d.dayOfWeek = sunday
abbrev isMonday (d : ScalarDate) : Bool := d.dayOfWeek = monday
abbrev isTuesday (d : ScalarDate) : Bool := d.dayOfWeek = tuesday
abbrev isWednesday (d : ScalarDate) : Bool := d.dayOfWeek = wednesday
abbrev isThursday (d : ScalarDate) : Bool := d.dayOfWeek = thursday
abbrev isFriday (d : ScalarDate) : Bool := d.dayOfWeek = friday
abbrev isSaturday (d : ScalarDate) : Bool := d.dayOfWeek = saturday

def addDays : ScalarDate → Nat → ScalarDate
| ⟨d⟩, ds => ⟨d + ds⟩

def subDays : ScalarDate → Nat → ScalarDate
| ⟨d⟩, ds => ⟨d - ds⟩
