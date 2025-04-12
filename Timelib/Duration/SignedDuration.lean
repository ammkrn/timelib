import Timelib.Util
import Timelib.Duration.Units

namespace Timelib

/--
A signed duration indexed by the applicable [SI unit](https://en.wikipedia.org/wiki/Second#SI_multiples),
representing some quantity of `10 ^ siPow` units of time. For example:

`SignedDuration 0`  := seconds
`SignedDuration -4` := milliseconds
`SignedDuration -9` := nanoseconds
`SignedDuration 3`  := kiloseconds
-/
@[ext]
structure SignedDuration (siPow : Int) where
  val : Int
deriving DecidableEq, Hashable

namespace SignedDuration

section base
variable {siPow : Int}

def ofSeconds (val : Int) : SignedDuration siPow := ⟨val⟩
def ofNatSeconds (val : Nat) : SignedDuration siPow := ⟨Int.ofNat val⟩


instance instInhabited : Inhabited (SignedDuration siPow) where
  default := ⟨0⟩

theorem default_def : (Inhabited.default : SignedDuration siPow) = ⟨0⟩ := rfl

/--
It's fine that this implicates an `ofNat` for `0` because siPow doesn't
matter for 0 values
-/
instance instZero : Zero (SignedDuration siPow) where
  zero := ⟨0⟩

theorem zero_def : (Zero.zero : SignedDuration siPow) = ⟨0⟩ := rfl

def isNeg (d : SignedDuration siPow) : Bool := d.val < 0

def isNonNeg (d : SignedDuration siPow) : Bool := ¬d.isNeg

def abs (d : SignedDuration siPow) : SignedDuration siPow := ⟨d.val.natAbs⟩

theorem abs_def (d : SignedDuration siPow) : d.abs = ⟨d.val.natAbs⟩ := rfl

instance : Neg (SignedDuration siPow) where
  neg d := ⟨-d.val⟩

theorem neg_def (d : SignedDuration siPow) : -d = ⟨-d.val⟩ := by rfl

instance : Add (SignedDuration siPow) where
  add a b := ⟨a.val + b.val⟩

theorem add_def (a b : SignedDuration siPow) : a + b = ⟨a.val + b.val⟩ := rfl

instance : Sub (SignedDuration siPow) where
  sub a b := ⟨a.val - b.val⟩

theorem sub_def (a b :  SignedDuration siPow) : a - b = ⟨a.val - b.val⟩ := rfl

instance instHMulR : HMul (SignedDuration siPow) Int (SignedDuration siPow) where
  hMul d n := ⟨d.val * n⟩

--instance instHMulL : HMul Int (SignedDuration siPow) (SignedDuration siPow) where
--  hMul n d := ⟨n * d.val⟩
--
--theorem hMul_comm (a :  SignedDuration siPow) (b : Int) : a * b = b * a := by
--  simp only [instHMulR, instHMulL, Int.mul_comm]

theorem hMul_def (a :  SignedDuration siPow) (b : Int) : a * b = ⟨a.val * b⟩ := rfl

instance : HMod (SignedDuration siPow) Int (SignedDuration siPow) where
  hMod a n := ⟨a.val % n⟩

theorem hMod_def (a : SignedDuration siPow) (b : Int) : a % b = ⟨a.val % b⟩ := by
  rfl

instance : HDiv (SignedDuration siPow) Nat (SignedDuration siPow) where
  hDiv a b := ⟨a.val / b⟩

theorem hDiv_def (a : SignedDuration siPow) (b : Nat) : a / b = ⟨a.val / b⟩ := by
  rfl

instance : HPow (SignedDuration siPow) Nat (SignedDuration siPow) where
  hPow a b := ⟨a.val ^ b⟩

instance instLT : LT (SignedDuration siPow) where
  lt := InvImage Int.lt SignedDuration.val

instance instLE : LE (SignedDuration siPow) where
  le := InvImage Int.le SignedDuration.val

theorem le_def {d₁ d₂ : SignedDuration siPow} : (d₁ <= d₂) = (d₁.val <= d₂.val) := rfl
theorem lt_def {d₁ d₂ : SignedDuration siPow} : (d₁ < d₂) = (d₁.val < d₂.val) := rfl

theorem val_eq_of_eq : {d1 d2 : SignedDuration siPow} → d1 = d2 → d1.val = d2.val
| ⟨_⟩, _, rfl => rfl

theorem eq_of_val_eq : {d1 d2 : SignedDuration siPow} → d1.val = d2.val → d1 = d2
| ⟨_⟩, _, rfl => rfl

theorem eq_def {d₁ d₂ : SignedDuration siPow} :
  (d₁ = d₂) ↔ (d₁.val = d₂.val)
:= ⟨val_eq_of_eq, eq_of_val_eq⟩

instance (a b : SignedDuration siPow) : Decidable (a < b) := inferInstanceAs (Decidable (a.val < b.val))
instance (a b : SignedDuration siPow) : Decidable (a <= b) := inferInstanceAs (Decidable (a.val <= b.val))

instance : Ord (SignedDuration siPow) where
  compare a b := compareOfLessAndEq a b

theorem monotone {d₁ d₂ : SignedDuration siPow} : d₁.val <= d₂.val → d₁ <= d₂
  | h => (le_def) ▸ h

theorem zero_def_ : (Zero.zero : SignedDuration siPow) = ⟨(0 : Int)⟩ := by rfl
--theorem one_def_ : (One.one : SignedDuration siPow) = ⟨(1 : Int)⟩ := by rfl

@[simp] theorem zero_val_def : (0 : SignedDuration siPow).val = (0 : Int) := by rfl
--@[simp] theorem one_val_def : (1 : SignedDuration siPow).val = (1 : Int) := by rfl


theorem sub_eq_add_neg (a b : SignedDuration siPow) : a - b = a + -b := by
  simp only [HSub.hSub, Sub.sub, Int.sub, neg_def, add_def]

theorem neg_add_cancel_right (a b : SignedDuration siPow) : a + -b + b = a := by
  simp only [add_def]
  apply eq_of_val_eq
  exact Int.neg_add_cancel_right a.val b.val

theorem add_sub_cancel (a b : SignedDuration siPow) : a + b - b = a := by
  simp only [add_def]
  apply eq_of_val_eq
  exact Int.add_sub_cancel a.val b.val

theorem add_left_neg (a : SignedDuration siPow) : -a + a = 0 := by
  apply eq_of_val_eq
  simp only [sub_def, add_def, neg_def]
  exact Int.add_left_neg a.val

theorem add_zero : ∀ (a : SignedDuration siPow), a + 0 = a := by
    simp only [add_def, zero_val_def, Int.add_zero, forall_const]

theorem sub_zero : ∀ (a : SignedDuration siPow), a - 0 = a := by
    simp only [sub_def, zero_val_def, Int.sub_zero, forall_const]

theorem zero_add : ∀ (a : SignedDuration siPow), 0 + a = a := by
    simp only [add_def, zero_val_def, Int.zero_add, forall_const]

theorem add_assoc (a b c : SignedDuration siPow) : a + b + c = a + (b + c) := by
  simp [add_def, Int.add_assoc]

instance instMinSignedDuration : Min (SignedDuration siPow) := minOfLe

theorem min_def (l r : SignedDuration siPow) : Min.min l r = (if l ≤ r then l else r) := by
  unfold Min.min
  simp [instMinSignedDuration, minOfLe]

theorem le_refl (l : SignedDuration siPow) : l ≤ l := by simp [SignedDuration.le_def]; done

theorem ne_of_not_le {l r : SignedDuration siPow} : ¬(l ≤ r) → l ≠ r := by
  intro hf hff
  exact False.elim ((hff ▸ hf) (le_refl r))

theorem min_eq_iff {l r : SignedDuration siPow} : (Min.min l r = l) ↔ l ≤ r := by
  refine Iff.intro ?mp ?mpr
  case mp =>
    simp only [min_def]
    by_cases hle : l ≤ r
    case pos => simp [hle]
    case neg =>
      have hf := (ne_of_not_le hle).symm
      simp [hle, hf]
      done
  case mpr =>
    intro hle
    simp [min_def, hle]
    done

/--
Absolute difference
-/
def absDiff (d₁ d₂ : SignedDuration siPow) : SignedDuration siPow :=
  (d₁ - d₂).abs

end base

set_option linter.unusedVariables.funArgs false in
def convertLossless
  {fine coarse : Int}
  (d : SignedDuration coarse)
  (siPowLe : fine <= coarse := by smesh) :
  SignedDuration fine :=
    ⟨d.val * (10 ^ (coarse - fine).natAbs)⟩

/--
Convert e.g. (6000 : SignedDuration 0) to (6 : SignedDuration 3) by providing
evidence that ∃ c, 6000 = 6 * c

10 ^ (coarse - fine) * output = original
-/
def convertLossless'
  {fine coarse : Int}
  (d : SignedDuration fine) :
  (coarse ≥ fine) →
  (10 ^ (coarse - fine).natAbs ∣ d.val) → SignedDuration coarse :=
   fun _ _ => ⟨d.val.ediv (10 ^ (coarse - fine).natAbs)⟩

/--
"upward" conversion is indeed lossless
-/
theorem convertLossless'_eq
  {fine coarse : Int}
  (d : SignedDuration fine)
  (hle : fine ≤ coarse)
  (hdvd : 10 ^ (coarse - fine).natAbs ∣ d.val) :
  (convertLossless' d hle hdvd).convertLossless hle = d := by
  apply SignedDuration.eq_of_val_eq
  exact Int.ediv_mul_cancel hdvd

/--
Lossy conversion using the `e` rounding convention
-/
def eConvertLossy
  {fine coarse : Int}
  (d : SignedDuration fine)
  (_ : fine <= coarse := by decide) : SignedDuration coarse :=
   ⟨d.val.ediv (10 ^ (coarse - fine).natAbs)⟩

/--
Lossy conversion using the `f` rounding convention
-/
def fConvertLossy
  {fine coarse : Int}
  (d : SignedDuration fine)
  (_ : fine <= coarse := by decide) : SignedDuration coarse :=
   ⟨d.val.fdiv (10 ^ (coarse - fine).natAbs)⟩

/-
I think this is pretty rarely going to work as expected, so this is an experiment.
There are more complex strategies that can be tried with different versions of `Coe`
-/
instance {n : Int} : Coe (SignedDuration n) (SignedDuration (n - 1)) where
  coe d := SignedDuration.convertLossless d (Int.sub_le_self n (Int.ofNat_zero_le _))

instance {n : Int} {m : Nat} : Coe (SignedDuration n) (SignedDuration (n - m)) where
  coe d := SignedDuration.convertLossless d (Int.sub_le_self n (Int.ofNat_zero_le _))

end SignedDuration

namespace SignedDuration
def eq_het {p1 p2 : Int} (d1 : SignedDuration p1) (d2 : SignedDuration p2) : Prop :=
  (d1.convertLossless (Int.min_le_left _ _) : SignedDuration (min p1 p2)).val
  = (d2.convertLossless (Int.min_le_right _ _) : SignedDuration (min p1 p2)).val

def le_het {p1 p2 : Int} (d1 : SignedDuration p1) (d2 : SignedDuration p2) : Prop :=
  (d1.convertLossless (Int.min_le_left _ _) : SignedDuration (min p1 p2)).val
  <= (d2.convertLossless (Int.min_le_right _ _) : SignedDuration (min p1 p2)).val

def lt_het {p1 p2 : Int} (d1 : SignedDuration p1) (d2 : SignedDuration p2) : Prop :=
  (d1.convertLossless (Int.min_le_left _ _) : SignedDuration (min p1 p2)).val
  < (d2.convertLossless (Int.min_le_right _ _) : SignedDuration (min p1 p2)).val

instance instDecidableEqHet {p1 p2 : Int} (d1 : SignedDuration p1) (d2 : SignedDuration p2) :
  Decidable (eq_het d1 d2)
:= inferInstanceAs <| Decidable <|
  (d1.convertLossless (Int.min_le_left _ _) : SignedDuration (min p1 p2)).val
  = (d2.convertLossless (Int.min_le_right _ _) : SignedDuration (min p1 p2)).val

instance instDecidableLEHet {p1 p2 : Int} (d1 : SignedDuration p1) (d2 : SignedDuration p2) :
  Decidable (le_het d1 d2)
:= inferInstanceAs <| Decidable <|
  (d1.convertLossless (Int.min_le_left _ _) : SignedDuration (min p1 p2)).val
  <= (d2.convertLossless (Int.min_le_right _ _) : SignedDuration (min p1 p2)).val

instance instDecidableLTHet {p1 p2 : Int} (d1 : SignedDuration p1) (d2 : SignedDuration p2) :
  Decidable (lt_het d1 d2)
:= inferInstanceAs <| Decidable <|
  (d1.convertLossless (Int.min_le_left _ _) : SignedDuration (min p1 p2)).val
  < (d2.convertLossless (Int.min_le_right _ _) : SignedDuration (min p1 p2)).val

end SignedDuration

theorem toString_IntNat_eq (x : Nat) : ToString.toString (↑x : Int) = ToString.toString x := by
  simp [ToString.toString]

def toSecondsString {siPow : Int} (d : SignedDuration siPow) : String :=
  if _ : siPow ≥ 0
  then
    s!"{(d.convertLossless : SignedDuration 0).val}.0 s"
  else
    let chars := s!"{d.val}".toList
    ⟨chars.insertIdx (chars.length - siPow.natAbs) '.'⟩ ++ " s"

instance (siPow : Int) : Repr (SignedDuration siPow) where
  reprPrec x _ := toSecondsString x

instance (siPow : Int) : ToString (SignedDuration siPow) where
  toString x := toSecondsString x


--open Lean Elab Term Meta
--
--/--
--Defining notation and suffixes for durations of time; the motivation for this
--is to move away from the admittedly convenient `ofNat` instances in order to
--prevent confusion of e.g. 1000 being 1000 seconds or 1000 milliseconds, etc.
--
--The other option is to just force use of type annotations, e.g.
--
--`(⟨1000⟩ : SignedDuration -3)` = `#SignedDuration 1000 ms`
---/
--syntax (name := parseSignedDuration) "#SignedDuration" term duration_unit : term
--
--@[term_elab parseSignedDuration] def expandSignedDuration : TermElab
--  | `(#SignedDuration $d:term $u:duration_unit), _ => do
--    let val ← elabTerm d (some (.const `Int []))
--    let siPow ← expandSiUnit u none
--    mkAppOptM ``Timelib.SignedDuration.mk #[some siPow, some val]
--  | _, _ => throwError ""
--
--
--#eval (#SignedDuration 1000 microseconds)
--#eval (#SignedDuration -1000 μs)
--#eval (#SignedDuration 23 Qs)
--#eval (#SignedDuration 23 s)
--#eval (#SignedDuration 23 seconds)
