import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Basic
import Mathlib.Data.String.Defs
import Mathlib.Data.String.Lemmas
import Mathlib.Data.Equiv.Basic
import Timelib.Util
import Timelib.NanoPrecision.Duration.SignedDuration
import Timelib.NanoPrecision.Duration.UnsignedDuration
import Timelib.NanoPrecision.DateTime.NaiveDateTime
import Timelib.NanoPrecision.DateTime.DateTime
import Timelib.NanoPrecision.TimeZone.Basic

structure HDateTime where
  offset : Offset
  dateTime : DateTime offset

def HDateTime.EquivSigma : Equiv HDateTime (Sigma DateTime) := {
  toFun := fun dt => ⟨dt.offset, dt.dateTime⟩ 
  invFun := fun sig => ⟨sig.fst, sig.snd⟩
  left_inv := by simp [Function.LeftInverse]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse]
}

section HDateTimeStuff

variable (t : HDateTime)

/- Show that this is an equivalence relation -/
@[reducible]
def HDateTime.simultaneous : HDateTime → HDateTime → Prop
| ⟨_, ⟨naive_dt₁⟩⟩, ⟨_, ⟨naive_dt₂⟩⟩ => naive_dt₁ = naive_dt₂

def HDateTime.simultaneous.equivalence : Equivalence HDateTime.simultaneous :=  {
  refl := fun d => rfl
  symm := fun h => h.symm
  trans := fun h h' => Eq.trans h h'
}

instance instHDateTimeSetoid : Setoid HDateTime := 
  ⟨HDateTime.simultaneous, HDateTime.simultaneous.equivalence⟩

/--
LT compares the underlying naive DateTime.
-/
instance : LT HDateTime where
  lt := InvImage instLTNaiveDateTime.lt (fun t => t.dateTime.naive)

/--
LE compares the underlying naive DateTime
-/
instance : LE HDateTime where
  le := InvImage instLENaiveDateTime.le (fun t => t.dateTime.naive)

@[simp] theorem HDateTime.le_def (d₁ d₂ : HDateTime) : (d₁ <= d₂) = (d₁.dateTime.naive <= d₂.dateTime.naive) := rfl
@[simp] theorem HDateTime.lt_def (d₁ d₂ : HDateTime) : (d₁ < d₂) = (d₁.dateTime.naive < d₂.dateTime.naive) := rfl

instance instDecidableLTHDateTime (a b : HDateTime) : Decidable (a < b) := inferInstanceAs (Decidable (a.dateTime.naive < b.dateTime.naive))
instance instDecidableLEHDateTime (a b : HDateTime) : Decidable (a <= b) := inferInstanceAs (Decidable (a.dateTime.naive <= b.dateTime.naive))

/--
HDateTime is only a Preorder since it does not respect antisymmetry. 
t₁ <= t₂ ∧ t₂ <= t₁ does not imply t₁ = t₂ since they may have different offets/timezones.
-/
instance : Preorder HDateTime where
  le_refl (a) := le_refl a.dateTime.naive
  le_trans (a b c) := Int.le_trans
  lt_iff_le_not_le (a b) := Int.lt_iff_le_not_le

instance : HAdd HDateTime SignedDuration HDateTime where
  hAdd da du := ⟨da.offset, da.dateTime + du⟩

instance : HAdd SignedDuration HDateTime HDateTime  where
  hAdd du da := da + du

theorem HDateTime.hAdd_def (d : HDateTime) (dur : SignedDuration) : d + dur = ⟨d.offset, d.dateTime  + dur⟩ := rfl

instance : HSub HDateTime SignedDuration HDateTime where
  hSub da du := ⟨da.offset, da.dateTime + -du⟩ 

theorem HDateTime.hSub_def (d : HDateTime) (dur : SignedDuration) : d - dur = ⟨d.offset, d.dateTime + -dur⟩ := rfl

instance : HAdd HDateTime UnsignedDuration HDateTime where
  hAdd da du := ⟨da.offset, da.dateTime + du⟩

instance : HAdd UnsignedDuration HDateTime HDateTime  where
  hAdd du da := da + du

theorem HDateTime.hAdd_def_unsigned (d : HDateTime) (dur : UnsignedDuration) : d + dur = ⟨d.offset, d.dateTime + dur⟩ := rfl

instance : HSub HDateTime UnsignedDuration HDateTime where
  hSub da du := ⟨da.offset, da.dateTime - du⟩ 

theorem HDateTime.hSub_def_unsigned (d : HDateTime) (dur : UnsignedDuration) : d - dur = ⟨d.offset, d.dateTime - dur⟩ := rfl
