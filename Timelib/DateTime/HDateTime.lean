import Timelib.DateTime.NaiveDateTime
import Timelib.DateTime.DateTime
import Timelib.Util
import Timelib.DateTime.TimeZone
import Timelib.DateTime.LeapSeconds

namespace Timelib

structure HDateTime where
  precision : Int
  leap : LeapSeconds
  zone : TimeZone
  val: DateTime precision leap zone

namespace HDateTime
section HDateTime

variable (t : HDateTime) {siPow : Int}

@[reducible]
def toNaiveLossless {p': Int} (d : HDateTime) (h : p' <= d.precision): NaiveDateTime p' :=
  d.val.toNaiveDateTime.convertLossless h

@[reducible]
def convertLossless {p': Int} (d : HDateTime) (h : p' <= d.precision) : { d' // (d' : HDateTime).precision = p' } :=
  ⟨{ d with precision := p', val := ⟨d.toNaiveLossless h⟩ }, by simp⟩

--@[reducible]
--def toNaiveLosslessMixed {p' : Int} (d : HDateTime) : NaiveDateTime (minLeft d.precision p') :=
--  d.val.toNaiveDateTime.convertLossless (fine := minLeft d.precision p') (coarse := d.precision) (minLeft_le _ _)

@[reducible]
def simultaneous : HDateTime → HDateTime → Prop
| ⟨p₁, _, _, ⟨naive₁⟩⟩, ⟨p₂, _, _, ⟨naive₂⟩⟩ =>
  (naive₁.convertLossless (min_le_left p₁ p₂)) = (naive₂.convertLossless (min_le_right p₁ p₂))

instance (h1 h2 : HDateTime) : Decidable (simultaneous h1 h2) := inferInstance

/--
LT compares the underlying naive DateTime.
-/
instance : LT HDateTime where
  lt a b := a.val.toNaiveDateTime.lt_het b.val.toNaiveDateTime

/--
LE compares the underlying naive DateTime
-/
instance : LE HDateTime where
  le a b := a.val.toNaiveDateTime.le_het b.val.toNaiveDateTime


@[simp] theorem le_def (d₁ d₂ : HDateTime) :
  (d₁ <= d₂) = (d₁.val.toNaiveDateTime.le_het d₂.val.toNaiveDateTime) := rfl

--theorem le_def' (d₁ d₂ : HDateTime) :
--  (d₁ <= d₂) =
--  ((d₁.toNaiveLossless (min_le_left d₁.precision d₂.precision)) <=
--  (d₂.toNaiveLossless (min_le_right d₁.precision d₂.precision))) := rfl

@[simp] theorem lt_def (d₁ d₂ : HDateTime) :
  (d₁ < d₂) = d₁.val.toNaiveDateTime.lt_het d₂.val.toNaiveDateTime := rfl

--theorem lt_def' (d₁ d₂ : HDateTime) :
--  (d₁ < d₂) =
--  (d₁.toNaiveLossless (min_le_left d₁.precision d₂.precision)
--  < (d₂.toNaiveLossless (min_le_right d₁.precision d₂.precision))) := rfl

instance instDecidableLEHDateTime (a b : HDateTime) : Decidable (a <= b) :=
  inferInstanceAs <| Decidable <| a.val.toNaiveDateTime.le_het b.val.toNaiveDateTime

instance instDecidableLTHDateTime (a b : HDateTime) : Decidable (a < b) :=
  inferInstanceAs <| Decidable <| a.val.toNaiveDateTime.lt_het b.val.toNaiveDateTime

instance : Preorder HDateTime where
  le_refl := fun _ =>
    by simp only [le_def, NaiveDateTime.le_het, SignedDuration.le_het, le_refl]
  le_trans := fun x y z => by
    simp only [le_def]
    exact NaiveDateTime.le_het_trans
      (p1 := x.precision)
      (p2 := y.precision)
      (p3 := z.precision)
      (x.val.toNaiveDateTime)
      (y.val.toNaiveDateTime)
      (z.val.toNaiveDateTime)
  lt_iff_le_not_le := fun a b => by
    have _ := NaiveDateTime.lt_het_iff_le_het_not_le_het
      a.val.toNaiveDateTime
      b.val.toNaiveDateTime
    simpa only [lt_def, le_def]
