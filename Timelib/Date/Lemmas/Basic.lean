import Mathlib.Data.Nat.Basic
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Int.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Equiv.Basic
import Mathlib.Init.Data.Int.Order
import Timelib.Date.Year
import Timelib.Date.Month
import Timelib.Date.ScalarDate
import Timelib.Date.OrdinalDate
import Timelib.Date.Ymd
import Timelib.Date.Convert
import Timelib.Util
import Timelib.Date.Lemmas.YmdOrdinalEquiv

instance : Equiv Ymd OrdinalDate where
  toFun := Ymd.toOrdinalDate
  invFun := OrdinalDate.toYmd
  left_inv := Ymd.toOrdinalDate_left_inv
  right_inv := OrdinalDate.toYmd_right_inv

instance : Equiv OrdinalDate ScalarDate where
  toFun := OrdinalDate.toScalarDate
  invFun := ScalarDate.toOrdinalDate
  left_inv := sorry
  right_inv := sorry

instance : Equiv Ymd ScalarDate := 
  Equiv.trans instEquivYmdOrdinalDate instEquivOrdinalDateScalarDate

theorem OrdinalDate.toYmd_monotonic {ω π : OrdinalDate} : ω <= π → ω.toYmd <= π.toYmd := sorry

theorem Ymd.toOrdinalDate_monotonic {d₁ d₂ : Ymd} : d₁ <= d₂ → d₁.toOrdinalDate <= d₂.toOrdinalDate := sorry

theorem OrdinalDate.toScalarDate_monotonic {ω π : OrdinalDate} : ω <= π → ω.toScalarDate <= π.toScalarDate := sorry

theorem ScalarDate.toOrdinalDate_monotonic {d1 d2 : ScalarDate} : d1 <= d2 → d1.toOrdinalDate <= d2.toOrdinalDate := sorry

theorem Ymd.toScalarDate_monotonic {y1 y2 : Ymd} : y1 <= y2 → y1.toScalarDate <= y2.toScalarDate := 
  OrdinalDate.toScalarDate_monotonic ∘ Ymd.toOrdinalDate_monotonic

theorem ScalarDate.toYmd_monotonic {d1 d2 : ScalarDate} : d1 <= d2 → d1.toYmd <= d2.toYmd :=
  OrdinalDate.toYmd_monotonic ∘ ScalarDate.toOrdinalDate_monotonic
