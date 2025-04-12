import Timelib.Duration.SignedDuration

namespace Timelib.SignedDuration

section durations

variable {siPow : Int} (siPow_le : siPow ≤ 0 := by smesh)

def oneSecond : SignedDuration siPow := (⟨1⟩ : SignedDuration 0).convertLossless siPow_le
def oneMinute : SignedDuration siPow := (⟨60⟩ : SignedDuration 0).convertLossless siPow_le
def oneHour : SignedDuration siPow := (⟨3600⟩ : SignedDuration 0).convertLossless siPow_le
def oneDay : SignedDuration siPow := (⟨86400⟩ : SignedDuration 0).convertLossless siPow_le
def oneWeek : SignedDuration siPow := (⟨604800⟩ : SignedDuration 0).convertLossless siPow_le
def oneYearNonleap : SignedDuration siPow := (⟨31536000⟩ : SignedDuration 0).convertLossless siPow_le
def oneYearLeap : SignedDuration siPow := (⟨31622400⟩ : SignedDuration 0).convertLossless siPow_le

theorem oneMinute_eq : oneMinute = oneSecond * (60 : Int) := by
  simp only [oneMinute, convertLossless, Int.zero_sub, Int.natAbs_neg, Int.mul_comm, oneSecond,
    Int.one_mul, hMul_def]

theorem oneHour_eq : oneHour = oneMinute * (60 : Int) := by
  simp only [oneHour, convertLossless, Int.zero_sub, Int.natAbs_neg, oneMinute, hMul_def, mk.injEq]
  omega

theorem oneDay_eq : oneDay = oneHour * (24 : Int) := by
  simp only [oneDay, oneHour, convertLossless, Int.zero_sub, Int.natAbs_neg, oneMinute, hMul_def, mk.injEq]
  omega

theorem oneWeek_eq : oneWeek = oneDay * (7 : Int) := by
  simp only [oneWeek, oneDay, convertLossless, Int.zero_sub, Int.natAbs_neg, oneMinute, hMul_def, mk.injEq]
  omega

theorem oneYearNonleap_eq : oneYearNonleap = oneDay * (365 : Int) := by
  simp only [oneYearNonleap, oneDay, convertLossless, Int.zero_sub, Int.natAbs_neg, oneMinute, hMul_def, mk.injEq]
  omega

theorem oneYearLeap_eq : oneYearLeap = oneDay * (366 : Int) := by
  simp only [oneYearLeap, oneDay, convertLossless, Int.zero_sub, Int.natAbs_neg, oneMinute, hMul_def, mk.injEq]
  omega

end durations

theorem zero_le_oneDay
  {p : Int}
  (isLe : p <= 0) :
  0 <= (oneDay isLe).val := by
  let rec zero_lt_10_pow : (p : Nat) → 0 < (10 : Int) ^ p
    | 0 => by simp
    | p+1 => by have ih := zero_lt_10_pow p; omega
  simp only [oneDay, convertLossless]
  apply Int.le_of_lt
  refine Int.mul_pos ?ha ?hb
  case ha => decide
  case hb => simp [zero_lt_10_pow p.natAbs]
