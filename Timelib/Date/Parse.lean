import Timelib.Date.Month

theorem isDigit_iff {c : Char} : c.isDigit ↔ (48 <= c.val ∧ c.val <= 57) :=
  Iff.intro
  (by simp only [Char.isDigit, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq, and_imp]; exact And.intro)
  (by simp only [Char.isDigit, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq, imp_self])

theorem isDigit_toNat_iff {c : Char} : c.isDigit ↔ (48 <= c.toNat ∧ c.toNat <= 57) :=
  Iff.intro
  (by simp only [Char.isDigit, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq, and_imp]; exact And.intro)
  (by simp only [Char.isDigit, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq, and_imp]; exact And.intro)

abbrev Char.decimalDigit (c : Char) : Nat := (c.val - 48).toNat

theorem Char.decimalDigit_eq {c : Char} (h : c.isDigit) : c.decimalDigit = (c.toNat - 48) :=
  UInt32.toNat_sub_of_le c.val '0'.val (isDigit_toNat_iff.mp h).left

theorem sub_toNat_eq_toNat_sub_of_isDigit {c : Char} (h : c.isDigit) : (c.val - 48).toNat = (c.toNat - 48) :=
  UInt32.toNat_sub_of_le c.val '0'.val (isDigit_toNat_iff.mp h).left

theorem Char.lt_10_of_isDigit {c : Char} : c.isDigit → c.toNat - 48 < 10 := by
  intro _; have _ := isDigit_toNat_iff.mp ‹_›; omega

theorem and_elim_left : ∀ {a b : Bool}, a && b → a := by decide
theorem and_elim_right : ∀ {a b : Bool}, a && b → b := by decide

namespace Timelib

theorem digitDrop (xs : List Char) : xs.all (Char.isDigit) → xs.dropLast.all (Char.isDigit) := by
  intro h
  have x := List.dropLast_prefix xs
  match x with
  | ⟨t, ht⟩ =>
    have h' := ht ▸ h
    have zz := List.all_append (xs := xs.dropLast) (ys := t) (f := Char.isDigit)
    rw [zz] at h'
    have and_elim_left : ∀ {a b : Bool}, a && b → a := by decide
    exact and_elim_left h'

theorem digitGet (xs : List Char) : xs.all (Char.isDigit) → (hnil : xs ≠ []) → (xs.getLast hnil).isDigit := by
  intro hall hnil
  simp [List.all] at hall
  exact hall (xs.getLast hnil) (List.getLast_mem hnil)

theorem mod_10_eq (n : Nat) : (n % 10).digitChar.toNat - 48 = (n % 10) :=
  match h: n % 10 with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => by simp [Nat.digitChar]
  | _+10 => by omega

def parseChar (c : Char) : Option Nat := if c.isDigit then some (c.toNat - 48) else none

theorem parseCharOkMatch : (c : Char) → c.isDigit → ((parseChar c).map (Nat.digitChar) = some c)
  | ⟨⟨48⟩, _⟩, h | ⟨⟨49⟩, _⟩, h | ⟨⟨50⟩, _⟩, h | ⟨⟨51⟩, _⟩, h
  | ⟨⟨52⟩, _⟩, h | ⟨⟨53⟩, _⟩, h | ⟨⟨54⟩, _⟩, h | ⟨⟨55⟩, _⟩, h
  | ⟨⟨56⟩, _⟩, h | ⟨⟨57⟩, _⟩, h => by
    simp only [parseChar, Char.isDigit, BitVec.ofNat_eq_ofNat, UInt32.ofBitVec_ofNat, UInt32.instOfNat,
      UInt32.reduceOfNat, ge_iff_le, UInt32.reduceLE, decide_true, Bool.and_self, ↓reduceIte,
      Char.toNat, UInt32.toNat, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub,
      Option.map_some', Nat.digitChar, Nat.add_one_ne_zero, Nat.reduceEqDiff, ↓Char.isValue,
      Option.some.injEq]
    apply Char.eq_of_val_eq
    simp only [↓Char.isValue, Char.reduceVal]
  | ⟨⟨0⟩, _⟩, h => by dsimp [Char.isDigit] at h; cases h

theorem parseCharOkMatch' : {c : Char} → c.isDigit → ((c.toNat - '0'.toNat) % 10).digitChar = c
  | ⟨⟨48⟩, _⟩, h | ⟨⟨49⟩, _⟩, h | ⟨⟨50⟩, _⟩, h | ⟨⟨51⟩, _⟩, h
  | ⟨⟨52⟩, _⟩, h | ⟨⟨53⟩, _⟩, h | ⟨⟨54⟩, _⟩, h | ⟨⟨55⟩, _⟩, h
  | ⟨⟨56⟩, _⟩, h | ⟨⟨57⟩, _⟩, h => by
    simp [Nat.digitChar, OfNat.ofNat, Char.toNat]
    rfl

theorem parseCharOkMatch2 : {c : Char} → c.isDigit → (c.toNat - '0'.toNat).digitChar = c := by
  intro c hDigit
  have heq : (c.toNat - '0'.toNat) % 10 = (c.toNat - '0'.toNat) := by
    have _ := Char.lt_10_of_isDigit hDigit
    simp only [↓Char.isValue, Char.reduceToNat]
    omega
  exact heq ▸ (parseCharOkMatch' hDigit)

theorem div10_eq_zero_of_isDigit : {hd : Char} → hd.isDigit → ((hd.toNat - 48) / 10) = 0
  | ⟨⟨48⟩, _⟩, h | ⟨⟨49⟩, _⟩, h | ⟨⟨50⟩, _⟩, h | ⟨⟨51⟩, _⟩, h
  | ⟨⟨52⟩, _⟩, h | ⟨⟨53⟩, _⟩, h | ⟨⟨54⟩, _⟩, h | ⟨⟨55⟩, _⟩, h
  | ⟨⟨56⟩, _⟩, h | ⟨⟨57⟩, _⟩, h => by simp [Char.toNat, UInt32.toNat]

theorem printOk : (n : Nat) → 0 <= n → n <= 9 → parseChar n.digitChar = some n
  | 0, hge, hle | 1, hge, hle | 2, hge, hle | 3, hge, hle
  | 4, hge, hle | 5, hge, hle | 6, hge, hle | 7, hge, hle
  | 8, hge, hle | 9, hge, hle => by simp [Nat.digitChar, parseChar]
  | _+10, hge, hle => by omega


abbrev foldlOp : Nat → Char → Nat :=
  fun sink c => (10 * sink) + (c.toNat - '0'.toNat)

@[reducible]
def parseFoldl (xs : List Char) := xs.foldl foldlOp (init := 0)

def parseRev (xs : List Char) : Nat :=
  if h : xs = []
  then 0
  else
    (10 * (parseRev xs.dropLast)) + ((xs.getLast h).toNat - '0'.toNat)
termination_by xs.length
decreasing_by
  . rw [xs.length_dropLast]; have _: xs.length > 0 := List.length_pos_iff.mpr ‹_›; omega

@[csimp]
theorem parsers_eq : parseRev = parseFoldl :=
  let rec aux (xs : List Char) :=
    match xs with
    | [] => by simp [parseFoldl, foldlOp, parseRev]
    | hd :: tl => by
      have hx := List.foldl_append (f := foldlOp) (b := 0) (l := (hd :: tl).dropLast) (l' := [(hd :: tl).getLast (by simp)])
      have h_app : (hd :: tl).dropLast ++ [(hd :: tl).getLast (by simp)] = hd :: tl := by
        simp only [List.dropLast_concat_getLast]
      have hy := h_app ▸ hx
      have ih := aux (hd :: tl).dropLast
      unfold parseRev
      simp only [Char.decimalDigit, sub_toNat_eq_toNat_sub_of_isDigit, List.foldl_cons, foldlOp, Nat.mul_zero, ↓Char.isValue, Char.reduceToNat,
        Nat.zero_add, List.foldl_nil] at hy
      simp only [reduceCtorEq, ↓reduceDIte, ih, ↓Char.isValue, Char.reduceToNat, parseFoldl,
        List.foldl_cons, foldlOp, Nat.mul_zero, Nat.zero_add, hy]
  termination_by xs.length
  funext aux


theorem parseRev_lt (xs : List Char) (hall : xs.all Char.isDigit) : (parseRev xs) < (10 ^ xs.length) :=
  if hnil : xs = []
  then by simp [parseRev, hnil]
  else by
    unfold parseRev
    simp only [hnil, ↓reduceDIte, ↓Char.isValue, Char.reduceToNat]
    have hnonzero : 0 < xs.length := List.length_pos_iff.mpr hnil
    have hlt : (xs.getLast hnil).toNat - 48 < 10 := (xs.getLast hnil).lt_10_of_isDigit (digitGet xs hall hnil)
    have ih := xs.length_dropLast ▸ parseRev_lt xs.dropLast (digitDrop xs hall)
    have hh' : 10 * 10 ^ (xs.length - 1) = 10 ^ (xs.length) := by
      have hsucc : xs.length = (xs.length - 1) + 1 := by omega
      conv =>
        rhs
        rw [hsucc]
      omega
    omega
termination_by xs.length
decreasing_by
  . rw [xs.length_dropLast]; have _: xs.length > 0 := List.length_pos_iff.mpr ‹_›; omega


theorem parseFoldl_lt : (xs : List Char) → xs.all Char.isDigit → (parseFoldl xs) < (10 ^ xs.length) := by
  rw [← parsers_eq]; exact parseRev_lt

def parseFoldl_s (s : String) := parseFoldl s.data

@[reducible]
def printNumberAux (n : Nat) : List Char :=
  if n = 0 then [] else printNumberAux (n / 10) ++ [(n % 10).digitChar]

theorem printNumberAux_digits(n : Nat) : (printNumberAux n).all Char.isDigit :=
  let digit1 : {n : Nat} → n ≤ 9 → n.digitChar.isDigit
    | 0, hle | 1, hle | 2, hle | 3, hle
    | 4, hle | 5, hle | 6, hle | 7, hle
    | 8, hle | 9, hle => by simp [Nat.digitChar, parseChar]
    | _+10, hle => by omega
  let h2 : [(n % 10).digitChar].all Char.isDigit = true := by
    have hle : n % 10 < 10 := Nat.mod_lt n (show 0 < 10 by decide)
    have h1 := digit1 (Nat.le_pred_of_lt hle)
    simp only [List.all_cons, h1, List.all_nil, Bool.and_self]
    done
  if h : n = 0
  then by
    unfold printNumberAux
    simp [h]
  else by
    have ih := printNumberAux_digits (n / 10)
    unfold printNumberAux
    simp only [h, ↓reduceIte, List.all_append, ih, h2, Bool.and_self]

@[reducible]
def printNumberAuxTR (n : Nat) : List Char :=
  let rec aux (n : Nat) (sink : List Char) : List Char :=
    if h : n = 0
    then sink
    else aux (n / 10) ((n % 10).digitChar :: sink)
  aux n []

-- Do this early.
@[csimp]
theorem printsEq : printNumberAux = printNumberAuxTR :=
  let rec printBase_s (n : Nat) : n ≠ 0 → printNumberAux n = printNumberAux (n / 10) ++ [(n % 10).digitChar] := by
    intro h
    conv =>
      lhs
      unfold printNumberAux
    simp only [h, ↓reduceIte]

  let rec lem2 (n : Nat) (xs ys : List Char) : (printNumberAuxTR.aux n xs) ++ ys = printNumberAuxTR.aux n (xs ++ ys) :=
    if h: n = 0
    then by
      simp only [h, printNumberAuxTR.aux, ↓reduceDIte]
    else by
      unfold printNumberAuxTR.aux
      have ih := lem2 (n/10) (((n % 10).digitChar :: xs)) ys
      simp only [h, ↓reduceDIte, ih, List.cons_append]

  let rec printsEq (n : Nat) : printNumberAux n = printNumberAuxTR n :=
    if h : n = 0
    then by
      unfold printNumberAuxTR.aux
      simp only [h, (show printNumberAux 0 = [] by rfl), ↓reduceDIte]
    else by
      unfold printNumberAuxTR.aux
      have hs := printBase_s (n) (h)
      have ih := printsEq (n / 10)
      have h3 := lem2 (n/10) [] [(n % 10).digitChar]
      simp only [hs, ih, h3, List.nil_append, h, ↓reduceDIte]

  funext printsEq

def printNumberPadded (n : Nat) (len: Nat) : String :=
  ⟨(printNumberAux n).leftpad len '0'⟩

theorem printNumberPadded_digits (n : Nat) (len : Nat) : (printNumberPadded n len).data.all Char.isDigit := by
  simp only [List.leftpad, ↓Char.isValue, List.all_append, List.all_replicate, Char.reduceIsDigit,
    ite_self, printNumberAux_digits, Bool.and_self, printNumberPadded]
  done


@[reducible]
def printNumber (n : Nat) : String :=
  printNumberPadded n 1

theorem digit_zero'' {c : Char} : c.isDigit → c.toNat - 48 = 0 → c = '0' := by
  intro h h'
  have _ := isDigit_toNat_iff.mp h
  have _ : c.toNat ≤ 48 := by omega
  have h8' : (48 : UInt32).toNat = (48 : Nat) := by simp
  have h8 := UInt32.toNat_inj.mp (h8' ▸ (show c.toNat = 48 by omega))
  exact Char.eq_of_val_eq h8

theorem eq_zero_iff0 (xs : List Char) (hDigit : xs.all Char.isDigit) : parseRev xs = 0 ↔ List.replicate xs.length '0' = xs :=
  if hnil : xs = []
  then by
    rw [hnil]
    simp [parseRev]
  else by
    have _ : 0 < xs.length := List.length_pos_iff.mpr hnil
    have ih := eq_zero_iff0 (xs.dropLast) (digitDrop xs hDigit)
    refine Iff.intro ?mp ?mpr
    case mp =>
      unfold parseRev
      simp only [hnil, ↓reduceDIte, ↓Char.isValue, Char.reduceToNat, Nat.add_eq_zero_iff, and_imp]
      intro h0 h1
      have hj := List.dropLast_concat_getLast hnil
      conv =>
        rhs
        rw [← hj]
      conv =>
        lhs
        rw [← hj]
      simp only [List.length_append, List.length_dropLast, List.length_singleton, ↓Char.isValue]
      rw [List.replicate_succ]
      have hlen : xs.length - 1 = xs.dropLast.length := by simp
      rw [hlen]
      have hh : '0' :: List.replicate (xs.dropLast.length) '0' = List.replicate (xs.dropLast.length) '0' ++ ['0'] := by
        have h0 : '0' :: List.replicate (xs.dropLast.length) '0' = ['0'] ++ List.replicate (xs.dropLast.length) '0' := by simp
        have h1 : ['0'] = List.replicate 1 '0' := by simp
        have h2 := h1 ▸ List.replicate_append_replicate (n := 1) (m := xs.dropLast.length) (a := '0')
        have h3 := h1 ▸ List.replicate_append_replicate (n := xs.dropLast.length) (m := 1) (a := '0')
        rw [h0]
        rw [h2, h3]
        simp only [List.length_dropLast, ↓Char.isValue, List.replicate_inj, Nat.add_eq_zero_iff,
          Nat.add_one_ne_zero, false_and, or_true, and_true]
        omega
      rw [hh]
      have heq_0 : xs.getLast hnil = '0' := digit_zero'' (digitGet xs hDigit hnil) h1
      rw [heq_0]
      simp only [↓Char.isValue, List.append_cancel_right_eq]
      apply ih.mp
      have of_0 : 10 * parseRev xs.dropLast =  parseRev xs.dropLast := by
        omega
      rw [of_0] at h0
      exact h0
    case mpr =>
      unfold parseRev
      simp only [↓Char.isValue, hnil, ↓reduceDIte, Char.reduceToNat]
      intro h1
      have hleft : parseRev xs.dropLast = 0 := ih.mpr (by
        have ih' := h1 ▸ ih
        simp at ih'
        conv =>
          rhs
          rw [← h1]
        have hlen : xs.dropLast.length = xs.length - 1 := by simp
        rw [hlen]
        exact (List.dropLast_replicate (n := (xs.length)) (a := '0')).symm
      )
      rw [hleft]
      simp only [Nat.mul_zero, Nat.zero_add]
      -- from h1 you can get this;
      have hnil' : List.replicate xs.length '0' ≠ [] := h1.symm ▸ hnil
      have hrw : xs.getLast hnil = (List.replicate xs.length '0').getLast (hnil') := by
        conv =>
          rhs
          simp [h1]
      simp [hrw]
      done

termination_by xs.length
decreasing_by
  .
    rw [xs.length_dropLast]
    have _: xs.length > 0 := List.length_pos_iff.mpr ‹_›
    omega

theorem toNat_inj  {a b : Char} : a.toNat = b.toNat → a = b := by
  simp [Char.toNat]
  intro h
  apply Char.eq_of_val_eq
  rw [← UInt32.toNat_inj]
  assumption

theorem digit_zero' {c : Char} : c.isDigit → c.val - 48 = 0 → c = '0' := by
  intro h h'
  have h4 := isDigit_iff.mp h
  have h5 := UInt32.toBitVec_eq_of_eq h'
  apply Char.eq_of_val_eq
  apply UInt32.eq_of_toBitVec_eq
  simp at h5
  simp [UInt32.toBitVec]
  bv_omega

theorem parsePrintRev (n : Nat) : parseRev (printNumberAux n) = n :=
  if h : n = 0
  then by
    unfold printNumberAux parseRev; simp only [h, ↓reduceIte, ↓reduceDIte]
  else by
    unfold printNumberAux parseRev
    simp only [h, ↓reduceIte, List.append_eq_nil_iff, List.cons_ne_self, and_false, ↓reduceDIte,
      List.dropLast_concat, ne_eq, not_false_eq_true, List.getLast_append_of_ne_nil,
      List.getLast_singleton, ↓Char.isValue, Char.reduceToNat, mod_10_eq n, Nat.div_add_mod n 10, parsePrintRev (n / 10)]

theorem print_parse_iso : (xs: List Char) → xs.all (Char.isDigit) → (printNumberAux (parseFoldl xs)).leftpad (xs.length) '0' = xs :=
  let rec aux (xs: List Char) (h : xs.all (Char.isDigit)) : (printNumberAux (parseRev xs)).leftpad (xs.length) '0' = xs :=
    if hnil : xs = []
    then by
      unfold parseRev printNumberAux; simp only [List.leftpad, hnil, List.length_nil, ↓reduceDIte,
        ↓reduceIte, Nat.sub_self, ↓Char.isValue, List.replicate_zero, List.append_nil]
    else by
      have _ : 0 < xs.length := List.length_pos_iff.mpr hnil
      have ih := aux (xs.dropLast) (digitDrop xs h)
      unfold parseRev
      simp only [↓Char.isValue, hnil, ↓reduceDIte, Char.reduceToNat]
      unfold printNumberAux
      by_cases hz : 10 * parseRev xs.dropLast + ((xs.getLast hnil).toNat - 48) = 0
      case pos =>
        simp only [List.leftpad, hz, ↓reduceIte, List.length_nil, Nat.sub_zero, ↓Char.isValue,
          List.append_nil]
        rw [← (eq_zero_iff0 xs h)]
        unfold parseRev
        simp only [hnil, ↓reduceDIte]
        exact hz
        done
      case neg =>
        simp only [↓Char.isValue, hz, ↓reduceIte]
        have hdigit := digitGet xs h hnil
        have hlt: ((xs.getLast hnil).toNat - 48) < 10 := Char.lt_10_of_isDigit hdigit
        have hmuldiv : (((10 * parseRev xs.dropLast) + ((xs.getLast hnil).toNat - 48)) / 10) = (parseRev xs.dropLast) := by omega
        have hmulmod : ((10 * parseRev xs.dropLast) + ((xs.getLast hnil).toNat - 48)) % 10 = ((xs.getLast hnil).toNat - 48) := by omega
        have hzz : ((xs.getLast hnil).toNat - 48).digitChar = xs.getLast hnil := parseCharOkMatch2 hdigit
        have happ : List.leftpad (xs.length) '0' (printNumberAux (parseRev xs.dropLast) ++ [((xs.getLast hnil).toNat - 48).digitChar])
          = (List.leftpad (xs.dropLast.length) '0' (printNumberAux (parseRev xs.dropLast))) ++ [((xs.getLast hnil).toNat - 48).digitChar] :=
          by
            simp only [List.leftpad, List.length_append, List.length_singleton, ↓Char.isValue,
              List.length_dropLast, List.append_assoc, List.append_cancel_right_eq,
              List.replicate_inj, or_true, and_true]
            omega
        rw [hmuldiv, hmulmod, happ, ih, hzz]
        exact List.dropLast_concat_getLast hnil
  parsers_eq ▸ aux
