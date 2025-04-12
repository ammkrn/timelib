/-
The best way to keep yourself sane while looking at this is to mentally separate two notions:

1. A timer; a monotinically increasing counter
2. A digital clock face on a consumer electronic device, like the clock that tells you the time on your phone.
-/
/-
Apparently the leap second will be axed in 2035. It's still worth it to have this because:

+ Historical time stamps will be around indefinitely
+ It is unlikely that software written and adopted before 2035 will quickly adapt to this change.
  The world will probably be using software (as applications or librarires) that in some way recognizes leap
  seconds for quite a while after 2035.
+ The details of applying negative leap seconds are still not perfectly understood, but it is
  now believed a negative leap second will be necessary before 2035.
-/
import Timelib.Util
import Timelib.DateTime.Naive
import Timelib.Duration.SignedDuration

namespace Timelib

/-
The left hand column feels like TAI (with a Jan 1 1900 epoch)
since it assumes a monotonic clock that does NOT adjust for "60"
or phantom 59s, and does not incorporate the initial 10 seconds.
The first time on the list is 1 Jan 1972 with no offset.
-/
structure LeapSecond where
  /--
  The UTC time (*in the proleptic gregorian epoch*) in seconds when this leap second is to be "inserted".
  We emphasize use of the proleptic gregorian epoch, because most available leap table data will
  specify this value as a time in the NTP epoch (Jan 1 1900) or unix epoch (Jan 1 1970) which will
  need to be converted.
  -/
  insertedAtUtc : NaiveDateTime 0
  /--
  The duration of the leap second; this will almost always be 1 second, but may be negative (-1 second),
  and the standard leap table begins with a single leap second of duration 10. The tl;dr is that between
  the synchronization of TAI and the creation of the modern leap second standard, TAI and UT1 drifted by
  ~10 seconds.
  -/
  duration : SignedDuration 0
  /--
  For parsing and printing to work correctly, we need assurance that
  positive leap seconds are inserted at the end/start boundary of some minute,
  and negative leap seconds are inserted at/elide some seconds leading up to the
  minute boundary. For example, a negative leap second with duration -1 seconds is
  inesrted at XX:XX:59 and elides the 59-60 second transition of that minute when
  printed, while a positive leap second is inserted at XX:XX:60.

  One of the difficulties of the standard leap second specification is that
  day 0 @ 23:59:60 and day 1 @ 00:00:00 can only be disambiguated by looking
  at the timestamp.
  -/
  h: insertedAtUtc.toSignedDuration % (60 : Int)
   = if duration ≥ 0 then 0 else (⟨60⟩ - duration.abs) := by decide
deriving DecidableEq, Repr

/--
The individual rows of a leap table; keeps track of the cumulative
duration, which for any row `i` is the sum of all durations for leap
seconds inserted at `t <= i.insertedAtUtc`
-/
structure Row extends LeapSecond where
  cumulative : SignedDuration 0
deriving DecidableEq, Repr

namespace Row

@[simp] abbrev prevCumulative (r : Row) : SignedDuration 0 :=
  r.cumulative - r.duration

/--
The moment at which a leap second is fully inserted, and we're no longer "within"
the leap second.

Remark: This works (in context) for negative leap seconds because it uses the
absolute value of the duration.
-/
@[simp] abbrev elapsesAt (r : Row) : NaiveDateTime 0 :=
  r.insertedAtUtc + r.duration.abs

end Row

/-
These should probably be converted to use proleptic gregorian epochs
on insertion; these are just ntp epoch holdovers.
-/
@[reducible]
def mkTable (xs : List LeapSecond) : List Row :=
  let rec aux : List LeapSecond → List Row
    | [] => []
    | hd :: tl =>
      let tl := aux tl
      --let cumulative := hd.duration + (tl.map (fun x => x.duration)).sum
      let cumulative := hd.duration + (tl[0]?.map (fun x => x.cumulative)).getD 0
      ⟨hd, cumulative⟩ :: tl
  aux (xs.mergeSort (fun a b => a.insertedAtUtc ≥ b.insertedAtUtc))

def do1 : Int × Int → Option LeapSecond
  | (insertedAtUtc, duration) =>
    let insertedAtUtc := (⟨⟨insertedAtUtc⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch
    let duration : SignedDuration 0 := ⟨duration⟩
    if h : insertedAtUtc.toSignedDuration % (60 : Int) = if duration ≥ 0 then 0 else (⟨60⟩ - duration.abs)
    then some ⟨insertedAtUtc, duration, h⟩
    else none

@[reducible]
def leapTableFromNtpEpochRows (xs : List (Int × Int)) : Option (List Row) :=
  (xs.mapM do1).map mkTable

namespace LeapTable

/--
This is frequently repeated, so is abstracted as an abbrev.
-/
abbrev cumulative (xs : List Row) : SignedDuration 0 :=
  (xs.map fun x => x.duration).sum

/--
Specifies the construction of a well-formed (`WF`) leap table.

A leap table is well-formed (abbreviated `WF`) if it's...
+ Empty
+ The concatenation of a well-formed leap table and a head containing a leap second
  which (0) is inserted at the correct time as encoded by the `LeapSecond` type, (1) is inserted
  at a later time than any other element of the table, (2) has a `cumulative` field which is the
  sum of its own duration and all other leap seconds in the table, and (3) does not overlap any
  of the other leap seconds in the table (leap seconds cannot be allowed to make UTC <-> TAI conversions
  ambiguous).
-/
inductive WF : List Row → Prop
  | nil : WF []
  | cons (hd : Row) (tl : List Row) :
    WF tl →
    (∀ x ∈ tl, x.insertedAtUtc + x.cumulative.abs < hd.insertedAtUtc - hd.cumulative.abs) →
    hd.cumulative = hd.duration + cumulative tl →
    WF (hd :: tl)


def LeapTable := { rows // WF rows }

@[simp]
def cons (hd : LeapSecond) (tl : List Row) : List Row :=
  ⟨hd, hd.duration + cumulative tl⟩ :: tl

theorem consWF
  (hd : LeapSecond)
  (tl : List Row)
  (htl : WF tl)
  (hafter : ∀ x ∈ tl, x.insertedAtUtc + x.cumulative.abs < hd.insertedAtUtc - (hd.duration + cumulative tl).abs)
  : WF (cons hd tl) :=
  WF.cons ⟨hd, hd.duration + cumulative tl⟩ tl htl hafter rfl

theorem singletonWF (s : LeapSecond) :
  WF [⟨s, s.duration⟩] := by
  have h := consWF s [] WF.nil (by simp)
  simpa only [cons, cumulative, List.map_nil, List.sum_nil, SignedDuration.add_zero] using h

theorem singletonWF_eta (hd : Row) :
  hd.duration = hd.cumulative → WF [hd] := by
  intro heq
  have hd_eta : (⟨hd.toLeapSecond, hd.cumulative⟩ : Row) = hd := by simp
  exact hd_eta ▸ heq ▸ singletonWF hd.toLeapSecond

theorem notWFSingleton
 (hd : Row) : hd.duration ≠ hd.cumulative → ¬WF [hd]
  | hf, WF.cons _ _ _ _ h => by
    simp only [cumulative, List.map_nil, List.sum_nil, SignedDuration.add_zero] at h
    exact hf.symm h

theorem lemma1' : (xs : List Row) → WF xs
  → (hnil : xs ≠ []) → cumulative xs = (xs.head hnil).cumulative
  | hd :: tl, WF.cons _ _ h0 h1 h2, hnil => by
    simp only [cumulative] at h2 |-
    simp only [List.map_cons, List.sum_cons, List.head_cons, h2]

theorem cons_cons_cumulative_eq : {x y : Row} → {tl : List Row} →
  WF (x :: y :: tl) → x.cumulative = x.duration + y.cumulative
  | ⟨⟨u, d, _⟩, c⟩, y, tl, WF.cons _ _ wftl _ _ => by
    have _ := lemma1' (y :: tl) wftl (List.cons_ne_nil _ _);
    simp_all only [List.mem_cons, gt_iff_lt, NaiveDateTime.lt_def, forall_eq_or_imp,
      List.map_cons, List.sum_cons, List.head_cons]

theorem forall_mem_gt_of_wf_cons {hd : Row} {tl : List Row} :
  WF (hd :: tl) → (∀ x ∈ tl, x.insertedAtUtc + x.cumulative.abs < hd.insertedAtUtc - (hd.duration + cumulative tl).abs)
  | WF.cons _ _ hall _ he => by rw [← he]; assumption

theorem insertedAtUtc_lt_of_wf (x y : Row) (tl : List Row) : WF (x :: y :: tl) → y.insertedAtUtc + y.cumulative.abs < x.insertedAtUtc - x.cumulative.abs
  | WF.cons _ _ _ hall _ => hall y List.mem_cons_self

theorem cumulative_evidence {y : Row} {tl : List Row} : WF (y :: tl) → y.cumulative = cumulative (y :: tl)
  | WF.cons _ _ wftl _ he => by simp only [he, cumulative, List.map_cons, List.sum_cons]

theorem forall_no_overlap (x : Row) (ys : List Row) :
  WF ys →
  (hnil : ys ≠ []) →
  x.insertedAtUtc - x.cumulative.abs > (ys.head hnil).insertedAtUtc + (ys.head hnil).cumulative.abs →
  (forall y, y ∈ ys → x.insertedAtUtc - x.cumulative.abs > y.insertedAtUtc + y.cumulative.abs)
  | WF.nil, _, _  => by simp
  | WF.cons y zs wftl hall hcumu, hnil, hgt => by
    intro row
    simp only [List.mem_cons, gt_iff_lt]
    intro hOr
    cases hOr with
    | inl hl =>
      simpa only [hl, List.mem_singleton, gt_iff_lt, forall_eq]
    | inr hr =>
      have hall' := hall row hr
      have lt_lem (a b : Int) : a - b.natAbs ≤ a + b.natAbs := by omega
      have hh : y.insertedAtUtc - y.cumulative.abs ≤ y.insertedAtUtc + y.cumulative.abs := by
        simp [SignedDuration.lt_def, SignedDuration.abs_def, SignedDuration.add_def,
        NaiveDateTime.instHAddSelfSignedDurationSelf_def,
        NaiveDateTime.hSub_signed_def,
        SignedDuration.neg_def,
        ] at hall'
        apply lt_lem
      have hmid : (row.insertedAtUtc + row.cumulative.abs) < (y.insertedAtUtc + y.cumulative.abs) := by
        exact NaiveDateTime.lt_of_lt_of_le hall' hh
      simp only [NaiveDateTime.lt_def] at hall' hgt |-
      simp only [List.head] at hgt
      exact Int.lt_trans hmid hgt

instance instDecidableWF : DecidablePred WF :=
  fun
  | [] => isTrue WF.nil
  -- Need an extra case for this because we want to get the cumulative value
  -- of the tail efficiently.
  | hd :: [] =>
    if h : hd.duration = hd.cumulative
    then isTrue <| singletonWF_eta hd h
    else isFalse <| notWFSingleton hd h
  | x :: y :: tl =>
    match instDecidableWF (y :: tl) with
      | isFalse y_tl_not_wf => isFalse <| fun
        | WF.cons _ _ htl _ _ => False.elim (y_tl_not_wf htl)
      | isTrue ht =>
        if h : x.cumulative = x.duration + y.cumulative ∧ x.insertedAtUtc - x.cumulative.abs > y.insertedAtUtc + y.cumulative.abs
        then
          have no_overlap := forall_no_overlap x (y :: tl) ht (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) h.right
          isTrue (WF.cons x (y :: tl) ht no_overlap  (cumulative_evidence ht ▸ h.left))
        else
          isFalse <| fun hf =>
            match Classical.not_and_iff_not_or_not.mp h with
            | Or.inl hl => hl (cons_cons_cumulative_eq hf)
            | Or.inr hr => hr (insertedAtUtc_lt_of_wf x y tl hf)

def baseTable : List Row :=
  let table := leapTableFromNtpEpochRows [
    (2272060800, 10),
    (2287785600, 1),
    (2303683200, 1),
    (2335219200, 1),
    (2366755200, 1),
    (2398291200, 1),
    (2429913600, 1),
    (2461449600, 1),
    (2492985600, 1),
    (2524521600, 1),
    (2571782400, 1),
    (2603318400, 1),
    (2634854400, 1),
    (2698012800, 1),
    (2776982400, 1),
    (2840140800, 1),
    (2871676800, 1),
    (2918937600, 1),
    (2950473600, 1),
    (2982009600, 1),
    (3029443200, 1),
    (3076704000, 1),
    (3124137600, 1),
    (3345062400, 1),
    (3439756800, 1),
  ]
  table.get (by decide)

--def baseTable_ : List Row :=
-- mkTable [
--  ⟨(⟨⟨2272060800⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨10⟩, by decide⟩,
--  ⟨(⟨⟨2287785600⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2303683200⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2335219200⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2366755200⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2398291200⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2429913600⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2461449600⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2492985600⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2524521600⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2571782400⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2603318400⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2634854400⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2698012800⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2776982400⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2840140800⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2871676800⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2918937600⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2950473600⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨2982009600⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨3029443200⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨3076704000⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨3124137600⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨3345062400⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
--  ⟨(⟨⟨3439756800⟩, by decide⟩ : NaiveDateTime 0).ntpEpochToProlepticGregorianEpoch, ⟨1⟩, by decide⟩,
-- ]


end LeapTable
