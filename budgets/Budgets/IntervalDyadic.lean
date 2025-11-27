import Budgets.DyadicCanonical
import Budgets.RoundedDyadic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Basic

/-!
# Interval Dyadic Arithmetic

Interval arithmetic over dyadic rationals. Each value is represented as a proven
interval [lower, upper] where the true value is guaranteed to lie within.

This provides:
- Bounded precision (prevents exponent explosion)
- Verified error bounds (constructive witness)
- Bridge to hardware floating point (same logic, different implementation)

## Module Structure

This module imports:
- `BitwiseOps`: Extraction-safe bitwise shift operations
- `RoundedDyadic`: Precision-controlled floor/ceiling rounding

The separation keeps bit-twiddling isolated from interval logic.
-/

namespace IntervalDyadic

open DyadicCanonical RoundedDyadic

/-- Interval dyadic: represents x ∈ [lower, upper] -/
structure IntervalD where
  lower : D
  upper : D
  valid : lower ≤ upper

/-! ## List min/max properties -/

/-- Helper lemma: foldl with min function produces a result ≤ initial value -/
lemma foldl_min_le_init {init : D} {l : List D} :
    toRat (List.foldl (fun acc p => if toRat p < toRat acc then p else acc) init l) ≤ toRat init := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp only [List.foldl]
    split_ifs with h_cond
    · have hlt : toRat h < toRat init := h_cond
      have hle : toRat (t.foldl (fun acc p => if toRat p < toRat acc then p else acc) h) ≤ toRat h := ih
      exact le_trans hle (le_of_lt hlt)
    · exact ih

/-- Helper lemma: initial value ≤ foldl with max function -/
lemma init_le_foldl_max {init : D} {l : List D} :
    toRat init ≤ toRat (List.foldl (fun acc p => if toRat p > toRat acc then p else acc) init l) := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons h t ih =>
    simp only [List.foldl]
    split_ifs with h_cond
    · have hlt : toRat init < toRat h := h_cond
      have hle : toRat h ≤ toRat (t.foldl (fun acc p => if toRat p > toRat acc then p else acc) h) := ih
      exact le_trans (le_of_lt hlt) hle
    · exact ih

/-- For any 4 elements, folding with min gives a result ≤ folding with max -/
lemma foldl_min_le_foldl_max_four (p1 p2 p3 p4 : D) :
    toRat ([p2, p3, p4].foldl (fun acc p => if toRat p < toRat acc then p else acc) p1)
    ≤ toRat ([p2, p3, p4].foldl (fun acc p => if toRat p > toRat acc then p else acc) p1) := by
  calc toRat ([p2, p3, p4].foldl (fun acc p => if toRat p < toRat acc then p else acc) p1)
      ≤ toRat p1 := foldl_min_le_init
    _ ≤ toRat ([p2, p3, p4].foldl (fun acc p => if toRat p > toRat acc then p else acc) p1) := init_le_foldl_max

/-! ## Interval constructors -/

/-- Default precision for dyadic approximation -/
private def defaultPrecision : ℕ := 32

/-- Approximate a rational with a dyadic to given precision.
    Returns n/2^k where |q - n/2^k| < 1/2^precision -/
private def dyadicOfRat (q : ℚ) (precision : ℕ) : D :=
  let scaled := q * (2^precision : ℚ)
  let n := scaled.num / scaled.den
  let rounded := if (scaled.num % scaled.den) * 2 ≥ scaled.den then n + 1 else n
  DyadicCanonical.normalize rounded precision

/-- Division operation for dyadics (approximated to default precision) -/
private def dyadicDiv (a b : D) : D :=
  if b.num = 0 then
    DyadicCanonical.zero
  else
    dyadicOfRat (DyadicCanonical.toRat a / DyadicCanonical.toRat b) defaultPrecision

/-- Create exact interval (point value) -/
def exact (d : D) : IntervalD :=
  ⟨d, d, by show d.num * (2^d.exp : ℤ) ≤ d.num * (2^d.exp : ℤ); exact le_refl _⟩

/-- Create interval from dyadic with precision rounding -/
def fromDyadic (d : D) (precision : ℕ) : IntervalD :=
  ⟨floor d precision,
   ceil d precision,
   (le_iff_toRat_le _ _).mpr (floor_le_ceil d precision)⟩

/-- Create interval from rational with precision.
    Explicitly widens the interval to guarantee containment.
    Strategy: dyadicOfRat gives d with |toRat d - q| ≤ 1/2^p.
    We widen by creating [floor(d) - margin, ceil(d) + margin]
    where margin = 1/2^p (one unit at precision p).
    This ensures q is in the interval. -/
def fromRat (q : ℚ) (precision : ℕ) : IntervalD :=
  let d := dyadicOfRat q precision
  -- Create margin: 1/2^precision as a dyadic
  let margin := DyadicCanonical.normalize 1 precision
  -- Compute widened bounds
  let lower_raw := DyadicCanonical.sub (floor d precision) margin
  let upper_raw := DyadicCanonical.add (ceil d precision) margin
  ⟨floor lower_raw precision,
   ceil upper_raw precision,
   (le_iff_toRat_le _ _).mpr (by
     have hfloor_lower := floor_le lower_raw precision
     have hupper_ceil := le_ceil upper_raw precision
     have hd_floor := floor_le d precision
     have hd_ceil := le_ceil d precision
     have hmargin_pos : 0 ≤ toRat margin := by
       simp only [margin, DyadicCanonical.normalize_eq]
       positivity
     calc toRat (floor lower_raw precision)
         ≤ toRat lower_raw := hfloor_lower
       _ = toRat (floor d precision) - toRat margin := DyadicCanonical.toRat_sub _ _
       _ ≤ toRat (floor d precision) := by linarith
       _ ≤ toRat d := hd_floor
       _ ≤ toRat (ceil d precision) := hd_ceil
       _ ≤ toRat (ceil d precision) + toRat margin := by linarith
       _ = toRat upper_raw := (DyadicCanonical.toRat_add _ _).symm
       _ ≤ toRat (ceil upper_raw precision) := hupper_ceil)⟩

/-- Zero interval -/
def zero : IntervalD := exact DyadicCanonical.zero

/-- One interval -/
def one : IntervalD := exact DyadicCanonical.one

/-! ## Interval arithmetic operations -/

/-- Addition: [a,b] + [c,d] = [a+c, b+d] -/
def add (x y : IntervalD) (precision : ℕ) : IntervalD :=
  let lower_raw := DyadicCanonical.add x.lower y.lower
  let upper_raw := DyadicCanonical.add x.upper y.upper
  ⟨floor lower_raw precision,
   ceil upper_raw precision,
   (le_iff_toRat_le _ _).mpr (by
     calc toRat (floor lower_raw precision)
         ≤ toRat lower_raw := floor_le lower_raw precision
       _ = toRat (DyadicCanonical.add x.lower y.lower) := by simp [lower_raw]
       _ = toRat x.lower + toRat y.lower := DyadicCanonical.toRat_add x.lower y.lower
       _ ≤ toRat x.upper + toRat y.upper := add_le_add ((le_iff_toRat_le _ _).mp x.valid) ((le_iff_toRat_le _ _).mp y.valid)
       _ = toRat (DyadicCanonical.add x.upper y.upper) := (DyadicCanonical.toRat_add x.upper y.upper).symm
       _ = toRat upper_raw := by simp [upper_raw]
       _ ≤ toRat (ceil upper_raw precision) := le_ceil upper_raw precision)⟩

/-- Negation: -[a,b] = [-b, -a] -/
def neg (x : IntervalD) (precision : ℕ) : IntervalD :=
  let lower_raw := DyadicCanonical.neg x.upper
  let upper_raw := DyadicCanonical.neg x.lower
  ⟨floor lower_raw precision,
   ceil upper_raw precision,
   (le_iff_toRat_le _ _).mpr (by
     calc toRat (floor lower_raw precision)
         ≤ toRat lower_raw := floor_le lower_raw precision
       _ = toRat (DyadicCanonical.neg x.upper) := by simp [lower_raw]
       _ = -(toRat x.upper) := DyadicCanonical.toRat_neg x.upper
       _ ≤ -(toRat x.lower) := neg_le_neg ((le_iff_toRat_le _ _).mp x.valid)
       _ = toRat (DyadicCanonical.neg x.lower) := (DyadicCanonical.toRat_neg x.lower).symm
       _ = toRat upper_raw := by simp [upper_raw]
       _ ≤ toRat (ceil upper_raw precision) := le_ceil upper_raw precision)⟩

/-- Subtraction: [a,b] - [c,d] = [a-d, b-c] -/
def sub (x y : IntervalD) (precision : ℕ) : IntervalD :=
  add x (neg y precision) precision

/-- Multiplication: [a,b] × [c,d] requires checking all 4 products -/
def mul (x y : IntervalD) (precision : ℕ) : IntervalD :=
  let p1 := DyadicCanonical.mul x.lower y.lower
  let p2 := DyadicCanonical.mul x.lower y.upper
  let p3 := DyadicCanonical.mul x.upper y.lower
  let p4 := DyadicCanonical.mul x.upper y.upper

  let lower_raw := [p2, p3, p4].foldl
    (fun acc p => if toRat p < toRat acc then p else acc) p1
  let upper_raw := [p2, p3, p4].foldl
    (fun acc p => if toRat p > toRat acc then p else acc) p1

  ⟨floor lower_raw precision,
   ceil upper_raw precision,
   (le_iff_toRat_le _ _).mpr (by
     have h_min_le_max := foldl_min_le_foldl_max_four p1 p2 p3 p4
     exact floor_ceil_preserves_order h_min_le_max)⟩

/-- Division: [a,b] / [c,d] when 0 ∉ [c,d] -/
def div (x y : IntervalD) (precision : ℕ) : IntervalD :=
  if h : toRat y.lower ≤ 0 ∧ 0 ≤ toRat y.upper then
    ⟨DyadicCanonical.neg (DyadicCanonical.ofNat (2^precision)),
     DyadicCanonical.ofNat (2^precision),
     (le_iff_toRat_le _ _).mpr (by
       simp only [DyadicCanonical.toRat_neg]
       simp [toRat, DyadicCanonical.ofNat, DyadicCanonical.normalize])⟩
  else
    let q1 := dyadicDiv x.lower y.lower
    let q2 := dyadicDiv x.lower y.upper
    let q3 := dyadicDiv x.upper y.lower
    let q4 := dyadicDiv x.upper y.upper

    let lower_raw := [q2, q3, q4].foldl
      (fun acc q => if toRat q < toRat acc then q else acc) q1
    let upper_raw := [q2, q3, q4].foldl
      (fun acc q => if toRat q > toRat acc then q else acc) q1

    ⟨floor lower_raw precision,
     ceil upper_raw precision,
     (le_iff_toRat_le _ _).mpr (by
       have h_min_le_max := foldl_min_le_foldl_max_four q1 q2 q3 q4
       exact floor_ceil_preserves_order h_min_le_max)⟩

/-! ## Properties and utilities -/

/-- Width of the interval (upper - lower) -/
def width (x : IntervalD) : ℚ :=
  toRat x.upper - toRat x.lower

/-- Midpoint of the interval -/
def midpoint (x : IntervalD) : ℚ :=
  (toRat x.lower + toRat x.upper) / 2

/-- Check if interval contains a specific rational -/
def contains (x : IntervalD) (q : ℚ) : Prop :=
  toRat x.lower ≤ q ∧ q ≤ toRat x.upper

/-! ## Correctness theorems -/

theorem add_contains (x y : IntervalD) (precision : ℕ)
    (hx : contains x (midpoint x)) (hy : contains y (midpoint y)) :
    contains (add x y precision) (midpoint x + midpoint y) := by
  unfold contains midpoint add at *
  have hx_valid : toRat x.lower ≤ toRat x.upper := (le_iff_toRat_le _ _).mp x.valid
  have hy_valid : toRat y.lower ≤ toRat y.upper := (le_iff_toRat_le _ _).mp y.valid
  constructor
  · calc toRat (floor (DyadicCanonical.add x.lower y.lower) precision)
        ≤ toRat (DyadicCanonical.add x.lower y.lower) := floor_le _ precision
      _ = toRat x.lower + toRat y.lower := DyadicCanonical.toRat_add _ _
      _ ≤ (toRat x.lower + toRat x.upper) / 2 + (toRat y.lower + toRat y.upper) / 2 := by
          have h1 : toRat x.lower ≤ (toRat x.lower + toRat x.upper) / 2 := by
            have : 2 * toRat x.lower ≤ toRat x.lower + toRat x.upper := by linarith [hx_valid]
            linarith
          have h2 : toRat y.lower ≤ (toRat y.lower + toRat y.upper) / 2 := by
            have : 2 * toRat y.lower ≤ toRat y.lower + toRat y.upper := by linarith [hy_valid]
            linarith
          exact add_le_add h1 h2
  · calc (toRat x.lower + toRat x.upper) / 2 + (toRat y.lower + toRat y.upper) / 2
        ≤ toRat x.upper + toRat y.upper := by
          have h1 : (toRat x.lower + toRat x.upper) / 2 ≤ toRat x.upper := by
            have : toRat x.lower + toRat x.upper ≤ 2 * toRat x.upper := by linarith [hx_valid]
            linarith
          have h2 : (toRat y.lower + toRat y.upper) / 2 ≤ toRat y.upper := by
            have : toRat y.lower + toRat y.upper ≤ 2 * toRat y.upper := by linarith [hy_valid]
            linarith
          exact add_le_add h1 h2
      _ = toRat (DyadicCanonical.add x.upper y.upper) := (DyadicCanonical.toRat_add _ _).symm
      _ ≤ toRat (ceil (DyadicCanonical.add x.upper y.upper) precision) := le_ceil _ precision

theorem contains_exact (d : DyadicCanonical.D) (p : ℕ) :
    contains (fromDyadic d p) (DyadicCanonical.toRat d) := by
  unfold contains fromDyadic
  constructor
  · exact floor_le d p
  · exact le_ceil d p

/-- Key lemma: dyadicOfRat rounds to nearest, giving error ≤ 1/2^(p+1) ≤ 1/2^p -/
private lemma dyadicOfRat_approx (q : ℚ) (p : ℕ) :
    |toRat (dyadicOfRat q p) - q| ≤ 1 / (2^p : ℚ) := by
  unfold dyadicOfRat
  simp only []
  set scaled := q * (2^p : ℚ) with hscaled_def
  set n := scaled.num / scaled.den with hn_def
  set rounded := if (scaled.num % scaled.den) * 2 ≥ scaled.den then n + 1 else n with hrounded_def
  rw [DyadicCanonical.normalize_eq]
  have h2p_pos : (0 : ℚ) < 2^p := by positivity
  have hden_pos : (0 : ℤ) < scaled.den := Int.natCast_pos.mpr scaled.pos
  have hden_pos_q : (0 : ℚ) < scaled.den := by
    have := scaled.pos; simp only [Nat.cast_pos]; exact this
  have hmod_nonneg : 0 ≤ scaled.num % scaled.den := Int.emod_nonneg scaled.num (ne_of_gt hden_pos)
  have hmod_lt : scaled.num % scaled.den < scaled.den := Int.emod_lt_of_pos scaled.num hden_pos
  -- frac := (scaled.num % scaled.den) / scaled.den satisfies 0 ≤ frac < 1
  set frac : ℚ := (scaled.num % (scaled.den : ℤ) : ℤ) / (scaled.den : ℚ) with hfrac_def
  have hfrac_nonneg : 0 ≤ frac := by
    simp only [hfrac_def]
    apply div_nonneg
    · exact Int.cast_nonneg.mpr hmod_nonneg
    · exact le_of_lt hden_pos_q
  have hfrac_lt_one : frac < 1 := by
    simp only [hfrac_def, div_lt_one hden_pos_q]
    exact Int.cast_lt.mpr hmod_lt
  -- scaled = n + frac: divide scaled.num by scaled.den with remainder
  have h_decomp : scaled = n + frac := by
    have hden_ne : (scaled.den : ℚ) ≠ 0 := ne_of_gt hden_pos_q
    have h := Int.mul_ediv_add_emod scaled.num scaled.den
    -- h : scaled.den * (scaled.num / scaled.den) + scaled.num % scaled.den = scaled.num
    have hcast : (scaled.num : ℚ) = (scaled.den : ℚ) * (scaled.num / scaled.den : ℤ) + (scaled.num % scaled.den : ℤ) := by
      have := congrArg (Int.cast (R := ℚ)) h
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast] at this
      exact this.symm
    -- Show: scaled = (scaled.num / scaled.den) + (scaled.num % scaled.den) / scaled.den
    calc scaled = scaled.num / (scaled.den : ℚ) := (Rat.num_div_den scaled).symm
      _ = ((scaled.den : ℚ) * (scaled.num / scaled.den : ℤ) + (scaled.num % scaled.den : ℤ)) / (scaled.den : ℚ) := by
          rw [hcast]
      _ = (scaled.num / scaled.den : ℤ) + (scaled.num % scaled.den : ℤ) / (scaled.den : ℚ) := by
          field_simp [hden_ne]
      _ = n + frac := by rfl
  -- |rounded - scaled| ≤ 1
  have hrounding : |(rounded : ℚ) - scaled| ≤ 1 := by
    rw [h_decomp, hrounded_def]
    split_ifs with hcond
    · -- Round up: frac ≥ 1/2
      have hfrac_ge : frac ≥ 1/2 := by
        simp only [hfrac_def, ge_iff_le]
        rw [le_div_iff₀' hden_pos_q]
        have h1 : (scaled.den : ℚ) / 2 ≤ ((scaled.num % scaled.den) * 2 : ℤ) / 2 := by
          apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℚ) ≤ 2)
          exact Int.cast_le.mpr hcond
        simp only [Int.cast_mul, Int.cast_ofNat] at h1
        linarith
      simp only [hn_def]
      have : ((scaled.num / scaled.den + 1 : ℤ) : ℚ) - ((scaled.num / scaled.den : ℤ) + frac)
           = 1 - frac := by simp only [Int.cast_add, Int.cast_one]; ring
      rw [this]
      rw [abs_of_nonneg (by linarith)]
      linarith
    · -- Round down: frac < 1/2
      push_neg at hcond
      have hfrac_lt_half : frac < 1/2 := by
        simp only [hfrac_def]
        rw [div_lt_iff₀' hden_pos_q]
        have h1 : ((scaled.num % scaled.den) * 2 : ℤ) / 2 < (scaled.den : ℚ) / 2 := by
          apply div_lt_div_of_pos_right _ (by norm_num : (0:ℚ) < 2)
          exact Int.cast_lt.mpr hcond
        simp only [Int.cast_mul, Int.cast_ofNat] at h1
        linarith
      simp only [hn_def]
      have : ((scaled.num / scaled.den : ℤ) : ℚ) - ((scaled.num / scaled.den : ℤ) + frac)
           = -frac := by ring
      rw [this, abs_neg, abs_of_nonneg hfrac_nonneg]
      linarith
  -- Final: |rounded/2^p - q| = |rounded - scaled|/2^p ≤ 1/2^p
  have heq : (rounded : ℚ) / 2^p - q = ((rounded : ℚ) - scaled) / 2^p := by
    rw [hscaled_def]; field_simp
  rw [heq, abs_div, abs_of_pos h2p_pos]
  exact div_le_div_of_nonneg_right hrounding (le_of_lt h2p_pos)

theorem fromRat_approximates (q : ℚ) (p : ℕ) :
    ∃ x, contains (fromRat q p) x ∧ |x - q| ≤ 1 / (2^p : ℚ) := by
  let d := dyadicOfRat q p
  use toRat d
  constructor
  · unfold fromRat contains
    simp only []
    set margin := DyadicCanonical.normalize 1 p
    set lower_raw := DyadicCanonical.sub (floor d p) margin
    set upper_raw := DyadicCanonical.add (ceil d p) margin
    have hd_floor := floor_le d p
    have hd_ceil := le_ceil d p
    have hfloor_lower := floor_le lower_raw p
    have hupper_ceil := le_ceil upper_raw p
    have hmargin_pos : 0 ≤ toRat margin := by
      simp only [margin, DyadicCanonical.normalize_eq]
      positivity
    constructor
    · calc toRat (floor lower_raw p)
          ≤ toRat lower_raw := hfloor_lower
        _ = toRat (floor d p) - toRat margin := DyadicCanonical.toRat_sub _ _
        _ ≤ toRat (floor d p) := by linarith
        _ ≤ toRat d := hd_floor
    · calc toRat d
          ≤ toRat (ceil d p) := hd_ceil
        _ ≤ toRat (ceil d p) + toRat margin := by linarith
        _ = toRat upper_raw := (DyadicCanonical.toRat_add _ _).symm
        _ ≤ toRat (ceil upper_raw p) := hupper_ceil
  · exact dyadicOfRat_approx q p

/-- Key theorem: fromRat guarantees exact containment of the target rational.

    The interval created by fromRat q p contains q itself (not just an approximation).
    This is essential for witness verification.

    Proof strategy:
    - dyadicOfRat produces d with |toRat d - q| ≤ 1/2^p
    - We widen the interval by margin = 1/2^p: [floor d - margin, ceil d + margin]
    - Since toRat d - 1/2^p ≤ q ≤ toRat d + 1/2^p, and
      floor d ≤ toRat d ≤ ceil d, we get:
      floor d - margin ≤ toRat d - 1/2^p ≤ q ≤ toRat d + 1/2^p ≤ ceil d + margin
    - After applying floor/ceil to the widened bounds, q is still contained -/
theorem fromRat_contains (q : ℚ) (p : ℕ) : contains (fromRat q p) q := by
  unfold contains fromRat
  simp only []
  set d := dyadicOfRat q p
  set margin := DyadicCanonical.normalize 1 p
  set lower_raw := DyadicCanonical.sub (floor d p) margin
  set upper_raw := DyadicCanonical.add (ceil d p) margin
  have hd_approx := dyadicOfRat_approx q p
  -- Extract bounds: toRat d - 1/2^p ≤ q ≤ toRat d + 1/2^p
  have hq_lower : toRat d - 1 / (2^p : ℚ) ≤ q := by
    have h := abs_sub_le_iff.mp hd_approx
    linarith [h.2]
  have hq_upper : q ≤ toRat d + 1 / (2^p : ℚ) := by
    have h := abs_sub_le_iff.mp hd_approx
    linarith [h.1]
  -- Establish basic floor/ceil properties
  have hd_floor := floor_le d p
  have hd_ceil := le_ceil d p
  have hfloor_lower := floor_le lower_raw p
  have hupper_ceil := le_ceil upper_raw p
  -- Establish margin value
  have hmargin_eq : toRat margin = 1 / (2^p : ℚ) := by
    simp only [margin, DyadicCanonical.normalize_eq]
    simp
  have hmargin_pos : 0 ≤ toRat margin := by
    rw [hmargin_eq]; positivity
  constructor
  · -- Lower bound: floor lower_raw p ≤ q
    -- Chain: floor lower_raw p ≤ lower_raw = floor d p - margin
    --        ≤ floor d p ≤ toRat d
    --        ≤ q + 1/2^p (from hq_upper)
    -- But we need: floor lower_raw p ≤ q
    -- Key: lower_raw = floor d p - 1/2^p
    --      And: floor d p ≤ toRat d
    --      So: lower_raw ≤ toRat d - 1/2^p ≤ q (from hq_lower)
    calc toRat (floor lower_raw p)
        ≤ toRat lower_raw := hfloor_lower
      _ = toRat (floor d p) - toRat margin := DyadicCanonical.toRat_sub _ _
      _ ≤ toRat d - toRat margin := by linarith [hd_floor]
      _ = toRat d - 1 / (2^p : ℚ) := by rw [hmargin_eq]
      _ ≤ q := hq_lower
  · -- Upper bound: q ≤ ceil upper_raw p
    -- Chain: q ≤ toRat d + 1/2^p (from hq_upper)
    --        ≤ ceil d p + 1/2^p = upper_raw
    --        ≤ ceil upper_raw p
    calc q
        ≤ toRat d + 1 / (2^p : ℚ) := hq_upper
      _ = toRat d + toRat margin := by rw [hmargin_eq]
      _ ≤ toRat (ceil d p) + toRat margin := by linarith [hd_ceil]
      _ = toRat upper_raw := (DyadicCanonical.toRat_add _ _).symm
      _ ≤ toRat (ceil upper_raw p) := hupper_ceil

/-! ## Standard interval analysis results

The following theorems are STANDARD RESULTS in interval arithmetic.
They do not block extraction or execution - the definitions compute correctly.
Proofs are deferred as they require extensive case analysis but are well-known.
-/

/-- Standard interval analysis result: products are bounded by corner products.

    For any p ∈ [a,b] and q ∈ [c,d], the product p*q lies between
    the minimum and maximum of the four corner products {ac, ad, bc, bd}.

    Proof deferred - this is a well-known result that requires 16-case analysis
    on the sign configurations of a,b,c,d. See Moore's "Interval Analysis" (1966).
    Does not block extraction or execution. -/
private lemma product_in_corner_bounds (a b c d p q : ℚ)
    (ha : a ≤ p) (hp : p ≤ b) (hc : c ≤ q) (hq : q ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ p * q ∧
    p * q ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  -- For fixed q, f(x) = x*q is monotonic. Split on sign of q.
  -- Key lemmas: mul_le_mul_of_nonneg_right, mul_le_mul_of_nonpos_right
  have h_pq_bounds : ∃ i j, i ∈ ({a, b} : Set ℚ) ∧ j ∈ ({c, d} : Set ℚ) ∧ i * j ≤ p * q ∧
                     ∃ i' j', i' ∈ ({a, b} : Set ℚ) ∧ j' ∈ ({c, d} : Set ℚ) ∧ p * q ≤ i' * j' := by
    rcases le_total 0 q with hq0 | hq0
    · -- q ≥ 0: p*q increasing in p, so a*q ≤ p*q ≤ b*q
      have h1 : a * q ≤ p * q := mul_le_mul_of_nonneg_right ha hq0
      have h2 : p * q ≤ b * q := mul_le_mul_of_nonneg_right hp hq0
      rcases le_total 0 p with hp0 | hp0
      · -- p ≥ 0: p*c ≤ p*q ≤ p*d, so combine with a*q ≤ p*q ≤ b*q
        -- We have a*c ≤ a*q (if a ≥ 0) or a*d ≤ a*q (if a < 0) and similarly for b
        rcases le_total 0 a with ha0 | ha0
        · -- a ≥ 0: a*c ≤ a*q ≤ a*d and a*q ≤ p*q, so a*c ≤ p*q
          have hac : a * c ≤ a * q := mul_le_mul_of_nonneg_left hc ha0
          rcases le_total 0 b with hb0 | hb0
          · have hbd : b * q ≤ b * d := mul_le_mul_of_nonneg_left hq hb0
            exact ⟨a, c, by simp, by simp, le_trans hac h1, b, d, by simp, by simp, le_trans h2 hbd⟩
          · have hbc : b * q ≤ b * c := mul_le_mul_of_nonpos_left hc hb0
            exact ⟨a, c, by simp, by simp, le_trans hac h1, b, c, by simp, by simp, le_trans h2 hbc⟩
        · -- a < 0: a*d ≤ a*q ≤ a*c
          have had : a * d ≤ a * q := mul_le_mul_of_nonpos_left hq ha0
          rcases le_total 0 b with hb0 | hb0
          · have hbd : b * q ≤ b * d := mul_le_mul_of_nonneg_left hq hb0
            exact ⟨a, d, by simp, by simp, le_trans had h1, b, d, by simp, by simp, le_trans h2 hbd⟩
          · have hbc : b * q ≤ b * c := mul_le_mul_of_nonpos_left hc hb0
            exact ⟨a, d, by simp, by simp, le_trans had h1, b, c, by simp, by simp, le_trans h2 hbc⟩
      · -- p ≤ 0: p*d ≤ p*q ≤ p*c
        rcases le_total 0 a with ha0 | ha0
        · have hac : a * c ≤ a * q := mul_le_mul_of_nonneg_left hc ha0
          rcases le_total 0 b with hb0 | hb0
          · have hbd : b * q ≤ b * d := mul_le_mul_of_nonneg_left hq hb0
            exact ⟨a, c, by simp, by simp, le_trans hac h1, b, d, by simp, by simp, le_trans h2 hbd⟩
          · have hbc : b * q ≤ b * c := mul_le_mul_of_nonpos_left hc hb0
            exact ⟨a, c, by simp, by simp, le_trans hac h1, b, c, by simp, by simp, le_trans h2 hbc⟩
        · have had : a * d ≤ a * q := mul_le_mul_of_nonpos_left hq ha0
          rcases le_total 0 b with hb0 | hb0
          · have hbd : b * q ≤ b * d := mul_le_mul_of_nonneg_left hq hb0
            exact ⟨a, d, by simp, by simp, le_trans had h1, b, d, by simp, by simp, le_trans h2 hbd⟩
          · have hbc : b * q ≤ b * c := mul_le_mul_of_nonpos_left hc hb0
            exact ⟨a, d, by simp, by simp, le_trans had h1, b, c, by simp, by simp, le_trans h2 hbc⟩
    · -- q ≤ 0: p*q decreasing in p, so b*q ≤ p*q ≤ a*q
      have h1 : b * q ≤ p * q := mul_le_mul_of_nonpos_right hp hq0
      have h2 : p * q ≤ a * q := mul_le_mul_of_nonpos_right ha hq0
      -- For a ≥ 0 and q ≤ 0: since c ≤ q ≤ d, we get a*d ≤ a*q ≤ a*c (q ≤ d means a*q ≤ a*d? No!)
      -- Actually: c ≤ q means a*c ≤ a*q if a ≥ 0. And q ≤ d means a*q ≤ a*d if a ≥ 0.
      -- So a*c ≤ a*q ≤ a*d. Upper bound on p*q uses a*d.
      rcases le_total 0 a with ha0 | ha0
      · -- a ≥ 0: a*c ≤ a*q ≤ a*d
        have hac_le : a * c ≤ a * q := mul_le_mul_of_nonneg_left hc ha0
        have haq_le : a * q ≤ a * d := mul_le_mul_of_nonneg_left hq ha0
        rcases le_total 0 b with hb0 | hb0
        · -- b ≥ 0: b*c ≤ b*q ≤ b*d
          have hbc_le : b * c ≤ b * q := mul_le_mul_of_nonneg_left hc hb0
          exact ⟨b, c, by simp, by simp, le_trans hbc_le h1, a, d, by simp, by simp, le_trans h2 haq_le⟩
        · -- b ≤ 0: b*d ≤ b*q ≤ b*c
          have hbd_le : b * d ≤ b * q := mul_le_mul_of_nonpos_left hq hb0
          exact ⟨b, d, by simp, by simp, le_trans hbd_le h1, a, d, by simp, by simp, le_trans h2 haq_le⟩
      · -- a ≤ 0: a*d ≤ a*q ≤ a*c
        have had_le : a * d ≤ a * q := mul_le_mul_of_nonpos_left hq ha0
        have haq_le : a * q ≤ a * c := mul_le_mul_of_nonpos_left hc ha0
        rcases le_total 0 b with hb0 | hb0
        · -- b ≥ 0: b*c ≤ b*q ≤ b*d
          have hbc_le : b * c ≤ b * q := mul_le_mul_of_nonneg_left hc hb0
          exact ⟨b, c, by simp, by simp, le_trans hbc_le h1, a, c, by simp, by simp, le_trans h2 haq_le⟩
        · -- b ≤ 0: b*d ≤ b*q ≤ b*c
          have hbd_le : b * d ≤ b * q := mul_le_mul_of_nonpos_left hq hb0
          exact ⟨b, d, by simp, by simp, le_trans hbd_le h1, a, c, by simp, by simp, le_trans h2 haq_le⟩
  obtain ⟨i, j, hi, hj, hij_le, i', j', hi', hj', le_ij'⟩ := h_pq_bounds
  constructor
  · -- Lower bound
    simp only [min_le_iff]
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · left; left; exact hij_le
    · left; right; exact hij_le
    · right; left; exact hij_le
    · right; right; exact hij_le
  · -- Upper bound
    simp only [le_max_iff]
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl
    · left; left; exact le_ij'
    · left; right; exact le_ij'
    · right; left; exact le_ij'
    · right; right; exact le_ij'

/-- Helper: foldl min on 4 elements equals mathematical min -/
private lemma foldl_min_four_eq (p1 p2 p3 p4 : D) :
    toRat ([p2, p3, p4].foldl (fun acc p => if toRat p < toRat acc then p else acc) p1) =
    min (min (toRat p1) (toRat p2)) (min (toRat p3) (toRat p4)) := by
  simp only [List.foldl]
  split_ifs <;> simp only [min_def] <;> split_ifs <;> linarith

/-- Helper: foldl max on 4 elements equals mathematical max -/
private lemma foldl_max_four_eq (p1 p2 p3 p4 : D) :
    toRat ([p2, p3, p4].foldl (fun acc p => if toRat p > toRat acc then p else acc) p1) =
    max (max (toRat p1) (toRat p2)) (max (toRat p3) (toRat p4)) := by
  simp only [List.foldl]
  split_ifs <;> simp only [max_def] <;> split_ifs <;> linarith

theorem mul_contains (x y : IntervalD) (precision : ℕ)
    (_hx : contains x (midpoint x)) (_hy : contains y (midpoint y)) :
    contains (mul x y precision) (midpoint x * midpoint y) := by
  unfold contains midpoint mul
  set p1 := DyadicCanonical.mul x.lower y.lower
  set p2 := DyadicCanonical.mul x.lower y.upper
  set p3 := DyadicCanonical.mul x.upper y.lower
  set p4 := DyadicCanonical.mul x.upper y.upper
  set mx := (toRat x.lower + toRat x.upper) / 2
  set my := (toRat y.lower + toRat y.upper) / 2
  have hx_valid : toRat x.lower ≤ toRat x.upper := (le_iff_toRat_le _ _).mp x.valid
  have hy_valid : toRat y.lower ≤ toRat y.upper := (le_iff_toRat_le _ _).mp y.valid
  have hx_mid_lower : toRat x.lower ≤ mx := by simp only [mx]; linarith [hx_valid]
  have hx_mid_upper : mx ≤ toRat x.upper := by simp only [mx]; linarith [hx_valid]
  have hy_mid_lower : toRat y.lower ≤ my := by simp only [my]; linarith [hy_valid]
  have hy_mid_upper : my ≤ toRat y.upper := by simp only [my]; linarith [hy_valid]
  have hbounds := product_in_corner_bounds
    (toRat x.lower) (toRat x.upper) (toRat y.lower) (toRat y.upper) mx my
    hx_mid_lower hx_mid_upper hy_mid_lower hy_mid_upper
  have hp1 : toRat p1 = toRat x.lower * toRat y.lower := DyadicCanonical.toRat_mul _ _
  have hp2 : toRat p2 = toRat x.lower * toRat y.upper := DyadicCanonical.toRat_mul _ _
  have hp3 : toRat p3 = toRat x.upper * toRat y.lower := DyadicCanonical.toRat_mul _ _
  have hp4 : toRat p4 = toRat x.upper * toRat y.upper := DyadicCanonical.toRat_mul _ _
  constructor
  · calc toRat (floor ([p2, p3, p4].foldl _ p1) precision)
        ≤ toRat ([p2, p3, p4].foldl (fun acc p => if toRat p < toRat acc then p else acc) p1) :=
            floor_le _ precision
      _ = min (min (toRat p1) (toRat p2)) (min (toRat p3) (toRat p4)) := foldl_min_four_eq p1 p2 p3 p4
      _ = min (min (toRat x.lower * toRat y.lower) (toRat x.lower * toRat y.upper))
            (min (toRat x.upper * toRat y.lower) (toRat x.upper * toRat y.upper)) := by rw [hp1, hp2, hp3, hp4]
      _ ≤ mx * my := hbounds.1
  · calc mx * my
        ≤ max (max (toRat x.lower * toRat y.lower) (toRat x.lower * toRat y.upper))
            (max (toRat x.upper * toRat y.lower) (toRat x.upper * toRat y.upper)) := hbounds.2
      _ = max (max (toRat p1) (toRat p2)) (max (toRat p3) (toRat p4)) := by rw [hp1, hp2, hp3, hp4]
      _ = toRat ([p2, p3, p4].foldl (fun acc p => if toRat p > toRat acc then p else acc) p1) :=
            (foldl_max_four_eq p1 p2 p3 p4).symm
      _ ≤ toRat (ceil ([p2, p3, p4].foldl _ p1) precision) := le_ceil _ precision

/-! ## Width bounds (error accumulation) -/

theorem add_width_bound (x y : IntervalD) (p : ℕ) :
    width (add x y p) ≤ width x + width y + 4 / (2^p : ℚ) := by
  unfold width add
  have floor_error : toRat (DyadicCanonical.add x.lower y.lower) -
                     toRat (floor (DyadicCanonical.add x.lower y.lower) p)
                   ≤ 2 / (2^p : ℚ) := by
    have hle := floor_le (DyadicCanonical.add x.lower y.lower) p
    have hceil := le_ceil (DyadicCanonical.add x.lower y.lower) p
    have hrounding := roundingError_bounded (DyadicCanonical.add x.lower y.lower) p
    have key : toRat (ceil (DyadicCanonical.add x.lower y.lower) p) -
               toRat (floor (DyadicCanonical.add x.lower y.lower) p) ≤ 2 / (2^p : ℚ) := by
      have h1 : (0 : ℝ) ≤ (toRat (ceil (DyadicCanonical.add x.lower y.lower) p) : ℝ) -
                          (toRat (floor (DyadicCanonical.add x.lower y.lower) p) : ℝ) := by
        simp only [sub_nonneg]
        exact_mod_cast (le_trans hle hceil)
      have h2 := hrounding
      rw [abs_of_nonneg h1] at h2
      by_contra hcon
      push_neg at hcon
      have hcon_r : ((2 : ℚ) / (2^p : ℚ) : ℝ) < ((toRat (ceil (DyadicCanonical.add x.lower y.lower) p) -
                      toRat (floor (DyadicCanonical.add x.lower y.lower) p) : ℚ) : ℝ) := by
        exact_mod_cast hcon
      simp only [Rat.cast_sub, Rat.cast_ofNat, Rat.cast_pow] at hcon_r
      linarith
    calc toRat (DyadicCanonical.add x.lower y.lower) -
         toRat (floor (DyadicCanonical.add x.lower y.lower) p)
        ≤ toRat (ceil (DyadicCanonical.add x.lower y.lower) p) -
          toRat (floor (DyadicCanonical.add x.lower y.lower) p) := by linarith [hceil]
      _ ≤ 2 / (2^p : ℚ) := key

  have ceil_error : toRat (ceil (DyadicCanonical.add x.upper y.upper) p) -
                    toRat (DyadicCanonical.add x.upper y.upper)
                  ≤ 2 / (2^p : ℚ) := by
    have hle := floor_le (DyadicCanonical.add x.upper y.upper) p
    have hceil := le_ceil (DyadicCanonical.add x.upper y.upper) p
    have hrounding := roundingError_bounded (DyadicCanonical.add x.upper y.upper) p
    have key : toRat (ceil (DyadicCanonical.add x.upper y.upper) p) -
               toRat (floor (DyadicCanonical.add x.upper y.upper) p) ≤ 2 / (2^p : ℚ) := by
      have h1 : (0 : ℝ) ≤ (toRat (ceil (DyadicCanonical.add x.upper y.upper) p) : ℝ) -
                          (toRat (floor (DyadicCanonical.add x.upper y.upper) p) : ℝ) := by
        simp only [sub_nonneg]
        exact_mod_cast (le_trans hle hceil)
      have h2 := hrounding
      rw [abs_of_nonneg h1] at h2
      by_contra hcon
      push_neg at hcon
      have hcon_r : ((2 : ℚ) / (2^p : ℚ) : ℝ) < ((toRat (ceil (DyadicCanonical.add x.upper y.upper) p) -
                      toRat (floor (DyadicCanonical.add x.upper y.upper) p) : ℚ) : ℝ) := by
        exact_mod_cast hcon
      simp only [Rat.cast_sub, Rat.cast_ofNat, Rat.cast_pow] at hcon_r
      linarith
    calc toRat (ceil (DyadicCanonical.add x.upper y.upper) p) -
         toRat (DyadicCanonical.add x.upper y.upper)
        ≤ toRat (ceil (DyadicCanonical.add x.upper y.upper) p) -
          toRat (floor (DyadicCanonical.add x.upper y.upper) p) := by linarith [hle]
      _ ≤ 2 / (2^p : ℚ) := key

  calc toRat (ceil (DyadicCanonical.add x.upper y.upper) p) -
       toRat (floor (DyadicCanonical.add x.lower y.lower) p)
      = (toRat (ceil (DyadicCanonical.add x.upper y.upper) p) -
         toRat (DyadicCanonical.add x.upper y.upper)) +
        (toRat (DyadicCanonical.add x.upper y.upper) - toRat (DyadicCanonical.add x.lower y.lower)) +
        (toRat (DyadicCanonical.add x.lower y.lower) -
         toRat (floor (DyadicCanonical.add x.lower y.lower) p)) := by ring
    _ ≤ 2 / (2^p : ℚ) +
        (toRat (DyadicCanonical.add x.upper y.upper) - toRat (DyadicCanonical.add x.lower y.lower)) +
        2 / (2^p : ℚ) := by linarith
    _ = (toRat x.upper + toRat y.upper) - (toRat x.lower + toRat y.lower) + 4 / (2^p : ℚ) := by
          rw [DyadicCanonical.toRat_add, DyadicCanonical.toRat_add]; ring
    _ = width x + width y + 4 / (2^p : ℚ) := by unfold width; ring

set_option maxHeartbeats 2000000 in
/-- Key lemma: max-min of four corner products bounded by interval arithmetic formula.
    For intervals [a,b] and [c,d], the spread of corners {ac,ad,bc,bd} satisfies:
    max(corners) - min(corners) ≤ (b-a)*|mid_y| + (d-c)*|mid_x| + (b-a)*(d-c)

    Standard result in interval arithmetic - uses triangle inequality on differences.
    See Moore's "Interval Analysis" for derivation. -/
private lemma corner_spread_bound (a b c d : ℚ) (hab : a ≤ b) (hcd : c ≤ d) :
    max (max (a*c) (a*d)) (max (b*c) (b*d)) - min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤
    (b - a) * abs ((c + d) / 2) + (d - c) * abs ((a + b) / 2) + (b - a) * (d - c) := by
  -- Key: max - min ≤ (b-a)*max(|c|,|d|) + (d-c)*max(|a|,|b|)
  --      ≤ (b-a)*(|mid_y|+wy/2) + (d-c)*(|mid_x|+wx/2)
  --      = (b-a)*|mid_y| + (d-c)*|mid_x| + (b-a)*(d-c)
  have hwx : 0 ≤ b - a := by linarith
  have hwy : 0 ≤ d - c := by linarith
  -- First show max(|c|,|d|) ≤ |mid_y| + (d-c)/2
  have hmy : max (abs c) (abs d) ≤ abs ((c + d) / 2) + (d - c) / 2 := by
    have h1 : abs c ≤ abs ((c + d) / 2) + (d - c) / 2 := by
      rcases le_or_gt 0 c with hc_nn | hc_neg
      · simp only [abs_of_nonneg hc_nn]
        rcases le_or_gt 0 ((c + d) / 2) with hm_nn | hm_neg
        · simp only [abs_of_nonneg hm_nn]; linarith
        · simp only [abs_of_neg hm_neg]; linarith
      · simp only [abs_of_neg hc_neg]
        rcases le_or_gt 0 ((c + d) / 2) with hm_nn | hm_neg
        · simp only [abs_of_nonneg hm_nn]; linarith
        · simp only [abs_of_neg hm_neg]; linarith
    have h2 : abs d ≤ abs ((c + d) / 2) + (d - c) / 2 := by
      rcases le_or_gt 0 d with hd_nn | hd_neg
      · simp only [abs_of_nonneg hd_nn]
        rcases le_or_gt 0 ((c + d) / 2) with hm_nn | hm_neg
        · simp only [abs_of_nonneg hm_nn]; linarith
        · simp only [abs_of_neg hm_neg]; linarith
      · simp only [abs_of_neg hd_neg]
        rcases le_or_gt 0 ((c + d) / 2) with hm_nn | hm_neg
        · simp only [abs_of_nonneg hm_nn]; linarith
        · simp only [abs_of_neg hm_neg]; linarith
    exact max_le h1 h2
  -- Similarly for max(|a|,|b|)
  have hmx : max (abs a) (abs b) ≤ abs ((a + b) / 2) + (b - a) / 2 := by
    have h1 : abs a ≤ abs ((a + b) / 2) + (b - a) / 2 := by
      rcases le_or_gt 0 a with ha_nn | ha_neg
      · simp only [abs_of_nonneg ha_nn]
        rcases le_or_gt 0 ((a + b) / 2) with hm_nn | hm_neg
        · simp only [abs_of_nonneg hm_nn]; linarith
        · simp only [abs_of_neg hm_neg]; linarith
      · simp only [abs_of_neg ha_neg]
        rcases le_or_gt 0 ((a + b) / 2) with hm_nn | hm_neg
        · simp only [abs_of_nonneg hm_nn]; linarith
        · simp only [abs_of_neg hm_neg]; linarith
    have h2 : abs b ≤ abs ((a + b) / 2) + (b - a) / 2 := by
      rcases le_or_gt 0 b with hb_nn | hb_neg
      · simp only [abs_of_nonneg hb_nn]
        rcases le_or_gt 0 ((a + b) / 2) with hm_nn | hm_neg
        · simp only [abs_of_nonneg hm_nn]; linarith
        · simp only [abs_of_neg hm_neg]; linarith
      · simp only [abs_of_neg hb_neg]
        rcases le_or_gt 0 ((a + b) / 2) with hm_nn | hm_neg
        · simp only [abs_of_nonneg hm_nn]; linarith
        · simp only [abs_of_neg hm_neg]; linarith
    exact max_le h1 h2
  -- The spread is bounded by (b-a)*max|y| + (d-c)*max|x|
  -- which is ≤ (b-a)*(|mid_y|+wy/2) + (d-c)*(|mid_x|+wx/2)
  -- Since we want: max - min ≤ (b-a)*|mid_y| + (d-c)*|mid_x| + (b-a)*(d-c)
  -- We prove directly by analyzing all pairwise corner differences
  have hmaxc : 0 ≤ max (abs c) (abs d) := le_trans (abs_nonneg c) (le_max_left _ _)
  have hmaxa : 0 ≤ max (abs a) (abs b) := le_trans (abs_nonneg a) (le_max_left _ _)
  -- Key: each corner difference x*y - x'*y' ≤ wx*max|y| + wy*max|x|
  -- For same-x edges: a*d - a*c = a*(d-c), so |a*d - a*c| ≤ |a|*wy ≤ max|a|*wy
  -- For same-y edges: b*c - a*c = c*(b-a), so |b*c - a*c| ≤ |c|*wx ≤ max|c|*wx
  -- For diagonals: use triangle inequality on path through intermediate corner
  -- Using the simple bound: all corners in [-M,M] where M = max|a|*max|c|
  -- So max - min ≤ 2M. But we need wx*max|c| + wy*max|a|.
  -- We prove this by explicit path: max-corner to min-corner via ≤2 edge steps

  -- Simplify: just prove the stronger bound directly using nlinarith with sq hints
  have hspread : max (max (a*c) (a*d)) (max (b*c) (b*d)) - min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤
      (b - a) * max (abs c) (abs d) + (d - c) * max (abs a) (abs b) := by
    -- For each of the 16 corner pairs, the difference is bounded
    -- The bound follows since max-min equals the difference between some max-corner and some min-corner
    have key : ∀ p q : ℚ, p ∈ ({a*c, a*d, b*c, b*d} : Set ℚ) → q ∈ ({a*c, a*d, b*c, b*d} : Set ℚ) →
        p - q ≤ (b - a) * max (abs c) (abs d) + (d - c) * max (abs a) (abs b) := by
      intros p q hp hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
      -- Enumerate all 16 cases
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
        nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d,
                   sq_nonneg (a-b), sq_nonneg (c-d), sq_nonneg (a+b), sq_nonneg (c+d),
                   abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg d,
                   le_max_left (abs a) (abs b), le_max_right (abs a) (abs b),
                   le_max_left (abs c) (abs d), le_max_right (abs c) (abs d),
                   le_abs_self a, neg_le_abs a, le_abs_self b, neg_le_abs b,
                   le_abs_self c, neg_le_abs c, le_abs_self d, neg_le_abs d]
    -- The max is one of the corners, min is another
    have hmax_in : max (max (a*c) (a*d)) (max (b*c) (b*d)) ∈ ({a*c, a*d, b*c, b*d} : Set ℚ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, max_def]; split_ifs <;> tauto
    have hmin_in : min (min (a*c) (a*d)) (min (b*c) (b*d)) ∈ ({a*c, a*d, b*c, b*d} : Set ℚ) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, min_def]; split_ifs <;> tauto
    exact key _ _ hmax_in hmin_in
  calc max (max (a*c) (a*d)) (max (b*c) (b*d)) - min (min (a*c) (a*d)) (min (b*c) (b*d))
      ≤ (b - a) * max (abs c) (abs d) + (d - c) * max (abs a) (abs b) := hspread
    _ ≤ (b - a) * (abs ((c + d) / 2) + (d - c) / 2) + (d - c) * (abs ((a + b) / 2) + (b - a) / 2) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hmy hwx
        · exact mul_le_mul_of_nonneg_left hmx hwy
    _ = (b - a) * abs ((c + d) / 2) + (d - c) * abs ((a + b) / 2) + (b - a) * (d - c) := by ring

/-- Width bound for multiplication. Standard result in interval arithmetic.

    The bound is: width([a,b]×[c,d]) ≤ width_x·|mid_y| + width_y·|mid_x| + width_x·width_y + rounding

    Proof deferred - requires technical but standard interval arithmetic analysis.
    See Moore's "Interval Analysis" for the formula derivation.
    Does not block extraction or execution. -/
theorem mul_width_bound (x y : IntervalD) (p : ℕ) :
    width (mul x y p) ≤
      width x * abs (midpoint y) + width y * abs (midpoint x) +
      width x * width y + 4 / (2^p : ℚ) := by
  unfold width mul midpoint
  set p1 := DyadicCanonical.mul x.lower y.lower
  set p2 := DyadicCanonical.mul x.lower y.upper
  set p3 := DyadicCanonical.mul x.upper y.lower
  set p4 := DyadicCanonical.mul x.upper y.upper
  set lower_raw := [p2, p3, p4].foldl (fun acc q => if toRat q < toRat acc then q else acc) p1
  set upper_raw := [p2, p3, p4].foldl (fun acc q => if toRat q > toRat acc then q else acc) p1
  have hrounding : toRat (ceil upper_raw p) - toRat (floor lower_raw p) ≤
      toRat upper_raw - toRat lower_raw + 4 / (2^p : ℚ) := by
    have hfloor := floor_le lower_raw p
    have hceil := le_ceil upper_raw p
    have hfround := roundingError_bounded lower_raw p
    have hfl_err : toRat lower_raw - toRat (floor lower_raw p) ≤ 2 / (2^p : ℚ) := by
      have hceil_l := le_ceil lower_raw p
      have key : toRat (ceil lower_raw p) - toRat (floor lower_raw p) ≤ 2 / (2^p : ℚ) := by
        have h1 : (0 : ℝ) ≤ (toRat (ceil lower_raw p) : ℝ) -
                            (toRat (floor lower_raw p) : ℝ) := by
          simp only [sub_nonneg]; exact_mod_cast (le_trans hfloor hceil_l)
        rw [abs_of_nonneg h1] at hfround
        by_contra hcon; push_neg at hcon
        have hcon_r : ((2 : ℚ) / (2^p : ℚ) : ℝ) < ((toRat (ceil lower_raw p) -
                        toRat (floor lower_raw p) : ℚ) : ℝ) := by exact_mod_cast hcon
        simp only [Rat.cast_sub, Rat.cast_ofNat, Rat.cast_pow] at hcon_r; linarith
      linarith [hceil_l]
    have hcround := roundingError_bounded upper_raw p
    have hcl_err : toRat (ceil upper_raw p) - toRat upper_raw ≤ 2 / (2^p : ℚ) := by
      have hfloor_u := floor_le upper_raw p
      have key : toRat (ceil upper_raw p) - toRat (floor upper_raw p) ≤ 2 / (2^p : ℚ) := by
        have h1 : (0 : ℝ) ≤ (toRat (ceil upper_raw p) : ℝ) -
                            (toRat (floor upper_raw p) : ℝ) := by
          simp only [sub_nonneg]; exact_mod_cast (le_trans hfloor_u hceil)
        rw [abs_of_nonneg h1] at hcround
        by_contra hcon; push_neg at hcon
        have hcon_r : ((2 : ℚ) / (2^p : ℚ) : ℝ) < ((toRat (ceil upper_raw p) -
                        toRat (floor upper_raw p) : ℚ) : ℝ) := by exact_mod_cast hcon
        simp only [Rat.cast_sub, Rat.cast_ofNat, Rat.cast_pow] at hcon_r; linarith
      linarith [hfloor_u]
    calc toRat (ceil upper_raw p) - toRat (floor lower_raw p)
        = (toRat (ceil upper_raw p) - toRat upper_raw) +
          (toRat upper_raw - toRat lower_raw) +
          (toRat lower_raw - toRat (floor lower_raw p)) := by ring
      _ ≤ 2 / (2^p : ℚ) + (toRat upper_raw - toRat lower_raw) + 2 / (2^p : ℚ) := by linarith
      _ = toRat upper_raw - toRat lower_raw + 4 / (2^p : ℚ) := by ring
  have hraw_width : toRat upper_raw - toRat lower_raw ≤
      (toRat x.upper - toRat x.lower) * abs ((toRat y.lower + toRat y.upper) / 2) +
      (toRat y.upper - toRat y.lower) * abs ((toRat x.lower + toRat x.upper) / 2) +
      (toRat x.upper - toRat x.lower) * (toRat y.upper - toRat y.lower) := by
    have hp1 : toRat p1 = toRat x.lower * toRat y.lower := DyadicCanonical.toRat_mul _ _
    have hp2 : toRat p2 = toRat x.lower * toRat y.upper := DyadicCanonical.toRat_mul _ _
    have hp3 : toRat p3 = toRat x.upper * toRat y.lower := DyadicCanonical.toRat_mul _ _
    have hp4 : toRat p4 = toRat x.upper * toRat y.upper := DyadicCanonical.toRat_mul _ _
    have hmax := foldl_max_four_eq p1 p2 p3 p4
    have hmin := foldl_min_four_eq p1 p2 p3 p4
    have hx_valid : toRat x.lower ≤ toRat x.upper := (le_iff_toRat_le _ _).mp x.valid
    have hy_valid : toRat y.lower ≤ toRat y.upper := (le_iff_toRat_le _ _).mp y.valid
    rw [hmax, hmin, hp1, hp2, hp3, hp4]
    exact corner_spread_bound (toRat x.lower) (toRat x.upper) (toRat y.lower) (toRat y.upper) hx_valid hy_valid
  linarith

/-! ## Optimized power operations -/

/-- Cubic with monotonic optimization: [a,b]^3 = [a^3, b^3]

    Since x^3 is strictly monotonic (increasing), we don't need to check
    cross terms. This prevents interval explosion from naive multiplication.

    Width growth: O(input_width * x^2) instead of O(3 * input_width) -/
def cube (x : IntervalD) (precision : ℕ) : IntervalD :=
  let lSq := DyadicCanonical.mul x.lower x.lower
  let lCub := DyadicCanonical.mul lSq x.lower
  let uSq := DyadicCanonical.mul x.upper x.upper
  let uCub := DyadicCanonical.mul uSq x.upper

  ⟨floor lCub precision,
   ceil uCub precision,
   (le_iff_toRat_le _ _).mpr (by
     have h_mono : toRat lCub ≤ toRat uCub := by
       have hv := (le_iff_toRat_le _ _).mp x.valid
       simp only [lSq, lCub, uSq, uCub, DyadicCanonical.toRat_mul]
       have hodd : _root_.Odd 3 := ⟨1, by ring⟩
       have mono : StrictMono fun (x : ℚ) => x^3 := _root_.Odd.strictMono_pow hodd
       calc toRat x.lower * toRat x.lower * toRat x.lower
           = (toRat x.lower)^3 := by ring
         _ ≤ (toRat x.upper)^3 := mono.monotone hv
         _ = toRat x.upper * toRat x.upper * toRat x.upper := by ring
     exact floor_ceil_preserves_order h_mono)⟩

/-- Square with optimization: [a,b]^2

    For x^2, we need to handle the case where interval contains 0:
    - If 0 in [a,b]: min is 0, max is max(a^2, b^2)
    - If 0 not in [a,b]: endpoints give min and max -/
def square (x : IntervalD) (precision : ℕ) : IntervalD :=
  let lSq := DyadicCanonical.mul x.lower x.lower
  let uSq := DyadicCanonical.mul x.upper x.upper

  if h : toRat x.lower ≤ 0 ∧ 0 ≤ toRat x.upper then
    let maxSq := if toRat lSq > toRat uSq then lSq else uSq
    ⟨DyadicCanonical.zero,
     ceil maxSq precision,
     (le_iff_toRat_le _ _).mpr (by
       simp only [DyadicCanonical.zero_toRat]
       have h_sq_nonneg : 0 ≤ toRat maxSq := by
         simp only [maxSq]
         split_ifs
         · simp only [lSq, DyadicCanonical.toRat_mul]; nlinarith [sq_nonneg (toRat x.lower)]
         · simp only [uSq, DyadicCanonical.toRat_mul]; nlinarith [sq_nonneg (toRat x.upper)]
       exact le_trans h_sq_nonneg (le_ceil maxSq precision))⟩
  else if hpos : toRat x.lower > 0 then
    ⟨floor lSq precision,
     ceil uSq precision,
     (le_iff_toRat_le _ _).mpr (by
       have hlsq : toRat lSq ≤ toRat uSq := by
         simp only [lSq, uSq, DyadicCanonical.toRat_mul]
         have h1 : 0 < toRat x.lower := hpos
         have h2 : toRat x.lower ≤ toRat x.upper := (le_iff_toRat_le _ _).mp x.valid
         nlinarith [sq_nonneg (toRat x.lower - toRat x.upper)]
       exact floor_ceil_preserves_order hlsq)⟩
  else
    ⟨floor uSq precision,
     ceil lSq precision,
     (le_iff_toRat_le _ _).mpr (by
       push_neg at h
       have husq : toRat uSq ≤ toRat lSq := by
         simp only [lSq, uSq, DyadicCanonical.toRat_mul]
         have h1 : toRat x.lower ≤ 0 := le_of_not_gt hpos
         have h2 : toRat x.upper < 0 := h h1
         have h3 : toRat x.lower ≤ toRat x.upper := (le_iff_toRat_le _ _).mp x.valid
         nlinarith [sq_nonneg (toRat x.lower - toRat x.upper)]
       exact floor_ceil_preserves_order husq)⟩

/-! ## Utility functions -/

/-- Absolute value of interval -/
def abs (x : IntervalD) (precision : ℕ) : IntervalD :=
  if h1 : toRat x.lower ≥ 0 then
    x
  else if h2 : toRat x.upper ≤ 0 then
    neg x precision
  else
    let negLower := DyadicCanonical.neg x.lower
    let maxAbs := if toRat negLower > toRat x.upper then negLower else x.upper
    ⟨DyadicCanonical.zero,
     ceil maxAbs precision,
     (le_iff_toRat_le _ _).mpr (by
       simp only [DyadicCanonical.zero_toRat]
       push_neg at h1 h2
       have h_max_nonneg : 0 ≤ toRat maxAbs := by
         show 0 ≤ toRat (if toRat negLower > toRat x.upper then negLower else x.upper)
         split_ifs with hcmp
         · simp only [negLower, DyadicCanonical.toRat_neg]; linarith
         · linarith
       exact le_trans h_max_nonneg (le_ceil maxAbs precision))⟩

/-- Scale by integer (exact when k is power of 2) -/
def scaleInt (x : IntervalD) (k : ℤ) (precision : ℕ) : IntervalD :=
  let kD := DyadicCanonical.ofInt k
  mul x (exact kD) precision

/-- Convert to rational (uses midpoint) -/
def toRational (x : IntervalD) : ℚ := midpoint x

/-- Get error bound (half width) -/
def errorBound (x : IntervalD) : ℚ := width x / 2

/-- Half: divide by 2 (exact operation for dyadics) -/
def half (x : IntervalD) : IntervalD :=
  ⟨DyadicCanonical.half x.lower, DyadicCanonical.half x.upper,
   (le_iff_toRat_le _ _).mpr (by
     have h1 : toRat (DyadicCanonical.half x.lower) = toRat x.lower / 2 := DyadicCanonical.toRat_half x.lower
     have h2 : toRat (DyadicCanonical.half x.upper) = toRat x.upper / 2 := DyadicCanonical.toRat_half x.upper
     rw [h1, h2]
     have hv : toRat x.lower ≤ toRat x.upper := (le_iff_toRat_le _ _).mp x.valid
     exact div_le_div_of_nonneg_right hv (by norm_num : (0 : ℚ) ≤ 2))⟩

/-- Square root via Newton's method with interval arithmetic

    For interval [a, b] with a,b ≥ 0, computes interval containing √[a,b]

    Uses Newton iteration: x_{n+1} = (x_n + y/x_n) / 2
    where y is the interval and x_n is the approximation
-/
def sqrt (y : IntervalD) (p : ℕ := 53) : IntervalD :=
  -- Check if interval is non-negative
  if _h : toRat y.lower < 0 then
    -- Negative input: return zero interval (could error instead)
    zero
  else
    -- Initial guess: use upper bound's rational value
    let mid_q := midpoint y
    let guess_q := if mid_q ≤ 1 then 1/2 else mid_q / 2
    let guess := fromRat guess_q p

    -- Newton iteration: x_new = (x + y/x) / 2
    let rec newton (x : IntervalD) (fuel : ℕ) : IntervalD :=
      match fuel with
      | 0 => x
      | n+1 =>
        -- y / x with interval division
        let y_over_x := div y x p
        -- (x + y/x)
        let sum := add x y_over_x p
        -- Divide by 2
        let x_next := half sum

        -- Check convergence: if width small enough, stop
        if width x_next < (1 : ℚ) / (2^p) then
          x_next
        else
          newton x_next n

    newton guess 20

end IntervalDyadic

export IntervalDyadic (fromRat_contains)
