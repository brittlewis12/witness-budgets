import Budgets.IntervalDyadic

/-!
# Witness Arithmetic Preservation

This module contains theorems proving that interval arithmetic operations
preserve the witness relationship between intervals and rationals.

## Main theorems

- `add_preserves_containment`: Addition of intervals contains sum of rationals
- `mul_preserves_containment`: Multiplication of intervals contains product of rationals
- `neg_preserves_containment`: Negation of intervals contains negation of rationals
- `sub_preserves_containment`: Subtraction of intervals contains difference of rationals
- `scalar_mul_preserves_containment`: Scalar multiplication preserves containment
- `complex_mul_preserves_witness`: Complex multiplication preserves witness for coefficient pairs

These theorems are the foundation for proving that array-based interval computations
correctly witness mathematical rational operations.
-/

namespace Witness

open IntervalDyadic

/-- An interval contains a rational number if the rational lies in [lower, upper].

This is the semantic meaning of interval arithmetic: the true value is
guaranteed to lie within the computed bounds. -/
def intervalContains (iv : IntervalD) (q : ℚ) : Prop :=
  DyadicCanonical.toRat iv.lower ≤ q ∧ q ≤ DyadicCanonical.toRat iv.upper

/-! ## Helper lemmas for interval containment -/

/-- The fromRat interval is wide enough to contain the rational itself.
    This is now guaranteed by the widened interval construction in fromRat,
    which explicitly adds margin to ensure containment. -/
lemma fromRat_contains_rat (q : ℚ) (p : ℕ) :
    intervalContains (IntervalDyadic.fromRat q p) q := by
  -- Use the proven containment theorem from IntervalDyadic
  have h := IntervalDyadic.fromRat_contains q p
  -- Unfold to show equivalence of contains and intervalContains
  unfold intervalContains IntervalDyadic.contains at *
  exact h

/-- Zero interval contains zero exactly -/
lemma zero_contains_zero :
    intervalContains IntervalDyadic.zero 0 := by
  unfold intervalContains IntervalDyadic.zero IntervalDyadic.exact
  simp [DyadicCanonical.toRat, DyadicCanonical.zero]

/-! ## Arithmetic Preservation Theorems -/

/-- Addition preserves interval containment.
    If intervals x and y contain rationals a and b respectively,
    then their sum contains a + b. -/
theorem add_preserves_containment (x y : IntervalD) (a b : ℚ) (p : ℕ)
    (hx : intervalContains x a) (hy : intervalContains y b) :
    intervalContains (IntervalDyadic.add x y p) (a + b) := by
  unfold intervalContains IntervalDyadic.add
  constructor
  · -- Lower bound: floor(x.lower + y.lower) ≤ a + b
    calc DyadicCanonical.toRat (RoundedDyadic.floor (DyadicCanonical.add x.lower y.lower) p)
        ≤ DyadicCanonical.toRat (DyadicCanonical.add x.lower y.lower) :=
            RoundedDyadic.floor_le _ p
      _ = DyadicCanonical.toRat x.lower + DyadicCanonical.toRat y.lower :=
            DyadicCanonical.toRat_add _ _
      _ ≤ a + b := add_le_add hx.1 hy.1
  · -- Upper bound: a + b ≤ ceil(x.upper + y.upper)
    calc a + b
        ≤ DyadicCanonical.toRat x.upper + DyadicCanonical.toRat y.upper :=
            add_le_add hx.2 hy.2
      _ = DyadicCanonical.toRat (DyadicCanonical.add x.upper y.upper) :=
            (DyadicCanonical.toRat_add _ _).symm
      _ ≤ DyadicCanonical.toRat (RoundedDyadic.ceil (DyadicCanonical.add x.upper y.upper) p) :=
            RoundedDyadic.le_ceil _ p

/-! ## Rigorous Interval Multiplication Proofs

  Strategy: Instead of case-splitting on 16 sign combinations, we use the structural
  property that extrema of linear functions on intervals occur at boundaries.

  Key insight: For c·x where x ∈ [l,u], the product is bounded by min(c·l, c·u) and max(c·l, c·u),
  regardless of signs. This reduces the 4-variable problem to two 2-variable applications.
-/

/-- Helper: Multiplication by a constant is bounded by the min/max of endpoint products.
    This works for any sign of c, avoiding case explosion. -/
private lemma mul_bounded_by_endpoints (c : ℚ) (x l u : ℚ) (h : l ≤ x ∧ x ≤ u) :
    min (c * l) (c * u) ≤ c * x ∧ c * x ≤ max (c * l) (c * u) := by
  by_cases hc : 0 ≤ c
  · -- Case c ≥ 0: order-preserving, so c*l ≤ c*x ≤ c*u
    have h1 : c * l ≤ c * x := mul_le_mul_of_nonneg_left h.1 hc
    have h2 : c * x ≤ c * u := mul_le_mul_of_nonneg_left h.2 hc
    constructor
    · -- min(c*l, c*u) = c*l ≤ c*x
      have : min (c * l) (c * u) = c * l := by
        rw [min_eq_left]
        exact mul_le_mul_of_nonneg_left (h.1.trans h.2) hc
      rw [this]
      exact h1
    · -- c*x ≤ c*u = max(c*l, c*u)
      have : max (c * l) (c * u) = c * u := by
        rw [max_eq_right]
        exact mul_le_mul_of_nonneg_left (h.1.trans h.2) hc
      rw [this]
      exact h2
  · -- Case c < 0: order-reversing, so c*u ≤ c*x ≤ c*l
    push_neg at hc
    have hc' : c ≤ 0 := le_of_lt hc
    have h1 : c * u ≤ c * x := mul_le_mul_of_nonpos_left h.2 hc'
    have h2 : c * x ≤ c * l := mul_le_mul_of_nonpos_left h.1 hc'
    constructor
    · -- min(c*l, c*u) = c*u ≤ c*x
      have : min (c * l) (c * u) = c * u := by
        rw [min_eq_right]
        exact mul_le_mul_of_nonpos_left (h.1.trans h.2) hc'
      rw [this]
      exact h1
    · -- c*x ≤ c*l = max(c*l, c*u)
      have : max (c * l) (c * u) = c * l := by
        rw [max_eq_left]
        exact mul_le_mul_of_nonpos_left (h.1.trans h.2) hc'
      rw [this]
      exact h2

/-- Helper lemma: product of values in intervals is bounded by min of corner products.

    Proof strategy:
    1. Fix b, apply mul_bounded_by_endpoints to show a·b ≥ min(x.lower·b, x.upper·b)
    2. For each of x.lower and x.upper, apply mul_bounded_by_endpoints again with y's bounds
    3. Combine via transitivity
-/
private lemma product_ge_min_corner (x y : IntervalD) (a b : ℚ)
    (hx : intervalContains x a) (hy : intervalContains y b) :
    min (min (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.lower)
             (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.upper))
        (min (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.lower)
             (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.upper)) ≤ a * b := by
  unfold intervalContains at hx hy

  -- Step 1: a·b is bounded by varying a (for fixed b)
  have step1 := mul_bounded_by_endpoints b a (DyadicCanonical.toRat x.lower) (DyadicCanonical.toRat x.upper) hx

  -- Step 2: For any constant C, C·b is bounded by varying b
  have lower_bound_y : ∀ C : ℚ,
      min (C * DyadicCanonical.toRat y.lower) (C * DyadicCanonical.toRat y.upper) ≤ C * b := by
    intro C
    exact (mul_bounded_by_endpoints C b (DyadicCanonical.toRat y.lower) (DyadicCanonical.toRat y.upper) hy).1

  -- Step 3: Apply to both x.lower and x.upper
  have h_lower : min (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.lower)
                     (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.upper)
                 ≤ DyadicCanonical.toRat x.lower * b :=
    lower_bound_y (DyadicCanonical.toRat x.lower)

  have h_upper : min (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.lower)
                     (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.upper)
                 ≤ DyadicCanonical.toRat x.upper * b :=
    lower_bound_y (DyadicCanonical.toRat x.upper)

  -- Step 4: Combine via transitivity
  -- Global min ≤ min(x.lower·b, x.upper·b) ≤ a·b
  -- Need to use mul_comm to convert step1.left from "b * a" form to "a * b" form
  have step1_comm_left : min (DyadicCanonical.toRat x.lower * b) (DyadicCanonical.toRat x.upper * b) ≤ a * b := by
    rw [mul_comm (DyadicCanonical.toRat x.lower) b, mul_comm (DyadicCanonical.toRat x.upper) b, mul_comm a b]
    exact step1.1

  calc min (min (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.lower)
                (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.upper))
           (min (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.lower)
                (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.upper))
      ≤ min (DyadicCanonical.toRat x.lower * b) (DyadicCanonical.toRat x.upper * b) :=
          min_le_min h_lower h_upper
    _ ≤ a * b := step1_comm_left

/-- Helper lemma: product of values in intervals is bounded by max of corner products.
    Symmetric to product_ge_min_corner, using max instead of min. -/
private lemma product_le_max_corner (x y : IntervalD) (a b : ℚ)
    (hx : intervalContains x a) (hy : intervalContains y b) :
    a * b ≤ max (max (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.lower)
                     (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.upper))
             (max (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.lower)
                  (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.upper)) := by
  unfold intervalContains at hx hy

  -- Step 1: a·b is bounded by varying a (for fixed b)
  have step1 := mul_bounded_by_endpoints b a (DyadicCanonical.toRat x.lower) (DyadicCanonical.toRat x.upper) hx

  -- Step 2: For any constant C, C·b is bounded by varying b
  have upper_bound_y : ∀ C : ℚ,
      C * b ≤ max (C * DyadicCanonical.toRat y.lower) (C * DyadicCanonical.toRat y.upper) := by
    intro C
    exact (mul_bounded_by_endpoints C b (DyadicCanonical.toRat y.lower) (DyadicCanonical.toRat y.upper) hy).2

  -- Step 3: Apply to both x.lower and x.upper
  have h_lower : DyadicCanonical.toRat x.lower * b
                 ≤ max (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.lower)
                       (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.upper) :=
    upper_bound_y (DyadicCanonical.toRat x.lower)

  have h_upper : DyadicCanonical.toRat x.upper * b
                 ≤ max (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.lower)
                       (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.upper) :=
    upper_bound_y (DyadicCanonical.toRat x.upper)

  -- Step 4: Combine via transitivity
  -- a·b ≤ max(x.lower·b, x.upper·b) ≤ Global max
  -- Need to use mul_comm to convert step1.right from "b * a" form to "a * b" form
  have step1_comm_right : a * b ≤ max (DyadicCanonical.toRat x.lower * b) (DyadicCanonical.toRat x.upper * b) := by
    rw [mul_comm (DyadicCanonical.toRat x.lower) b, mul_comm (DyadicCanonical.toRat x.upper) b, mul_comm a b]
    exact step1.2

  calc a * b
      ≤ max (DyadicCanonical.toRat x.lower * b) (DyadicCanonical.toRat x.upper * b) := step1_comm_right
    _ ≤ max (max (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.lower)
                 (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.upper))
            (max (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.lower)
                 (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.upper)) :=
          max_le_max h_lower h_upper

/-- Multiplication preserves interval containment.
    If intervals x and y contain rationals a and b respectively,
    then their product contains a * b.

    This relies on the fact that interval multiplication computes bounds
    by considering all four corner products. -/
theorem mul_preserves_containment (x y : IntervalD) (a b : ℚ) (p : ℕ)
    (hx : intervalContains x a) (hy : intervalContains y b) :
    intervalContains (IntervalDyadic.mul x y p) (a * b) := by
  unfold intervalContains IntervalDyadic.mul
  -- Define the four corner products
  set p1 := DyadicCanonical.mul x.lower y.lower
  set p2 := DyadicCanonical.mul x.lower y.upper
  set p3 := DyadicCanonical.mul x.upper y.lower
  set p4 := DyadicCanonical.mul x.upper y.upper
  set lower_raw := [p2, p3, p4].foldl
    (fun acc p => if DyadicCanonical.toRat p < DyadicCanonical.toRat acc then p else acc) p1
  set upper_raw := [p2, p3, p4].foldl
    (fun acc p => if DyadicCanonical.toRat p > DyadicCanonical.toRat acc then p else acc) p1

  -- Establish rational values of corners
  have hp1 : DyadicCanonical.toRat p1 = DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.lower :=
    DyadicCanonical.toRat_mul _ _
  have hp2 : DyadicCanonical.toRat p2 = DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.upper :=
    DyadicCanonical.toRat_mul _ _
  have hp3 : DyadicCanonical.toRat p3 = DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.lower :=
    DyadicCanonical.toRat_mul _ _
  have hp4 : DyadicCanonical.toRat p4 = DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.upper :=
    DyadicCanonical.toRat_mul _ _

  constructor
  · -- Lower bound: floor(min(corners)) ≤ a * b
    have hlower_eq : DyadicCanonical.toRat lower_raw =
        min (min (DyadicCanonical.toRat p1) (DyadicCanonical.toRat p2))
            (min (DyadicCanonical.toRat p3) (DyadicCanonical.toRat p4)) := by
      unfold lower_raw
      simp only [List.foldl]
      split_ifs <;> simp only [min_def] <;> split_ifs <;> linarith

    calc DyadicCanonical.toRat (RoundedDyadic.floor lower_raw p)
        ≤ DyadicCanonical.toRat lower_raw := RoundedDyadic.floor_le _ p
      _ = min (min (DyadicCanonical.toRat p1) (DyadicCanonical.toRat p2))
              (min (DyadicCanonical.toRat p3) (DyadicCanonical.toRat p4)) := hlower_eq
      _ = min (min (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.lower)
                   (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.upper))
              (min (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.lower)
                   (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.upper)) := by
          rw [hp1, hp2, hp3, hp4]
      _ ≤ a * b := product_ge_min_corner x y a b hx hy

  · -- Upper bound: a * b ≤ ceil(max(corners))
    have hupper_eq : DyadicCanonical.toRat upper_raw =
        max (max (DyadicCanonical.toRat p1) (DyadicCanonical.toRat p2))
            (max (DyadicCanonical.toRat p3) (DyadicCanonical.toRat p4)) := by
      unfold upper_raw
      simp only [List.foldl]
      split_ifs <;> simp only [max_def] <;> split_ifs <;> linarith

    calc a * b
        ≤ max (max (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.lower)
                   (DyadicCanonical.toRat x.lower * DyadicCanonical.toRat y.upper))
             (max (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.lower)
                  (DyadicCanonical.toRat x.upper * DyadicCanonical.toRat y.upper)) :=
          product_le_max_corner x y a b hx hy
      _ = max (max (DyadicCanonical.toRat p1) (DyadicCanonical.toRat p2))
              (max (DyadicCanonical.toRat p3) (DyadicCanonical.toRat p4)) := by
          rw [hp1, hp2, hp3, hp4]
      _ = DyadicCanonical.toRat upper_raw := hupper_eq.symm
      _ ≤ DyadicCanonical.toRat (RoundedDyadic.ceil upper_raw p) := RoundedDyadic.le_ceil _ p

/-- Scalar multiplication preserves interval containment -/
theorem scalar_mul_preserves_containment (c : ℚ) (x : IntervalD) (a : ℚ) (p : ℕ)
    (hx : intervalContains x a) :
    intervalContains (IntervalDyadic.mul (IntervalDyadic.fromRat c p) x p) (c * a) := by
  exact mul_preserves_containment (IntervalDyadic.fromRat c p) x c a p (fromRat_contains_rat c p) hx

/-- Negation preserves interval containment -/
theorem neg_preserves_containment (x : IntervalD) (a : ℚ) (p : ℕ)
    (hx : intervalContains x a) :
    intervalContains (IntervalDyadic.neg x p) (-a) := by
  unfold intervalContains IntervalDyadic.neg
  simp only []
  constructor
  · -- Lower bound: floor(-x.upper) ≤ -a
    have lower_calc : DyadicCanonical.toRat (RoundedDyadic.floor (DyadicCanonical.neg x.upper) p) ≤ -a := by
      calc DyadicCanonical.toRat (RoundedDyadic.floor (DyadicCanonical.neg x.upper) p)
          ≤ DyadicCanonical.toRat (DyadicCanonical.neg x.upper) := RoundedDyadic.floor_le _ p
        _ = -DyadicCanonical.toRat x.upper := DyadicCanonical.toRat_neg _
        _ ≤ -a := neg_le_neg hx.2
    exact lower_calc
  · -- Upper bound: -a ≤ ceil(-x.lower)
    have upper_calc : -a ≤ DyadicCanonical.toRat (RoundedDyadic.ceil (DyadicCanonical.neg x.lower) p) := by
      calc -a
          ≤ -DyadicCanonical.toRat x.lower := neg_le_neg hx.1
        _ = DyadicCanonical.toRat (DyadicCanonical.neg x.lower) := (DyadicCanonical.toRat_neg _).symm
        _ ≤ DyadicCanonical.toRat (RoundedDyadic.ceil (DyadicCanonical.neg x.lower) p) :=
            RoundedDyadic.le_ceil _ p
    exact upper_calc

/-- Subtraction preserves interval containment -/
theorem sub_preserves_containment (x y : IntervalD) (a b : ℚ) (p : ℕ)
    (hx : intervalContains x a) (hy : intervalContains y b) :
    intervalContains (IntervalDyadic.sub x y p) (a - b) := by
  unfold IntervalDyadic.sub
  have : a - b = a + (-b) := by ring
  rw [this]
  exact add_preserves_containment x (IntervalDyadic.neg y p) a (-b) p hx (neg_preserves_containment y b p hy)

/-! ## Complex Arithmetic Preservation -/

/-- Complex multiplication preserves witness for individual coefficients.
    If (iv_re1, iv_im1) witnesses (q_re1, q_im1) and (iv_re2, iv_im2) witnesses (q_re2, q_im2),
    then the complex product witnesses the mathematical complex product. -/
theorem complex_mul_preserves_witness (iv1 iv2 : IntervalD × IntervalD) (q1 q2 : ℚ × ℚ) (p : ℕ)
    (h1 : intervalContains iv1.1 q1.1 ∧ intervalContains iv1.2 q1.2)
    (h2 : intervalContains iv2.1 q2.1 ∧ intervalContains iv2.2 q2.2) :
    let iv_prod := (
      IntervalDyadic.sub (IntervalDyadic.mul iv1.1 iv2.1 p) (IntervalDyadic.mul iv1.2 iv2.2 p) p,
      IntervalDyadic.add (IntervalDyadic.mul iv1.1 iv2.2 p) (IntervalDyadic.mul iv1.2 iv2.1 p) p
    )
    let q_prod := (q1.1 * q2.1 - q1.2 * q2.2, q1.1 * q2.2 + q1.2 * q2.1)
    intervalContains iv_prod.1 q_prod.1 ∧ intervalContains iv_prod.2 q_prod.2 := by
  -- Real part: re1*re2 - im1*im2
  have h_re : intervalContains
      (IntervalDyadic.sub (IntervalDyadic.mul iv1.1 iv2.1 p) (IntervalDyadic.mul iv1.2 iv2.2 p) p)
      (q1.1 * q2.1 - q1.2 * q2.2) := by
    exact sub_preserves_containment
      (IntervalDyadic.mul iv1.1 iv2.1 p) (IntervalDyadic.mul iv1.2 iv2.2 p)
      (q1.1 * q2.1) (q1.2 * q2.2) p
      (mul_preserves_containment iv1.1 iv2.1 q1.1 q2.1 p h1.1 h2.1)
      (mul_preserves_containment iv1.2 iv2.2 q1.2 q2.2 p h1.2 h2.2)
  -- Imaginary part: re1*im2 + im1*re2
  have h_im : intervalContains
      (IntervalDyadic.add (IntervalDyadic.mul iv1.1 iv2.2 p) (IntervalDyadic.mul iv1.2 iv2.1 p) p)
      (q1.1 * q2.2 + q1.2 * q2.1) := by
    exact add_preserves_containment
      (IntervalDyadic.mul iv1.1 iv2.2 p) (IntervalDyadic.mul iv1.2 iv2.1 p)
      (q1.1 * q2.2) (q1.2 * q2.1) p
      (mul_preserves_containment iv1.1 iv2.2 q1.1 q2.2 p h1.1 h2.2)
      (mul_preserves_containment iv1.2 iv2.1 q1.2 q2.1 p h1.2 h2.1)
  exact ⟨h_re, h_im⟩

end Witness
