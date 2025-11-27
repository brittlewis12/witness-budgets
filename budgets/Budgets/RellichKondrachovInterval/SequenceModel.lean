import Budgets.RellichKondrachovInterval.Harmonics
import Budgets.RellichKondrachovD.Core
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Interval sequence model

We model Dirichlet sequences via the same coefficient machinery as the torus
QRK instance, embedding odd sine modes into the torus lattice.  This file
introduces the helper structure `IntervalSeq` and shows how to map it into
`SeqD 1` for reuse of the existing QRK proofs.
-/

namespace RellichKondrachovInterval

open scoped BigOperators ComplexConjugate

@[simp] lemma sq_neg (x : ℝ) : (-x)^2 = x^2 := by
  simp [pow_two]

lemma pi_sq_mul (x : ℝ) : (Real.pi * x)^2 = Real.pi^2 * x^2 := by
  simp [pow_two, mul_comm, mul_left_comm]

/-- Dirichlet sequence on the interval via sine coefficients. -/
structure IntervalSeq where
  coeffs : ℕ → ℝ
  support : Finset ℕ
  support_spec : ∀ k ∉ support, coeffs k = 0

namespace IntervalSeq

attribute [simp] Finset.mem_union Finset.mem_image

lemma sum_select {β} [AddCommMonoid β] [DecidableEq ℕ]
    (s : Finset ℕ) (n : ℕ) (f : ℕ → β) :
    (∑ m ∈ s, (if n = m then f m else 0)) =
        if n ∈ s then f n else 0 := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a t ha IH
    by_cases hna : n = a
    · subst hna
      simp [ha]
    · simp [hna]

/-- Evaluate the coefficient vector as a sine-series test function. -/
noncomputable def eval (u : IntervalSeq) : FiniteSine :=
  ⟨u.coeffs, u.support, u.support_spec⟩

section Embedding

open Complex

private def axis (z : ℤ) : ℓ2ZD.Lattice 1 := fun _ => z

@[simp] lemma axis_apply (z : ℤ) (i : Fin 1) : axis z i = z := by
  fin_cases i
  rfl


def freqInt (n : ℕ) : ℤ := (n.succ : ℕ)

lemma freqInt_succ (n : ℕ) : freqInt n = (n.succ : ℤ) := rfl

lemma freqInt_injective : Function.Injective freqInt := by
  intro m n h
  have hsucc : m.succ = n.succ := by
    exact Int.ofNat.inj h
  exact Nat.succ.inj hsucc

lemma freqInt_pos (n : ℕ) : 0 < freqInt n := by
  have : 0 < (n.succ : ℕ) := Nat.succ_pos _
  simp [freqInt]

lemma freqInt_ne_neg (m n : ℕ) : freqInt m ≠ -freqInt n := by
  have hneg : -freqInt n < 0 := by
    simpa using (neg_lt_zero.mpr (freqInt_pos n))
  have hpos : 0 < freqInt m := freqInt_pos m
  have : -freqInt n < freqInt m := lt_trans hneg hpos
  exact ne_of_gt this

lemma freqInt_ne_neg_self (n : ℕ) : freqInt n ≠ -freqInt n :=
  freqInt_ne_neg _ _

lemma negfreq_ne_freq (m n : ℕ) : -freqInt n ≠ freqInt m := by
  have hneg : -freqInt n < 0 := by
    simpa using (neg_lt_zero.mpr (freqInt_pos n))
  have hpos : 0 ≤ freqInt m := le_of_lt (freqInt_pos m)
  have : -freqInt n < freqInt m := lt_of_lt_of_le hneg hpos
  exact ne_of_lt this

@[simp] lemma freqInt_eq_iff {m n : ℕ} :
    freqInt m = freqInt n ↔ m = n := by
  constructor
  · intro h; exact freqInt_injective h
  · intro h; cases h; rfl

@[simp] lemma freqInt_eq_neg_iff {m n : ℕ} :
    freqInt m = -freqInt n ↔ False := by
  constructor
  · intro h; exact (freqInt_ne_neg m n) h
  · intro h; exact h.elim

@[simp] lemma negfreq_eq_freqInt_iff {m n : ℕ} :
    -freqInt m = freqInt n ↔ False := by
  constructor
  · intro h
    have : freqInt m = -freqInt n := by
      simpa using congrArg Neg.neg h
    exact (freqInt_ne_neg m n) this
  · intro h; exact h.elim

@[simp] lemma negfreq_eq_negfreq_iff {m n : ℕ} :
    -freqInt m = -freqInt n ↔ m = n := by
  constructor
  · intro h
    have := congrArg Neg.neg h
    have : freqInt m = freqInt n := by simpa using this
    exact freqInt_injective this
  · intro h; cases h; rfl

lemma eq_axis_iff {k : ℓ2ZD.Lattice 1} {z : ℤ} :
    k = axis z ↔ k 0 = z := by
  constructor
  · intro h; simpa [axis] using congrArg (fun f => f 0) h
  · intro h; ext i; fin_cases i; simpa [axis] using h

lemma axis_freq_injective :
    Function.Injective (fun n : ℕ => axis (freqInt n)) := by
  intro m n h
  have h0 := congrArg (fun f => f 0) h
  have : freqInt m = freqInt n := by simpa [axis] using h0
  exact freqInt_injective this

lemma axis_negfreq_injective :
    Function.Injective (fun n : ℕ => axis (-freqInt n)) := by
  intro m n h
  have h0 := congrArg (fun f => f 0) h
  have : -freqInt m = -freqInt n := by simpa [axis] using h0
  have := congrArg Neg.neg this
  simpa using freqInt_injective (by simpa using this)

noncomputable def torusFactor : ℂ :=
  -Complex.I * ((Real.sqrt 2) / 2 : ℂ)

def posSupport (u : IntervalSeq) : Finset (ℓ2ZD.Lattice 1) :=
  u.support.image (fun k => axis (freqInt k))

def negSupport (u : IntervalSeq) : Finset (ℓ2ZD.Lattice 1) :=
  u.support.image (fun k => axis (-freqInt k))

def torusSupport (u : IntervalSeq) : Finset (ℓ2ZD.Lattice 1) :=
  posSupport u ∪ negSupport u

lemma axis_mem_pos {u : IntervalSeq} {n : ℕ} (hn : n ∈ u.support) :
    axis (freqInt n) ∈ posSupport u := by
  classical
  refine Finset.mem_image.mpr ?_
  exact ⟨n, hn, rfl⟩

lemma axis_mem_neg {u : IntervalSeq} {n : ℕ} (hn : n ∈ u.support) :
    axis (-freqInt n) ∈ negSupport u := by
  classical
  refine Finset.mem_image.mpr ?_
  exact ⟨n, hn, rfl⟩

lemma k0_ne_freq_of_not_mem_pos {u : IntervalSeq} {k : ℓ2ZD.Lattice 1}
    (hk : k ∉ posSupport u) :
    ∀ n ∈ u.support, k 0 ≠ freqInt n := by
  classical
  intro n hn hfreq
  have hk_axis : k = axis (freqInt n) :=
    (eq_axis_iff).2 hfreq
  have : k ∈ posSupport u := by
    simpa [hk_axis] using axis_mem_pos (u := u) (n := n) hn
  exact hk this

lemma k0_ne_negfreq_of_not_mem_neg {u : IntervalSeq} {k : ℓ2ZD.Lattice 1}
    (hk : k ∉ negSupport u) :
    ∀ n ∈ u.support, k 0 ≠ -freqInt n := by
  classical
  intro n hn hfreq
  have hk_axis : k = axis (-freqInt n) :=
    (eq_axis_iff).2 hfreq
  have : k ∈ negSupport u := by
    simpa [hk_axis] using axis_mem_neg (u := u) (n := n) hn
  exact hk this

/-- Coefficient embedding into the torus lattice. -/
noncomputable def toSeqD (u : IntervalSeq) : ℓ2ZD.SeqD 1 :=
  { a := fun k =>
      Finset.sum u.support (fun n =>
        let freq := freqInt n
        let coeff : ℂ := (u.coeffs n : ℂ)
        (if k 0 = freq then torusFactor * coeff else 0) +
          (if k 0 = -freq then -torusFactor * coeff else 0))
    summable_sq := by
      classical
      refine summable_of_ne_finset_zero (s := torusSupport u) ?_
      intro k hk
      have hk_pos : k ∉ posSupport u := by
        intro hkpos
        exact hk (by
          simpa [torusSupport] using Finset.mem_union.mpr (Or.inl hkpos))
      have hk_neg : k ∉ negSupport u := by
        intro hkneg
        exact hk (by
          simpa [torusSupport] using Finset.mem_union.mpr (Or.inr hkneg))
      have hpos :
          ∀ n ∈ u.support, k 0 ≠ freqInt n :=
        k0_ne_freq_of_not_mem_pos (u := u) hk_pos
      have hneg :
          ∀ n ∈ u.support, k 0 ≠ -freqInt n :=
        k0_ne_negfreq_of_not_mem_neg (u := u) hk_neg
      have hsum :
          Finset.sum u.support
              (fun n =>
                (if k 0 = freqInt n then torusFactor * (u.coeffs n : ℂ) else 0) +
                  (if k 0 = -freqInt n then -torusFactor * (u.coeffs n : ℂ) else 0))
            = 0 := by
        classical
        refine Finset.sum_eq_zero ?_
        intro n hn
        have hpos' := hpos n hn
        have hneg' := hneg n hn
        classical
        by_cases hkfreq : k 0 = freqInt n
        · exact (hpos' hkfreq).elim
        · by_cases hkneg : k 0 = -freqInt n
          · exact (hneg' hkneg).elim
          ·
            simp [hkfreq, hkneg]
      simpa using hsum }

lemma value_on_pos (u : IntervalSeq) (n : ℕ) :
    (toSeqD u).a (axis (freqInt n))
      = torusFactor * (u.coeffs n : ℂ) := by
  classical
  have hx :
      (toSeqD u).a (axis (freqInt n))
        =
          if n ∈ u.support then torusFactor * (u.coeffs n : ℂ) else 0 := by
    have hsum :
        ∑ m ∈ u.support,
            (if n = m then torusFactor * (u.coeffs m : ℂ) else (0 : ℂ))
          = if n ∈ u.support then torusFactor * (u.coeffs n : ℂ) else 0 :=
      sum_select _ _ _
    simp [toSeqD, axis_apply, Finset.sum_add_distrib, freqInt_eq_iff,
      freqInt_eq_neg_iff, hsum]
  by_cases hn : n ∈ u.support
  · simp [hx, hn]
  ·
    have hcoeff : u.coeffs n = 0 := u.support_spec n hn
    simp [hx, hn, hcoeff]

lemma value_on_neg (u : IntervalSeq) (n : ℕ) :
    (toSeqD u).a (axis (-freqInt n))
      = -torusFactor * (u.coeffs n : ℂ) := by
  classical
  have hx :
      (toSeqD u).a (axis (-freqInt n))
        =
          if n ∈ u.support then -torusFactor * (u.coeffs n : ℂ) else 0 := by
    have hsum :
        ∑ m ∈ u.support,
            (if n = m then -torusFactor * (u.coeffs m : ℂ) else (0 : ℂ))
          = if n ∈ u.support then -torusFactor * (u.coeffs n : ℂ) else 0 :=
      sum_select _ _ _
    simp [toSeqD, axis_apply, Finset.sum_add_distrib, negfreq_eq_freqInt_iff]
  by_cases hn : n ∈ u.support
  · simp [hx, hn]
  ·
    have hcoeff : u.coeffs n = 0 := u.support_spec n hn
    simp [hx, hn, hcoeff]

lemma torusFactor_norm_sq : ‖torusFactor‖^2 = (1 / 2 : ℝ) := by
  have hnonneg : 0 ≤ (Real.sqrt 2 / 2 : ℝ) := by
    have : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have : 0 ≤ (Real.sqrt 2 : ℝ) / 2 :=
      div_nonneg this (by norm_num : (0 : ℝ) ≤ 2)
    simpa using this
  have hnorm :
      ‖torusFactor‖ = Real.sqrt 2 / 2 := by
    have hreal :
        ‖((Real.sqrt 2) / 2 : ℂ)‖ = Real.sqrt 2 / 2 := by simp
    have hI : ‖-Complex.I‖ = 1 := by simp
    have := norm_mul (-Complex.I) ((Real.sqrt 2) / 2 : ℂ)
    simp [torusFactor]
  have hsqrt : (Real.sqrt 2)^2 = 2 := by simp
  have hsq :
      (Real.sqrt 2 / 2 : ℝ)^2 = (1 / 2 : ℝ) := by
    calc
      (Real.sqrt 2 / 2 : ℝ)^2
          = (Real.sqrt 2)^2 / 4 := by
              field_simp [pow_two]; ring
      _ = (2 : ℝ) / 4 := by simp [hsqrt]
      _ = (1 / 2 : ℝ) := by norm_num
  have hnormsq :
      ‖torusFactor‖^2 = (Real.sqrt 2 / 2 : ℝ)^2 := by
    simpa using congrArg (fun t : ℝ => t ^ 2) hnorm
  exact hnormsq.trans hsq

lemma norm_sq_of_real (x : ℝ) : ‖(x : ℂ)‖^2 = x^2 := by
  have : ‖(x : ℂ)‖ = |x| := by simp
  have habs : |x|^2 = x^2 := by simp [pow_two]
  simp [pow_two]

lemma norm_sq_on_pos (u : IntervalSeq) (n : ℕ) :
    ‖(toSeqD u).a (axis (freqInt n))‖^2
      = (1 / 2 : ℝ) * (u.coeffs n)^2 := by
  have hv := value_on_pos (u := u) (n := n)
  have hmul :
      ‖torusFactor * (u.coeffs n : ℂ)‖^2
        = ‖torusFactor‖^2 * ‖(u.coeffs n : ℂ)‖^2 := by
    have := congrArg (fun t : ℝ => t^2) (norm_mul torusFactor (u.coeffs n : ℂ))
    simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  have hcoeff : ‖(u.coeffs n : ℂ)‖^2 = (u.coeffs n)^2 :=
    norm_sq_of_real (u.coeffs n)
  calc
    ‖(toSeqD u).a (axis (freqInt n))‖^2
        = ‖torusFactor * (u.coeffs n : ℂ)‖^2 := by simp [hv]
    _ = ‖torusFactor‖^2 * ‖(u.coeffs n : ℂ)‖^2 := by simpa using hmul
    _ = (1 / 2 : ℝ) * (u.coeffs n)^2 := by
          simp [torusFactor_norm_sq]

lemma norm_sq_on_neg (u : IntervalSeq) (n : ℕ) :
    ‖(toSeqD u).a (axis (-freqInt n))‖^2
      = (1 / 2 : ℝ) * (u.coeffs n)^2 := by
  have hv := value_on_neg (u := u) (n := n)
  have hmul :
      ‖torusFactor * (u.coeffs n : ℂ)‖^2
        = ‖torusFactor‖^2 * ‖(u.coeffs n : ℂ)‖^2 := by
    have := congrArg (fun t : ℝ => t^2) (norm_mul torusFactor (u.coeffs n : ℂ))
    simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  have hcoeff : ‖(u.coeffs n : ℂ)‖^2 = (u.coeffs n)^2 :=
    norm_sq_of_real (u.coeffs n)
  calc
    ‖(toSeqD u).a (axis (-freqInt n))‖^2
        = ‖torusFactor * (u.coeffs n : ℂ)‖^2 := by
              simp [hv]
    _ = ‖torusFactor‖^2 * ‖(u.coeffs n : ℂ)‖^2 := by simpa using hmul
    _ = (1 / 2 : ℝ) * (u.coeffs n)^2 := by
          simp [torusFactor_norm_sq]


lemma sum_pos_image (u : IntervalSeq)
    (f : ℓ2ZD.Lattice 1 → ℝ) :
    Finset.sum (posSupport u) f =
      Finset.sum u.support (fun n => f (axis (freqInt n))) := by
  classical
  have hinj :
      ∀ a ∈ u.support, ∀ b ∈ u.support,
          axis (freqInt a) = axis (freqInt b) → a = b := by
    intro a ha b hb h
    exact axis_freq_injective h
  simpa [posSupport] using Finset.sum_image hinj

lemma sum_neg_image (u : IntervalSeq)
    (f : ℓ2ZD.Lattice 1 → ℝ) :
    Finset.sum (negSupport u) f =
      Finset.sum u.support (fun n => f (axis (-freqInt n))) := by
  classical
  have hinj :
      ∀ a ∈ u.support, ∀ b ∈ u.support,
          axis (-freqInt a) = axis (-freqInt b) → a = b := by
    intro a ha b hb h
    exact axis_negfreq_injective h
  simpa [negSupport] using Finset.sum_image hinj

lemma h1Weight_axis (n : ℕ) :
    ℓ2ZD.h1Weight (axis (freqInt n))
      = 1 + 4 * Real.pi^2 * ((n.succ : ℝ)^2) := by
  classical
  have : (axis (freqInt n) 0 : ℝ) = (n.succ : ℝ) := by simp [axis, freqInt]
  simp [ℓ2ZD.h1Weight, ℓ2ZD.normSq, axis, freqInt, pow_two]

lemma h1Weight_axis_neg (n : ℕ) :
    ℓ2ZD.h1Weight (axis (-freqInt n)) =
      ℓ2ZD.h1Weight (axis (freqInt n)) := by
  classical
  have hneg : (axis (-freqInt n) 0 : ℝ) = -(n.succ : ℝ) := by
    simp [axis, freqInt]
  have hpos : (axis (freqInt n) 0 : ℝ) = (n.succ : ℝ) := by
    simp [axis, freqInt]
  have hsq : (-(n.succ : ℝ))^2 = (n.succ : ℝ)^2 := by
    simpa using (sq_neg (n.succ : ℝ))
  simp [ℓ2ZD.h1Weight, ℓ2ZD.normSq, pow_two]

lemma sum_pos_sq (u : IntervalSeq) :
    Finset.sum (posSupport u)
        (fun k => ‖(toSeqD u).a k‖^2)
      = (1 / 2 : ℝ) * FiniteSine.l2IntervalSq (u.eval) := by
  classical
  have himage := sum_pos_image (u := u)
      (f := fun k => ‖(toSeqD u).a k‖^2)
  have hx :
      Finset.sum u.support
          (fun n => ‖(toSeqD u).a (axis (freqInt n))‖^2)
        = (1 / 2 : ℝ) *
            Finset.sum u.support (fun n => (u.coeffs n)^2) := by
    simp [norm_sq_on_pos, Finset.mul_sum]
  simpa [IntervalSeq.eval, FiniteSine.l2IntervalSq] using himage.trans hx

lemma sum_neg_sq (u : IntervalSeq) :
    Finset.sum (negSupport u)
        (fun k => ‖(toSeqD u).a k‖^2)
      = (1 / 2 : ℝ) * FiniteSine.l2IntervalSq (u.eval) := by
  classical
  have himage := sum_neg_image (u := u)
      (f := fun k => ‖(toSeqD u).a k‖^2)
  have hx :
      Finset.sum u.support
          (fun n => ‖(toSeqD u).a (axis (-freqInt n))‖^2)
        = (1 / 2 : ℝ) *
            Finset.sum u.support (fun n => (u.coeffs n)^2) := by
    simp [norm_sq_on_neg, Finset.mul_sum]
  simpa [IntervalSeq.eval, FiniteSine.l2IntervalSq] using himage.trans hx

lemma pos_neg_disjoint (u : IntervalSeq) :
    Disjoint (posSupport u) (negSupport u) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro k hkpos hkneg
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hkpos
  obtain ⟨m, hm, hkm⟩ := Finset.mem_image.mp hkneg
  have hk0 := congrArg (fun f => f 0) hkm
  have : freqInt n = -freqInt m := by simp [axis] at hk0
  exact (freqInt_ne_neg n m) this

lemma sum_torus_sq (u : IntervalSeq) :
    Finset.sum (torusSupport u)
        (fun k => ‖(toSeqD u).a k‖^2)
      = FiniteSine.l2IntervalSq (u.eval) := by
  classical
  have hdisj := pos_neg_disjoint (u := u)
  have hsplit :
      Finset.sum (torusSupport u)
          (fun k => ‖(toSeqD u).a k‖^2)
        = Finset.sum (posSupport u)
            (fun k => ‖(toSeqD u).a k‖^2) +
            Finset.sum (negSupport u)
            (fun k => ‖(toSeqD u).a k‖^2) := by
    simpa [torusSupport] using
      Finset.sum_union hdisj (f := fun k => ‖(toSeqD u).a k‖^2)
  have hL :
      FiniteSine.l2IntervalSq (u.eval)
        = FiniteSine.l2IntervalSq (u.eval) := rfl
  have hcalc :
      FiniteSine.l2IntervalSq (u.eval)
        = (1 / 2 : ℝ) * FiniteSine.l2IntervalSq (u.eval)
            + (1 / 2 : ℝ) * FiniteSine.l2IntervalSq (u.eval) := by
    ring
  have hpos := sum_pos_sq (u := u)
  have hneg := sum_neg_sq (u := u)
  have hsums :
      Finset.sum (torusSupport u)
          (fun k => ‖(toSeqD u).a k‖^2)
        = (1 / 2 : ℝ) * FiniteSine.l2IntervalSq (u.eval)
            + (1 / 2 : ℝ) * FiniteSine.l2IntervalSq (u.eval) := by
    simpa [hpos, hneg] using hsplit
  have hsum :
      (1 / 2 : ℝ) * FiniteSine.l2IntervalSq (u.eval)
        + (1 / 2 : ℝ) * FiniteSine.l2IntervalSq (u.eval)
        = FiniteSine.l2IntervalSq (u.eval) := by
    simpa using hcalc.symm
  exact hsums.trans hsum

lemma sum_pos_h1 (u : IntervalSeq) :
    Finset.sum (posSupport u)
        (fun k => ℓ2ZD.h1Weight k * ‖(toSeqD u).a k‖^2)
      = (1 / 2 : ℝ) *
          Finset.sum u.support
            (fun n =>
              (1 + 4 * Real.pi^2 * ((n.succ : ℝ)^2)) * (u.coeffs n)^2) := by
  classical
  have himage := sum_pos_image (u := u)
      (f := fun k => ℓ2ZD.h1Weight k * ‖(toSeqD u).a k‖^2)
  have hx :
      Finset.sum u.support
          (fun n =>
            ℓ2ZD.h1Weight (axis (freqInt n)) *
              ‖(toSeqD u).a (axis (freqInt n))‖^2)
        = (1 / 2 : ℝ) *
            Finset.sum u.support
              (fun n =>
                (1 + 4 * Real.pi^2 * ((n.succ : ℝ)^2)) * (u.coeffs n)^2) := by
    simp [h1Weight_axis, norm_sq_on_pos, Finset.mul_sum, mul_comm, mul_left_comm,
      mul_assoc, add_mul]
  simpa using himage.trans hx

lemma sum_neg_h1 (u : IntervalSeq) :
    Finset.sum (negSupport u)
        (fun k => ℓ2ZD.h1Weight k * ‖(toSeqD u).a k‖^2)
      = (1 / 2 : ℝ) *
          Finset.sum u.support
            (fun n =>
              (1 + 4 * Real.pi^2 * ((n.succ : ℝ)^2)) * (u.coeffs n)^2) := by
  classical
  have himage := sum_neg_image (u := u)
      (f := fun k => ℓ2ZD.h1Weight k * ‖(toSeqD u).a k‖^2)
  have hx :
      Finset.sum u.support
          (fun n =>
            ℓ2ZD.h1Weight (axis (-freqInt n)) *
              ‖(toSeqD u).a (axis (-freqInt n))‖^2)
        = (1 / 2 : ℝ) *
            Finset.sum u.support
              (fun n =>
                (1 + 4 * Real.pi^2 * ((n.succ : ℝ)^2)) * (u.coeffs n)^2) := by
    simp [h1Weight_axis_neg, h1Weight_axis, norm_sq_on_neg, Finset.mul_sum,
      mul_comm, mul_left_comm, mul_assoc, add_mul]
  simpa using himage.trans hx

lemma sum_torus_h1 (u : IntervalSeq) :
    Finset.sum (torusSupport u)
        (fun k => ℓ2ZD.h1Weight k * ‖(toSeqD u).a k‖^2)
      = FiniteSine.l2IntervalSq (u.eval)
          + 4 * FiniteSine.h1IntervalSq (u.eval) := by
  classical
  have hdisj := pos_neg_disjoint (u := u)
  have hsplit :
      Finset.sum (torusSupport u)
          (fun k => ℓ2ZD.h1Weight k * ‖(toSeqD u).a k‖^2)
        = Finset.sum (posSupport u)
            (fun k => ℓ2ZD.h1Weight k * ‖(toSeqD u).a k‖^2) +
          Finset.sum (negSupport u)
            (fun k => ℓ2ZD.h1Weight k * ‖(toSeqD u).a k‖^2) := by
    simpa [torusSupport] using
      Finset.sum_union hdisj
        (f := fun k => ℓ2ZD.h1Weight k * ‖(toSeqD u).a k‖^2)
  set S :=
    Finset.sum u.support
      (fun n =>
        (1 + 4 * Real.pi^2 * ((n.succ : ℝ)^2)) * (u.coeffs n)^2)
  have hpos := sum_pos_h1 (u := u)
  have hneg := sum_neg_h1 (u := u)
  have hpos' :
      Finset.sum (posSupport u)
          (fun k => ℓ2ZD.h1Weight k * ‖(toSeqD u).a k‖^2)
        = (1 / 2 : ℝ) * S := by
    simpa [S] using hpos
  have hneg' :
      Finset.sum (negSupport u)
          (fun k => ℓ2ZD.h1Weight k * ‖(toSeqD u).a k‖^2)
        = (1 / 2 : ℝ) * S := by
    simpa [S] using hneg
  have hsums :
      Finset.sum (torusSupport u)
          (fun k => ℓ2ZD.h1Weight k * ‖(toSeqD u).a k‖^2)
        = (1 / 2 : ℝ) * S + (1 / 2 : ℝ) * S := by
    simpa [hpos', hneg'] using hsplit
  have hSsplit :
      S = FiniteSine.l2IntervalSq (u.eval)
          + Finset.sum u.support
              (fun n =>
                (4 * Real.pi^2 * ((n.succ : ℝ)^2)) * (u.coeffs n)^2) := by
    simp [S, IntervalSeq.eval, FiniteSine.l2IntervalSq, Finset.sum_add_distrib,
      add_mul, mul_comm, mul_left_comm, mul_assoc]
  have hHsum :
      4 * FiniteSine.h1IntervalSq (u.eval)
        = Finset.sum u.support
            (fun n =>
              (4 * Real.pi^2 * ((n.succ : ℝ)^2)) * (u.coeffs n)^2) := by
    simp [IntervalSeq.eval, FiniteSine.h1IntervalSq, Finset.mul_sum, pi_sq_mul,
      mul_comm, mul_left_comm, mul_assoc]
  have hH := hHsum.symm
  have hS :
      S = FiniteSine.l2IntervalSq (u.eval)
          + 4 * FiniteSine.h1IntervalSq (u.eval) := by
    have hadd :=
      congrArg (fun t => FiniteSine.l2IntervalSq (u.eval) + t) hH
    exact hSsplit.trans hadd
  have hcombined' : (1 / 2 : ℝ) * S + (1 / 2 : ℝ) * S = S := by
    ring
  have hcombined :
      (1 / 2 : ℝ) * S + (1 / 2 : ℝ) * S
        = FiniteSine.l2IntervalSq (u.eval)
            + 4 * FiniteSine.h1IntervalSq (u.eval) := by
    simpa [hS] using hcombined'
  exact hsums.trans hcombined


end Embedding

end IntervalSeq

end RellichKondrachovInterval
