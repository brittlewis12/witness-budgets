import Budgets.RellichKondrachovInterval.Harmonics
import Budgets.RellichKondrachovInterval.SequenceModel

/-
# Bridging sine series with the torus sequence model

`FiniteSine` already stores finitely-supported coefficient lists.  This file
provides the small adapter that turns such data into the `IntervalSeq`
structure used by `SequenceModel` and, ultimately, into a `SeqD 1`
element on the torus lattice.  No new analysis happens here; we simply
package the existing definitions so that the downstream QRK pipeline can
reuse lemmas uniformly.
-/

namespace RellichKondrachovInterval

open IntervalSeq

namespace FiniteSine

/-- View a finite sine series as an `IntervalSeq`. -/
@[simp] def toIntervalSeq (f : FiniteSine) : IntervalSeq :=
  ⟨f.coeffs, f.support, f.support_spec⟩

/-- The torus sequence obtained from a finite sine series. -/
noncomputable def toSeqD (f : FiniteSine) : ℓ2ZD.SeqD 1 :=
  IntervalSeq.toSeqD (toIntervalSeq f)

@[simp] lemma toSeqD_apply (f : FiniteSine) (k : ℓ2ZD.Lattice 1) :
    (toSeqD f).a k =
      Finset.sum f.support (fun n =>
        let freq := freqInt n
        let coeff : ℂ := (f.coeffs n : ℂ)
        (if k 0 = freq then torusFactor * coeff else 0) +
          (if k 0 = -freq then -torusFactor * coeff else 0)) := rfl

end FiniteSine

end RellichKondrachovInterval
