import Budgets.AubinLions.Core

/-!
# Quantitative Aubin–Lions: time-grid utilities

This file packages elementary lemmas about the uniform time grid introduced in
`Core`.  They will later underpin the quantitative time-modulus estimate (the
H⁻¹ equicontinuity bound and its translation to L² after truncation).

The statements are intentionally simple for now:
* re-expressing the `node` inequality in ℝ,
* monotonicity of the node map,
* a helper for comparing successive time slots.
-/

namespace AubinLions

open TimeGrid

lemma node_le_horizon_real (tg : TimeGrid) (i : Fin tg.segments) :
    ((tg.node i : ℚ) : ℝ) ≤ (tg.horizon : ℝ) := by
  have := TimeGrid.node_le_horizon tg i
  exact_mod_cast this

lemma node_strict_mono {tg : TimeGrid} {i j : Fin tg.segments}
    (hij : i < j) : tg.node i < tg.node j := by
  have hij' : (i : ℚ) < (j : ℚ) := by exact_mod_cast hij
  have hmesh_pos : 0 < mesh tg := TimeGrid.mesh_pos_rat tg
  have : tg.node i < tg.node j :=
    mul_lt_mul_of_pos_right hij' hmesh_pos
  simpa [TimeGrid.node] using this

lemma slot_length_coe (tg : TimeGrid) :
    ((mesh tg : ℚ) : ℝ) = (tg.horizon : ℝ) / (tg.segments : ℝ) := by
  simp [TimeGrid.mesh]

end AubinLions
