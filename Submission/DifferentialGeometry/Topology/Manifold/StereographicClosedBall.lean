import Submission.DifferentialGeometry.Topology.Manifold.StereographicAntipodal
import Submission.DifferentialGeometry.Topology.Embedding.Frontier

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Topology.Manifold

open _root_.Set _root_.Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

theorem stereographic_symm_zero (p : Metric.sphere (0 : E) 1) :
    (stereographic' n p).symm 0 = -p := by
  apply Subtype.ext
  change ((stereographic' n p).symm 0 : E) = -(p : E)
  norm_num [stereographic'_symm_apply, smul_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.stereographic_symm_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.stereographic_symm_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.stereographic_symm_zero ``Submission.DifferentialGeometry.Topology.Manifold.stereographic_symm_zero

theorem mem_antipodal_stereographic_symm_closedBall
    (p : Metric.sphere (0 : E) 1) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin n)) :
    -(stereographic' n p).symm x ∈ (stereographic' n p).symm '' _root_.Metric.closedBall 0 (4 / r) ↔
      r ≤ ‖x‖ := by
  let c := stereographic' n p
  have hinj : Function.Injective c.symm := (c.symm.isOpenEmbedding (by simp [c])).injective
  by_cases hx : x = 0
  · subst x
    rw [stereographic_symm_zero, neg_neg, norm_zero]
    have hp : p ∉ c.symm '' _root_.Metric.closedBall 0 (4 / r) := by
      rintro ⟨y, _, hy⟩
      have hs := c.map_target (show y ∈ c.target by simp [c])
      rw [hy] at hs
      simp [c] at hs
    exact iff_of_false hp (not_le.mpr hr)
  · rw [← stereographicInverse_antipodal p x hx]
    change c.symm ((-4 / ‖x‖ ^ 2) • x) ∈ c.symm '' _root_.Metric.closedBall 0 (4 / r) ↔ _
    rw [hinj.mem_set_image, mem_closedBall_zero_iff]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hnorm : ‖(-4 / ‖x‖ ^ 2) • x‖ = 4 / ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_neg (div_neg_of_neg_of_pos (by norm_num) (sq_pos_of_pos hxpos))]
      field_simp
    rw [hnorm, div_le_div_iff₀ hxpos hr]
    constructor <;> intro h <;> nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.mem_antipodal_stereographic_symm_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.mem_antipodal_stereographic_symm_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.mem_antipodal_stereographic_symm_closedBall ``Submission.DifferentialGeometry.Topology.Manifold.mem_antipodal_stereographic_symm_closedBall

theorem antipodal_image_stereographic_symm_closedBall
    (p : Metric.sphere (0 : E) 1) {r : ℝ} (hr : 0 < r) :
    Neg.neg '' ((stereographic' n p).symm '' _root_.Metric.closedBall 0 (4 / r)) =
      ((stereographic' n p).symm '' _root_.Metric.ball 0 r)ᶜ := by
  let c := stereographic' n p
  have hinj : Function.Injective c.symm := (c.symm.isOpenEmbedding (by simp [c])).injective
  ext y
  have hleft : y ∈ Neg.neg '' (c.symm '' _root_.Metric.closedBall 0 (4 / r)) ↔
      -y ∈ c.symm '' _root_.Metric.closedBall 0 (4 / r) := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [neg_neg] using hz
    · intro hy
      exact ⟨-y, hy, neg_neg y⟩
  rw [hleft]
  by_cases hy : y = p
  · subst y
    have hmem : -p ∈ c.symm '' _root_.Metric.closedBall 0 (4 / r) :=
      ⟨0, _root_.Metric.mem_closedBall_self (by positivity), stereographic_symm_zero p⟩
    have hnot : p ∉ c.symm '' _root_.Metric.ball 0 r := by
      rintro ⟨x, _, hx⟩
      have hs := c.map_target (show x ∈ c.target by simp [c])
      rw [hx] at hs
      simp [c] at hs
    exact iff_of_true hmem hnot
  · have hys : y ∈ c.source := by
      simpa only [c, stereographic'_source, _root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff] using hy
    have he : c.symm (c y) = y := c.left_inv hys
    rw [← he, mem_antipodal_stereographic_symm_closedBall p hr, _root_.Set.mem_compl_iff,
      hinj.mem_set_image, mem_ball_zero_iff, not_lt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.antipodal_image_stereographic_symm_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.antipodal_image_stereographic_symm_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.antipodal_image_stereographic_symm_closedBall ``Submission.DifferentialGeometry.Topology.Manifold.antipodal_image_stereographic_symm_closedBall

theorem interior_image_stereographic_symm_closedBall
    (p : Metric.sphere (0 : E) 1) {r : ℝ} (hr : r ≠ 0) :
    interior ((stereographic' n p).symm '' _root_.Metric.closedBall 0 r) =
      (stereographic' n p).symm '' _root_.Metric.ball 0 r := by
  rw [DifferentialGeometry.Topology.Embedding.interior_image_of_isOpenEmbedding
    ((stereographic' n p).symm.isOpenEmbedding (by simp)), interior_closedBall _ hr]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.interior_image_stereographic_symm_closedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.interior_image_stereographic_symm_closedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.interior_image_stereographic_symm_closedBall ``Submission.DifferentialGeometry.Topology.Manifold.interior_image_stereographic_symm_closedBall

end DifferentialGeometry.Topology.Manifold
