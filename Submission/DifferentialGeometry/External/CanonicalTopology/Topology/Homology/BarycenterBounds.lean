import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineSubdivision

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

/-! # The actual barycenter diameter estimate used by subdivision -/

noncomputable section

open _root_.Set

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Difference from the actual barycenter is the average of the original
differences, including degenerate and zero-dimensional simplices. -/
theorem affineSimplexBarycenter_sub (n : ℕ) (v : Fin (n + 1) → E) (x : E) :
    affineSimplexBarycenter n v - x = ((n + 1 : ℝ)⁻¹) • ∑ i, (v i - x) := by
  have hs : (∑ _i : Fin (n + 1), x) = (n + 1 : ℝ) • x := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.cast_smul_eq_nsmul ℝ (n + 1) x).symm
  change (∑ i : Fin (n + 1), (Fintype.card (Fin (n + 1)) : ℝ)⁻¹ • v i) - x = _
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  rw [← Finset.smul_sum, Finset.sum_sub_distrib, hs, smul_sub, smul_smul,
    inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSimplexBarycenter_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSimplexBarycenter_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSimplexBarycenter_sub ``Submission.DifferentialGeometry.Topology.affineSimplexBarycenter_sub

omit [NormedSpace ℝ E] in
/-- The sum of distances from one original vertex is bounded by n times
the original vertex diameter, since its own summand is exactly zero. -/
theorem affineSimplex_vertex_distance_sum (n : ℕ) (v : Fin (n + 1) → E) (j : Fin (n + 1)) :
    (∑ i, ‖v i - v j‖) ≤ (n : ℝ) * Metric.diam (_root_.Set.range v) := by
  rw [Fin.sum_univ_succAbove _ j]
  simp only [sub_self, norm_zero, zero_add]
  calc
    (∑ i : Fin n, ‖v (j.succAbove i) - v j‖) ≤ ∑ _i : Fin n, Metric.diam (_root_.Set.range v) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem (_root_.Set.finite_range v).isBounded ⟨j.succAbove i, rfl⟩ ⟨j, rfl⟩
    _ = (n : ℝ) * Metric.diam (_root_.Set.range v) := by simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSimplex_vertex_distance_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSimplex_vertex_distance_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSimplex_vertex_distance_sum ``Submission.DifferentialGeometry.Topology.affineSimplex_vertex_distance_sum

/-- The barycenter is at most n/(n+1) times the original diameter from
each original vertex. -/
theorem affineSimplexBarycenter_dist_vertex (n : ℕ) (v : Fin (n + 1) → E) (j : Fin (n + 1)) :
    _root_.Dist.dist (affineSimplexBarycenter n v) (v j) ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (_root_.Set.range v) := by
  rw [dist_eq_norm, affineSimplexBarycenter_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)⁻¹)]
  calc
    (n + 1 : ℝ)⁻¹ * ‖∑ i, (v i - v j)‖ ≤
        (n + 1 : ℝ)⁻¹ * ((n : ℝ) * Metric.diam (_root_.Set.range v)) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (affineSimplex_vertex_distance_sum n v j))
        (by positivity)
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSimplexBarycenter_dist_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSimplexBarycenter_dist_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSimplexBarycenter_dist_vertex ``Submission.DifferentialGeometry.Topology.affineSimplexBarycenter_dist_vertex

/-- The same sharp bound holds throughout the entire original convex hull. -/
theorem affineSimplexBarycenter_dist_convexHull (n : ℕ) (v : Fin (n + 1) → E)
    {x : E} (hx : x ∈ convexHull ℝ (_root_.Set.range v)) :
    _root_.Dist.dist (affineSimplexBarycenter n v) x ≤
      ((n : ℝ) / (n + 1)) * Metric.diam (_root_.Set.range v) := by
  obtain ⟨y, ⟨j, rfl⟩, hj⟩ := convexHull_exists_dist_ge hx (affineSimplexBarycenter n v)
  rw [dist_comm x, dist_comm (v j)] at hj
  exact hj.trans (affineSimplexBarycenter_dist_vertex n v j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.affineSimplexBarycenter_dist_convexHull then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.affineSimplexBarycenter_dist_convexHull"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.affineSimplexBarycenter_dist_convexHull ``Submission.DifferentialGeometry.Topology.affineSimplexBarycenter_dist_convexHull

end DifferentialGeometry.Topology
