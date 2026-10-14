import Submission.DifferentialGeometry.Topology.Embedding.Sphere
import Submission.DifferentialGeometry.Topology.Embedding.SphericalCap

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Pointwise
open _root_.EuclideanGeometry (sphericalCap sphericalCapHeight sphericalCap_neg_one_image_closedBall)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem sphereChartEquiv_sphericalCap_neg_one {n : ℕ}
    [Fact (Module.finrank ℝ E = n + 1)]
    (v : Metric.sphere (0 : E) 1) (x : EuclideanSpace ℝ (Fin n)) :
    sphereChartEquiv v (sphericalCap (-1) x) = ((stereographic' n v).symm ((2 : ℝ) • x) : E) := by
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere v)).repr
  have hn : ‖(U.symm ((2 : ℝ) • x) : E)‖ = 2 * ‖x‖ := by
    simp [← Submodule.coe_norm, norm_smul]
  rw [sphereChartEquiv_apply, stereographic'_symm_apply]
  change (U.symm (sphericalCap (-1) x).1 : E) + (sphericalCap (-1) x).2 • (v : E) =
    (‖(U.symm ((2 : ℝ) • x) : E)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (U.symm ((2 : ℝ) • x) : E) +
      (‖(U.symm ((2 : ℝ) • x) : E)‖ ^ 2 + 4)⁻¹ •
        (‖(U.symm ((2 : ℝ) • x) : E)‖ ^ 2 - 4) • v.val
  rw [hn]
  simp only [sphericalCap, sphericalCapHeight, map_smul,
    Submodule.coe_smul_of_tower, smul_smul]
  match_scalars
  all_goals
    field_simp
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `sphereChartEquiv_sphericalCap_neg_one then
    throwError "Refusing to shadow existing declaration sphereChartEquiv_sphericalCap_neg_one"
  Lean.modifyEnv fun env => Lean.addAlias env `sphereChartEquiv_sphericalCap_neg_one ``Submission.sphereChartEquiv_sphericalCap_neg_one

theorem sphereChartEquiv_image_hemisphere {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
    (v : Metric.sphere (0 : E) 1) :
    sphereChartEquiv v ''
      {p : EuclideanSpace ℝ (Fin n) × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 = 1 ∧ p.2 ≤ 0} =
      Subtype.val '' ((stereographic' n v).symm '' Metric.closedBall 0 2) := by
  have hscale : (fun x : EuclideanSpace ℝ (Fin n) => (2 : ℝ) • x) '' Metric.closedBall 0 1 =
      Metric.closedBall 0 2 := by
    change (2 : ℝ) • Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 = _
    rw [_root_.smul_closedBall _ _ zero_le_one]
    norm_num
  rw [← sphericalCap_neg_one_image_closedBall, Set.image_image]
  calc
    _ = (fun x => ((stereographic' n v).symm ((2 : ℝ) • x) : E)) '' Metric.closedBall 0 1 :=
      Set.image_congr (fun x _ => sphereChartEquiv_sphericalCap_neg_one v x)
    _ = Subtype.val '' ((stereographic' n v).symm ''
        ((fun x => (2 : ℝ) • x) '' Metric.closedBall 0 1)) := by
      rw [Set.image_image, Set.image_image]
    _ = _ := by rw [hscale]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `sphereChartEquiv_image_hemisphere then
    throwError "Refusing to shadow existing declaration sphereChartEquiv_image_hemisphere"
  Lean.modifyEnv fun env => Lean.addAlias env `sphereChartEquiv_image_hemisphere ``Submission.sphereChartEquiv_image_hemisphere
