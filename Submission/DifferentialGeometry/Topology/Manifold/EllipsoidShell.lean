import Submission.DifferentialGeometry.Topology.Manifold.EllipsoidRadialGraph
import Submission.DifferentialGeometry.Topology.Manifold.RadialShell

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Metric _root_.Manifold _root_.Module
open scoped _root_.ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem closedBall_diff_openEllipsoid_eq_radialShell
    (A : E ≃L[ℝ] E) (p : E) {r R : ℝ} (hr : 0 < r) (hp : ‖p‖ < R)
    (v : _root_.Metric.sphere (0 : E) 1) :
    _root_.Metric.closedBall 0 R \ (fun x ↦ A x + p) '' _root_.Metric.ball 0 r =
      radialShell p (ellipsoidRadialFunction A r)
        (fun u ↦ DifferentialGeometry.Analysis.ballRadialFunction p R (u : E)) v := by
  ext x
  let u := sphereDirection v (x - p)
  have hu : ‖(u : E)‖ = 1 := norm_eq_of_mem_sphere u
  have houter := DifferentialGeometry.Analysis.smul_add_mem_closedBall_iff hp hu (norm_nonneg (x - p))
  have hinner := smul_add_mem_openEllipsoid_iff A p r u (norm_nonneg (x - p))
  constructor
  · rintro ⟨hxB, hxA⟩
    have hxp : x ≠ p := by
      intro h
      apply hxA
      refine ⟨0, _root_.Metric.mem_ball_self hr, ?_⟩
      simpa only [map_zero, zero_add] using h.symm
    have hrec : ‖x - p‖ • (u : E) + p = x := by
      rw [norm_smul_sphereDirection v (sub_ne_zero.mpr hxp), sub_add_cancel]
    refine ⟨hxp, ?_, ?_⟩
    · exact le_of_not_gt (fun h ↦ hxA (hrec ▸ hinner.mpr h))
    · exact houter.mp (hrec.symm ▸ hxB)
  · intro hx
    have hrec : ‖x - p‖ • (u : E) + p = x := by
      rw [norm_smul_sphereDirection v (sub_ne_zero.mpr hx.1), sub_add_cancel]
    refine ⟨hrec ▸ houter.mpr hx.2.2, ?_⟩
    intro hxA
    exact (hinner.mp (hrec.symm ▸ hxA)).not_ge hx.2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.closedBall_diff_openEllipsoid_eq_radialShell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.closedBall_diff_openEllipsoid_eq_radialShell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.closedBall_diff_openEllipsoid_eq_radialShell ``Submission.DifferentialGeometry.Topology.Manifold.closedBall_diff_openEllipsoid_eq_radialShell

theorem exists_smooth_ellipsoidShell_parametrization
    {n : ℕ} [Fact (_root_.Module.finrank ℝ E = n + 1)]
    (A : E ≃L[ℝ] E) (p : E) {r R : ℝ} (hr : 0 < r) (hp : ‖p‖ < R)
    (hsub : (fun x ↦ A x + p) '' _root_.Metric.closedBall 0 r ⊆ _root_.Metric.ball 0 R)
    (v : _root_.Metric.sphere (0 : E) 1) :
    ∃ e : PartialEquiv (_root_.Metric.sphere (0 : E) 1 × unitInterval) E,
      e.source = _root_.Set.univ ∧ e.target = _root_.Metric.closedBall 0 R \ (fun x ↦ A x + p) '' _root_.Metric.ball 0 r ∧
      ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, E) ∞ e ∧
      ContMDiffOn 𝓘(ℝ, E) ((𝓡 n).prod (𝓡∂ 1)) ∞ e.symm e.target := by
  let a := ellipsoidRadialFunction A r
  let b := fun u : _root_.Metric.sphere (0 : E) 1 ↦ DifferentialGeometry.Analysis.ballRadialFunction p R (u : E)
  have ha : ∀ u, 0 < a u := ellipsoidRadialFunction_pos A hr
  have hab : ∀ u, a u < b u := ellipsoidRadialFunction_lt_ballRadialFunction A p hr hp hsub
  have has : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ a := contMDiff_ellipsoidRadialFunction A r
  have hbs : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ b :=
    (DifferentialGeometry.Analysis.contDiff_ballRadialFunction hp).contMDiff.comp contMDiff_coe_sphere
  refine ⟨radialShellEquiv p a b v ha hab, rfl, ?_,
    contMDiff_radialShellInclusion p a b has hbs,
    contMDiffOn_radialShellProjection p a b v hab has hbs⟩
  exact (closedBall_diff_openEllipsoid_eq_radialShell A p hr hp v).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.exists_smooth_ellipsoidShell_parametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.exists_smooth_ellipsoidShell_parametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.exists_smooth_ellipsoidShell_parametrization ``Submission.DifferentialGeometry.Topology.Manifold.exists_smooth_ellipsoidShell_parametrization

end DifferentialGeometry.Topology.Manifold
