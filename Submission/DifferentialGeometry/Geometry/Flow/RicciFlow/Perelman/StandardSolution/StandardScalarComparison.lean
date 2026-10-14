import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardActionComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarLower
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureComparison
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Tensor0SBundle _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Submission.ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.StandardCap.E3 target :: scope.openDecls } }

theorem exists_uniform_scalar_bound_of_standard_metric_close_on_opens
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ ε A : ℝ, 0 < ε ∧ 0 < A ∧
      ∀ (U : _root_.TopologicalSpace.Opens E3) (g : SmoothRiemannianMetric (𝓡 3) U)
        (S : StandardSolution) (τ : ℝ), τ ∈ _root_.Set.Icc 0 θ → ∀ x : U,
        (∀ j ≤ 2, metricDerivNorm j g ((S.val.metric τ).restrictOpen U)
          (metric.restrictOpen U) x ≤ ε) →
        |metricScalarAt g x| ≤ A := by
  obtain ⟨ε, P, hε, hP, hcurv⟩ :=
    exists_uniform_curvature_bound_of_standard_metric_close_on_opens θ hθ hθ1
  refine ⟨ε, 9 * P, hε, by positivity, ?_⟩
  intro U g S τ hτ x hclose
  have hscalar := scalar_abs_le_rm g x
  change |metricScalarAt g x| ≤ (Module.finrank ℝ E3 : ℝ) ^ 2 *
    Real.sqrt (normSq0S g x 4 (metricRm04 g x)) at hscalar
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
    show (3 : ℝ) ^ 2 = 9 by norm_num] at hscalar
  exact hscalar.trans (mul_le_mul_of_nonneg_left (hcurv U g S τ hτ x hclose) (by norm_num))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_scalar_bound_of_standard_metric_close_on_opens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_scalar_bound_of_standard_metric_close_on_opens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_scalar_bound_of_standard_metric_close_on_opens ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_scalar_bound_of_standard_metric_close_on_opens

theorem exists_uniform_scalar_lower_bound_of_standard_metric_close_on_opens
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (U : _root_.TopologicalSpace.Opens E3) (g : SmoothRiemannianMetric (𝓡 3) U)
        (S : StandardSolution) (t : ℝ), t ∈ _root_.Set.Icc 0 θ → ∀ x : U,
        (∀ j ≤ 2, metricDerivNorm j g ((S.val.metric t).restrictOpen U)
          (metric.restrictOpen U) x ≤ ε) →
        1 / 2 ≤ metricScalarAt g x := by
  obtain ⟨ε,hε,hcomparison⟩ := exists_uniform_standard_metric_scalar_lower_comparison θ hθ hθ1
  refine ⟨ε,hε,?_⟩
  intro U g S t ht x hclose
  have hcompare := (hcomparison S U g t ht x hclose).2
  have hdom : t ∈ S.val.domain := by
    apply (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos t).mpr
    refine ⟨ht.1,?_⟩
    rw [S.lifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr (ht.2.trans_lt hθ1)
  have hlower := S.val.one_le_scalar t hdom x.val
  rw [metricScalarAt_restrictOpen] at hcompare
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_scalar_lower_bound_of_standard_metric_close_on_opens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_scalar_lower_bound_of_standard_metric_close_on_opens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_scalar_lower_bound_of_standard_metric_close_on_opens ``Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_uniform_scalar_lower_bound_of_standard_metric_close_on_opens

end DifferentialGeometry.PDE.RicciFlow.StandardCap
