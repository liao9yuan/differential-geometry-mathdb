import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformLifetime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

theorem PartialStandardSolution.ricci_quadratic_bound (S : PartialStandardSolution)
    {t K : ℝ} (hK : 0 ≤ K) (x : E3)
    (hRm : Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K)
    (v : TangentSpace (𝓡 3) x) :
    |ricciTensor (S.metric t) x v v| ≤ 9 * K * (S.metric t).inner x v v := by
  have hsq : normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x) ≤ K ^ 2 :=
    (Real.sqrt_le_iff).mp hRm |>.2
  have h := ricci_quadratic_form_bound_of_solution_curvature_bound S.toSolutionOn x v hsq
  simpa only [PartialStandardSolution.toSolutionOn_metric, finrank_euclideanSpace,
    Fintype.card_fin, Nat.cast_ofNat, Real.sqrt_sq hK, show (3 : ℝ) ^ 2 = 9 by norm_num] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.ricci_quadratic_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.ricci_quadratic_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.ricci_quadratic_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.ricci_quadratic_bound

theorem PartialStandardSolution.metric_comparison_closed (S : PartialStandardSolution)
    {θ K : ℝ} (hθT : ENNReal.ofReal θ < S.lifetime) (hK : 0 ≤ K)
    (hRm : ∀ t ∈ _root_.Set.Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (S.metric t) x 4 (metricRm04 (S.metric t) x)) ≤ K)
    (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 θ) (x : E3) (v : TangentSpace (𝓡 3) x) :
    Real.exp (-(18 * K * t)) * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤
      (S.metric t).inner x v v ∧
    (S.metric t).inner x v v ≤
      Real.exp (18 * K * t) * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v := by
  have hdomain : _root_.Set.Icc 0 θ ⊆ S.domain := fun s hs =>
    (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos s).mpr
      ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt hθT⟩
  have hpde : ∀ s ∈ _root_.Set.Icc 0 θ, ∀ (y : E3) (u w : TangentSpace (𝓡 3) y),
      HasDerivWithinAt (fun r => (S.metric r).inner y u w)
        (-2 * ricciTensor (S.metric s) y u w) (_root_.Set.Icc 0 θ) s :=
    fun s hs y u w => (S.equation s (hdomain hs) y u w).mono _root_.Set.Icc_subset_Ici_self
  have hric : ∀ s ∈ _root_.Set.Icc 0 θ, ∀ (y : E3) (u : TangentSpace (𝓡 3) y),
      |ricciTensor (S.metric s) y u u| ≤ (9 * K) * (S.metric s).inner y u u :=
    fun s hs y u => S.ricci_quadratic_bound hK y (hRm s hs y) u
  have h := metricEquiv_Icc S.metric hpde hric t ht x v
  simpa only [S.initial, sub_zero, show (2 : ℝ) * (9 * K) = 18 * K by ring] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.metric_comparison_closed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.metric_comparison_closed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.metric_comparison_closed ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.metric_comparison_closed

theorem uniformStandardLifetime_metricComparison (θ : ℝ) (hθ : 0 ≤ θ)
    (hlt : ENNReal.ofReal θ < uniformStandardLifetime) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∀ S : StandardSolution, ∀ t ∈ _root_.Set.Icc 0 θ,
      t ∈ S.val.domain ∧ ∀ (x : E3) (v : TangentSpace (𝓡 3) x),
        Λ⁻¹ * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v ≤
          (S.val.metric t).inner x v v ∧
        (S.val.metric t).inner x v v ≤
          Λ * DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v := by
  obtain ⟨hT, K, hK, hRm⟩ := uniformStandardLifetime_slab θ hθ hlt
  let Λ : ℝ := Real.exp (18 * K * θ)
  have hΛ : 1 ≤ Λ := Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) hK) hθ)
  refine ⟨Λ, hΛ, ?_⟩
  intro S t ht
  have hdom : t ∈ S.val.domain :=
    (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt (hT S)⟩
  refine ⟨hdom, ?_⟩
  intro x v
  have h := S.val.metric_comparison_closed (hT S) hK (hRm S) t ht x v
  have hscale : 18 * K * t ≤ 18 * K * θ :=
    mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (by norm_num) hK)
  have hnonneg : 0 ≤ DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner x v v := by
    by_cases hv : v = 0
    · simp only [hv, map_zero, le_refl]
    · exact (DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.pos x v hv).le
  constructor
  · have he : Λ⁻¹ ≤ Real.exp (-(18 * K * t)) := by
      rw [show Λ⁻¹ = Real.exp (-(18 * K * θ)) from (Real.exp_neg _).symm]
      exact Real.exp_le_exp.mpr (neg_le_neg hscale)
    exact (mul_le_mul_of_nonneg_right he hnonneg).trans h.1
  · exact h.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hscale) hnonneg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_metricComparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_metricComparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_metricComparison ``Submission.DifferentialGeometry.PDE.RicciFlow.uniformStandardLifetime_metricComparison
end DifferentialGeometry.PDE.RicciFlow
