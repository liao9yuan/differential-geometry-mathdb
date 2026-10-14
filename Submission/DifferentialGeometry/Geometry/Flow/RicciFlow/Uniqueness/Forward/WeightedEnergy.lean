import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.WeightedIntegratedCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.WeightedVanishing
import Submission.DifferentialGeometry.Analysis.ODE.Gronwall.Integrable
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.DominatedIntegral

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Analysis _root_.Submission.DifferentialGeometry.Analysis.ODE
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

theorem forward_unique_on_Ioo_of_uniform_bounds_of_weighted_energy_tendsto_zero
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (_root_.Set.Ioo a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (_root_.Set.Ioo a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ _root_.Set.Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (_root_.Set.Ici a) t)
    (hpde₂ : ∀ t ∈ _root_.Set.Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (_root_.Set.Ici a) t)
    {C R₁ R₂ D₁ D₂ : ℝ} (hC : 1 ≤ C)
    (hEquiv : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M, ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hR₁ : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ R₁)
    (hR₂ : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ R₂)
    (hD₁ : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ D₁)
    (hD₂ : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t)))) x) ≤ D₂)
    (η : C^∞⟮I, M; ℝ⟯) {A : ℝ} (hA : 0 ≤ A)
    (hηgrad : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) η x) ≤ A * η x ^ 2)
    (Kex : CompactExhaustion M) (χ : ℕ → C^∞⟮I, M; ℝ⟯)
    (hχsupport : ∀ n, HasCompactSupport (χ n : M → ℝ))
    (hχone : ∀ n, ∀ x ∈ Kex n, χ n x = 1)
    (hχrange : ∀ n x, |χ n x| ≤ 1) {L : ℝ}
    (hχgrad : ∀ n, ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) (χ n) x) ≤ L)
    (hden : ∀ t ∈ _root_.Set.Ioo a b,
      Integrable (fun x => η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x)
        (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hEint : ∀ c ∈ _root_.Set.Ioo a b,
      IntervalIntegrable (fun t => ∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
        ∂riemannianMeasureFamily (I := I) (M := M) g₁ t) _root_.MeasureTheory.MeasureSpace.volume a c)
    (hη : ∀ t ∈ _root_.Set.Ioo a b, ∀ᵐ x ∂riemannianMeasureFamily (I := I) g₁ t, η x ≠ 0)
    (hEzero : _root_.Filter.Tendsto (fun t => ∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
      ∂riemannianMeasureFamily (I := I) (M := M) g₁ t) (𝓝[>] a) (𝓝 0)) :
    ∀ t ∈ _root_.Set.Ioo a b, g₁ t = g₂ t := by
  obtain ⟨K, hK, hbound⟩ := forward_uniqueness_weighted_energy_sub_le_integral_on_Ioo_of_uniform_bounds
    (I := I) g₁ g₂ hjoint₁ hjoint₂ hpde₁ hpde₂ hC hEquiv hR₁ hR₂ hD₁ hD₂
    η hA hηgrad Kex χ hχsupport hχone hχrange hχgrad hden hEint
  have hzero := eq_zero_of_nonneg_of_sub_le_mul_integral_of_tendsto hK
    (fun t _ => _root_.MeasureTheory.integral_nonneg fun x =>
      mul_nonneg (sq_nonneg _) (density_nonneg (I := I) g₁ g₂ t x))
    hEint hEzero hbound
  intro t ht
  exact metric_eq_of_weighted_energy_zero (I := I) g₁ g₂ η (hη t ht) (hden t ht) (hzero t ht)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_uniform_bounds_of_weighted_energy_tendsto_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_uniform_bounds_of_weighted_energy_tendsto_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_uniform_bounds_of_weighted_energy_tendsto_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_uniform_bounds_of_weighted_energy_tendsto_zero

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instBorelSpace_differentialGeometry target :: scope.openDecls } }

theorem forward_unique_on_Ioo_of_uniform_bounds_of_dominated_density_tendsto_zero
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (_root_.Set.Ioo a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (_root_.Set.Ioo a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ _root_.Set.Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (_root_.Set.Ici a) t)
    (hpde₂ : ∀ t ∈ _root_.Set.Ioo a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (_root_.Set.Ici a) t)
    {C R₁ R₂ D₁ D₂ : ℝ} (hC : 1 ≤ C)
    (hEquiv : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M, ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hR₁ : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ R₁)
    (hR₂ : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ R₂)
    (hD₁ : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ D₁)
    (hD₂ : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t)))) x) ≤ D₂)
    (η : C^∞⟮I, M; ℝ⟯) {A : ℝ} (hA : 0 ≤ A)
    (hηgrad : ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) η x) ≤ A * η x ^ 2)
    (Kex : CompactExhaustion M) (χ : ℕ → C^∞⟮I, M; ℝ⟯)
    (hχsupport : ∀ n, HasCompactSupport (χ n : M → ℝ))
    (hχone : ∀ n, ∀ x ∈ Kex n, χ n x = 1)
    (hχrange : ∀ n x, |χ n x| ≤ 1) {L : ℝ}
    (hχgrad : ∀ n, ∀ t ∈ _root_.Set.Ioo a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 1 (differential1FormFun (I := I) (χ n) x) ≤ L)
    (hden : ∀ t ∈ _root_.Set.Ioo a b,
      Integrable (fun x => η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x)
        (riemannianMeasureFamily (I := I) (M := M) g₁ t))
    (hEint : ∀ c ∈ _root_.Set.Ioo a b,
      IntervalIntegrable (fun t => ∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
        ∂riemannianMeasureFamily (I := I) (M := M) g₁ t) _root_.MeasureTheory.MeasureSpace.volume a c)
    (hη : ∀ t ∈ _root_.Set.Ioo a b, ∀ᵐ x ∂riemannianMeasureFamily (I := I) g₁ t, η x ≠ 0)
    (μ : _root_.MeasureTheory.Measure M) (G : M → ℝ)
    (hμ : ∀ᶠ t in 𝓝[>] a, riemannianMeasureFamily (I := I) (M := M) g₁ t ≤ μ)
    (hG : _root_.MeasureTheory.Integrable G μ)
    (hdom : ∀ᶠ t in 𝓝[>] a, ∀ᵐ x ∂μ,
      η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ≤ G x)
    (hzero : ∀ᵐ x ∂μ, _root_.Filter.Tendsto (fun t => forwardUniqueDensity (I := I) g₁ g₂ t x)
      (𝓝[>] a) (𝓝 0)) :
    ∀ t ∈ _root_.Set.Ioo a b, g₁ t = g₂ t := by
  apply forward_unique_on_Ioo_of_uniform_bounds_of_weighted_energy_tendsto_zero
    (I := I) g₁ g₂ hjoint₁ hjoint₂ hpde₁ hpde₂ hC hEquiv hR₁ hR₂ hD₁ hD₂
    η hA hηgrad Kex χ hχsupport hχone hχrange hχgrad hden hEint hη
  apply tendsto_integral_zero_of_dominated_measure_family hμ hG
  · exact Eventually.of_forall fun t =>
      ((η.contMDiff.continuous.pow 2).mul (dens_continuous (I := I) g₁ g₂ t)).aestronglyMeasurable
  · filter_upwards [hdom] with t ht
    filter_upwards [ht] with x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sq_nonneg _) (density_nonneg (I := I) g₁ g₂ t x))]
  · filter_upwards [hzero] with x hx
    simpa only [_root_.MulZeroClass.mul_zero] using hx.const_mul (η x ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_uniform_bounds_of_dominated_density_tendsto_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_uniform_bounds_of_dominated_density_tendsto_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_uniform_bounds_of_dominated_density_tendsto_zero ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_unique_on_Ioo_of_uniform_bounds_of_dominated_density_tendsto_zero

end DifferentialGeometry.PDE.RicciFlow
