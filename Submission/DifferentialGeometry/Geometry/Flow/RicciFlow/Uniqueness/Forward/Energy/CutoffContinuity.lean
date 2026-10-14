import Submission.DifferentialGeometry.Analysis.Integration.Measure.Family.CompactSupportContinuity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Measure.DensityRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open _root_.Submission.DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]

theorem forward_uniqueness_cutoff_energy_continuousOn
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : M → ℝ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    {J : Set ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (J ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousOn (fun t => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
      ∂riemannianMeasureFamily g₁ t) J := by
  have hf : ContinuousOn
      (fun p : ℝ × M => χ p.2 ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ p.1 p.2)
      (J ×ˢ (_root_.Set.univ : Set M)) :=
    ((hχ.comp continuous_snd).pow 2).continuousOn.mul
      (dens_jointContMDiffOn (I := I) g₁ g₂ hjoint₁ hjoint₂).continuousOn
  exact continuousOn_integral_riemannianVolumeMeasure_of_compact_support g₁
    (fun α i j => (hjoint₁ α i j).continuousOn)
    (fun t x => χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x) hf hcχ
    (fun _ _ x hx => by simp [image_eq_zero_of_notMem_tsupport hx])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_continuousOn

theorem forward_uniqueness_cutoff_energy_continuousWithinAt_initial
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : M → ℝ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    {a b : ℝ} (hab : a < b)
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (_root_.Set.Ico a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (_root_.Set.Ico a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousWithinAt (fun t => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
      ∂riemannianMeasureFamily g₁ t) (_root_.Set.Ico a b) a :=
  forward_uniqueness_cutoff_energy_continuousOn g₁ g₂ χ hχ hcχ hjoint₁ hjoint₂ a ⟨le_rfl, hab⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_continuousWithinAt_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_continuousWithinAt_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_continuousWithinAt_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_continuousWithinAt_initial

theorem forward_uniqueness_cutoff_energy_tendsto_zero_initial
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : M → ℝ) (hχ : Continuous χ) (hcχ : HasCompactSupport χ)
    {a b : ℝ} (hab : a < b)
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (_root_.Set.Ico a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (_root_.Set.Ico a b ×ˢ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet))
    (heq : g₁ a = g₂ a) :
    Tendsto (fun t => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
      ∂riemannianMeasureFamily g₁ t) (𝓝[_root_.Set.Ico a b] a) (𝓝 0) := by
  have hc := forward_uniqueness_cutoff_energy_continuousWithinAt_initial
    g₁ g₂ χ hχ hcχ hab hjoint₁ hjoint₂
  simpa only [ContinuousWithinAt, density_eq_zero_of_eq (I := I) g₁ g₂ heq,
    _root_.MulZeroClass.mul_zero, _root_.MeasureTheory.integral_zero] using hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_tendsto_zero_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_tendsto_zero_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_tendsto_zero_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_cutoff_energy_tendsto_zero_initial

end DifferentialGeometry.PDE.RicciFlow
