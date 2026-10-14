import Submission.DifferentialGeometry.Analysis.Calculus.Manifold.Derivative.Measurable
import Submission.DifferentialGeometry.Geometry.Metric.Family.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}

theorem MetricFamilySmoothOn.metricQuadratic_continuousOn_carrier
    (hg : MetricFamilySmoothOn D g) :
    ContinuousOn (fun p : ℝ × TangentBundle I M => (g p.1).inner p.2.proj p.2.2 p.2.2)
      (D.carrier ×ˢ _root_.Set.univ) := by
  have hmetric : ContinuousOn (fun p : ℝ × TangentBundle I M =>
      TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2.proj ((g p.1).inner p.2.proj)) (D.carrier ×ˢ _root_.Set.univ) :=
    hg.metricCLMSection_continuousOn_carrier.comp
      (continuous_fst.prodMk ((FiberBundle.continuous_proj E (TangentSpace I)).comp
        continuous_snd)).continuousOn (fun p hp => ⟨hp.1, _root_.Set.mem_univ _⟩)
  have hvec : ContinuousOn (fun p : ℝ × TangentBundle I M =>
      TotalSpace.mk' E (E := TangentSpace I) p.2.proj p.2.2) (D.carrier ×ˢ _root_.Set.univ) :=
    continuous_snd.continuousOn
  have htotal := ContinuousOn.clm_bundle_apply₂
    (𝕜 := ℝ) (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := Bundle.Trivial M ℝ)
    (b := fun p : ℝ × TangentBundle I M => p.2.proj) hmetric hvec hvec
  have hprod := (Bundle.Trivial.homeomorphProd M ℝ).continuous.comp_continuousOn htotal
  exact (continuous_snd.comp_continuousOn hprod).congr fun _ _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.metricQuadratic_continuousOn_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.metricQuadratic_continuousOn_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.metricQuadratic_continuousOn_carrier ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.metricQuadratic_continuousOn_carrier

variable [I.Boundaryless]

theorem MetricFamilySmoothOn.aemeasurable_metricQuadratic_mfderiv
    (hg : MetricFamilySmoothOn D g) {μ : _root_.MeasureTheory.Measure ℝ} {Ω : Set ℝ} (hΩ : IsOpen Ω)
    (γ : ℝ → M) (hγ : ContinuousOn γ Ω)
    (hd : ∀ᵐ t ∂μ.restrict Ω, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (τ : ℝ → ℝ) (hτ : ContinuousOn τ Ω) (hclock : _root_.Set.MapsTo τ Ω D.carrier) :
    AEMeasurable (fun t => (g (τ t)).inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) (μ.restrict Ω) := by
  apply Manifold.aemeasurable_continuous_tangentMap hΩ γ hγ hd
    (fun p => (g (τ p.1)).inner p.2.proj p.2.2 p.2.2)
  exact hg.metricQuadratic_continuousOn_carrier.comp
    ((hτ.comp continuous_fst.continuousOn (fun p hp => hp.1)).prodMk
      continuous_snd.continuousOn) (fun p hp => ⟨hclock hp.1, _root_.Set.mem_univ _⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.aemeasurable_metricQuadratic_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.aemeasurable_metricQuadratic_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.aemeasurable_metricQuadratic_mfderiv ``Submission.DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn.aemeasurable_metricQuadratic_mfderiv

end DifferentialGeometry.Geometry.Curvature
