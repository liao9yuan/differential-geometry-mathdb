import Submission.DifferentialGeometry.Geometry.Metric.Family.Measurable
import Submission.DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {D : RealTimeInterval}

theorem aestronglyMeasurable_lRegularizedLagrangian
    (S : SolutionOn (I := I) (M := M) D) (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S) {μ : _root_.MeasureTheory.Measure ℝ} {Ω : Set ℝ}
    (hΩ : IsOpen Ω) (T : ℝ) (γ : ℝ → M) (hγ : ContinuousOn γ Ω)
    (hd : ∀ᵐ t ∂μ.restrict Ω, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (hclock : ∀ t ∈ Ω, T - t ^ 2 ∈ D.carrier) :
    AEStronglyMeasurable (lRegularizedLagrangian S T γ) (μ.restrict Ω) := by
  have hτ : ContinuousOn (fun t : ℝ => T - t ^ 2) Ω :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn
  have hkin : AEMeasurable (fun t => (S.family.metric (T - t ^ 2)).inner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))
      (μ.restrict Ω) :=
    MetricFamilySmoothOn.aemeasurable_metricQuadratic_mfderiv
      (I := I) (M := M) (μ := μ) (Ω := Ω) hMet hΩ γ hγ hd
      (fun t => T - t ^ 2) hτ hclock
  have hpair : ContinuousOn (fun t : ℝ => (T - t ^ 2, γ t)) Ω := hτ.prodMk hγ
  have hmaps : _root_.Set.MapsTo (fun t : ℝ => (T - t ^ 2, γ t)) Ω (D.carrier ×ˢ (_root_.Set.univ : Set M)) :=
    fun t ht => ⟨hclock t ht, _root_.Set.mem_univ _⟩
  have hscalar : ContinuousOn (fun t => S.scalar (T - t ^ 2) (γ t)) Ω := by
    simpa only [Function.comp_def] using hSc.scalar_continuousOn.comp hpair hmaps
  have hsc : AEMeasurable (fun t => S.scalar (T - t ^ 2) (γ t)) (μ.restrict Ω) :=
    hscalar.aemeasurable hΩ.measurableSet
  have hweight : AEMeasurable (fun t : ℝ => 2 * t ^ 2) (μ.restrict Ω) :=
    (continuous_const.mul (continuous_id.pow 2)).measurable.aemeasurable
  have hkinScalar : AEMeasurable (fun t => (1 / 2 : ℝ) *
      (S.base.metric (T - t ^ 2)).inner (γ t) (lVelocity γ t) (lVelocity γ t))
      (μ.restrict Ω) := by
    change AEMeasurable (fun t => (1 / 2 : ℝ) *
      (S.family.metric (T - t ^ 2)).inner (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ))) (μ.restrict Ω)
    exact aemeasurable_const.mul hkin
  have hsc' : AEMeasurable (fun t => 2 * t ^ 2 * S.scalar (T - t ^ 2) (γ t))
      (μ.restrict Ω) := hweight.mul hsc
  have hlag : AEMeasurable (lRegularizedLagrangian S T γ) (μ.restrict Ω) := by
    unfold lRegularizedLagrangian
    exact hkinScalar.add hsc'
  exact hlag.aestronglyMeasurable

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.aestronglyMeasurable_lRegularizedLagrangian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.aestronglyMeasurable_lRegularizedLagrangian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.aestronglyMeasurable_lRegularizedLagrangian ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.aestronglyMeasurable_lRegularizedLagrangian

theorem aestronglyMeasurable_lRegularizedLagrangian_of_absolutelyContinuousOnInterval
    (S : SolutionOn (I := I) (M := M) D) (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S) (T : ℝ) (γ : ℝ → M) {a b : ℝ}
    (hγ : Manifold.absolutelyContinuousOnInterval I γ a b)
    (hclock : ∀ t ∈ _root_.Set.Ioo a b, T - t ^ 2 ∈ D.carrier) :
    AEStronglyMeasurable (lRegularizedLagrangian S T γ) (volume.restrict (_root_.Set.Ioo a b)) := by
  apply aestronglyMeasurable_lRegularizedLagrangian S hMet hSc isOpen_Ioo T γ
    (hγ.1.mono (Ioo_subset_Icc_self.trans _root_.Set.Icc_subset_uIcc)) _ hclock
  exact (Manifold.absolutelyContinuousOnInterval_ae_mdifferentiableAt hγ).filter_mono
    (_root_.MeasureTheory.ae_mono (Measure.restrict_mono (Ioo_subset_Icc_self.trans _root_.Set.Icc_subset_uIcc) le_rfl))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.aestronglyMeasurable_lRegularizedLagrangian_of_absolutelyContinuousOnInterval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.aestronglyMeasurable_lRegularizedLagrangian_of_absolutelyContinuousOnInterval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.aestronglyMeasurable_lRegularizedLagrangian_of_absolutelyContinuousOnInterval ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.aestronglyMeasurable_lRegularizedLagrangian_of_absolutelyContinuousOnInterval

end DifferentialGeometry.PDE.RicciFlow.Perelman
