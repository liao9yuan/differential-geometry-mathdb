import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Submission.DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem completeMetric_exists_minimizing_curve
    (g : SmoothRiemannianMetric I N) (hcomplete : RiemannianMetricComplete (I := I) g)
    (p q : N) (hfin : riemannianEDistOf (I := I) g p q ≠ ⊤) :
    ∃ γ : ℝ → N, ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (_root_.Set.Icc 0 1) ∧
      γ 0 = p ∧ γ 1 = q ∧
      metricPathELength (I := I) g γ 0 1 = riemannianEDistOf (I := I) g p q := by
  let _ : IsManifold I 1 N := IsManifold.of_le (n := ∞) (by decide)
  let _ : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace I N
  let _ : T3Space N := inferInstance
  let _ : _root_.Bundle.RiemannianBundle (fun x : N => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace N := EMetricSpace.ofRiemannianMetric I N
  let _ : PseudoEMetricSpace N := (EMetricSpace.ofRiemannianMetric I N).toPseudoEMetricSpace
  let _ : CompleteSpace N := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hfin' : _root_.Manifold.riemannianEDist I p q ≠ ⊤ := by
    simpa [riemannianEDistOf] using hfin
  obtain ⟨v, hvexp, hvnorm⟩ := minExp_of_ne_top g hEnorm p q hfin'
  let γ : ℝ → N := intrinsicGeodesic (I := I) g hEnorm p v
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (_root_.Set.Icc 0 1) :=
    (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v).mono (_root_.Set.subset_univ _)
  have hγ0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hγ1 : γ 1 = q := by
    change intrinsicGeodesic (I := I) g hEnorm p v 1 = q
    rw [← expMapIntrinsic_def]
    exact hvexp
  refine ⟨γ, hγ, hγ0, hγ1, ?_⟩
  rw [metricPathELength_eq]
  calc
    _ = ∫⁻ _ in _root_.Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
      refine _root_.MeasureTheory.setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
      exact congrArg (fun z : ℝ => ENNReal.ofReal (Real.sqrt z))
        (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p v t)
    _ = ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
      rw [_root_.MeasureTheory.setLIntegral_const, Real.volume_Ioo]
      norm_num
    _ = _root_.Manifold.riemannianEDist I p q := by
      rw [hvnorm]
      exact ENNReal.ofReal_toReal hfin'
    _ = riemannianEDistOf (I := I) g p q :=
      (riemannianEDistOf_eq_riemannianEDist g hEnorm p q).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_exists_minimizing_curve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_exists_minimizing_curve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_exists_minimizing_curve ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.completeMetric_exists_minimizing_curve

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
