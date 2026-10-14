import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.SqrtSupport
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness
import Submission.DifferentialGeometry.Geometry.Geodesic.EquationGerm
import Submission.DifferentialGeometry.Bundle.FiberBundleHausdorff

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.ENNReal

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem sqrt_sub_le_distance_of_geodesic_upper_support
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    {u : M → ℝ} (hu : Continuous u) {C : ℝ} (hC : 0 ≤ C)
    (hsupport : ∀ (gamma : ℝ → M) (t : ℝ),
      IsGeodesicAt (I := I) g gamma t → 0 < u (gamma t) → ∃ phi : ℝ → ℝ, ∃ d : ℝ,
        phi t = u (gamma t) ∧ (u ∘ gamma) ≤ᶠ[𝓝[>] t] phi ∧
        HasDerivAt phi d t ∧
          d ≤ 2 * C * Real.sqrt (u (gamma t)) * Real.sqrt (g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)))
    (x y : M) (hfin : riemannianEDistOf g x y ≠ ⊤) :
    Real.sqrt (u y) ≤ Real.sqrt (u x) + C * (riemannianEDistOf g x y).toReal := by
  let manifoldOne : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ := manifoldOne
  let metrizable : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ := metrizable
  let regular : T3Space M := inferInstance
  let _ := regular
  let riemannian : _root_.Bundle.RiemannianBundle (fun z : M ↦ TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  let _ := riemannian
  let riemannianContinuous : IsContinuousRiemannianBundle E (fun z : M ↦ TangentSpace I z) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro z v w; rfl⟩⟩
  let _ := riemannianContinuous
  let emetric : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ := emetric
  let pseudoEmetric : PseudoEMetricSpace M := emetric.toPseudoEMetricSpace
  let _ := pseudoEmetric
  let complete : CompleteSpace M := hg.complete
  let _ := complete
  have hEnorm : IsMetricNorm (I := I) g :=
    fun z v ↦ tensor0SBundle_enorm_eq_riemannianBundle_enorm g z v
  have hfin' : _root_.Manifold.riemannianEDist I x y ≠ ⊤ := by
    simpa only [riemannianEDistOf] using hfin
  obtain ⟨v, hvexp, hvnorm⟩ := minExp_of_ne_top g hEnorm x y hfin'
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x v
  have hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma := intrinsicGeodesic_contMDiff g hEnorm x v
  let completeModel : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ := completeModel
  have hgeodesic (t : ℝ) : IsGeodesicAt (I := I) g gamma t :=
    isGeodesicAt_of_isGeodesicOn g _root_.Filter.univ_mem
      ((intrinsicGeodesic_isGeodesic g hEnorm x v).isGeodesicOn _root_.Set.univ)
      hgamma.continuous.continuousOn
  have hgamma0 : gamma 0 = x := intrinsicGeodesic_zero g hEnorm x v
  have hgamma1 : gamma 1 = y := by
    change intrinsicGeodesic (I := I) g hEnorm x v 1 = y
    rw [← expMapIntrinsic_def]
    exact hvexp
  have hspeed (t : ℝ) : Real.sqrt (g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)) = (riemannianEDistOf g x y).toReal := by
    rw [show g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t 1)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t 1) = g.inner x v v from
      intrinsicGeodesic_speedSq_eq g hEnorm x v t]
    exact hvnorm
  have hbound := sqrt_le_of_deriv_upper_support
    (a := 0) (b := 1) (C := C * (riemannianEDistOf g x y).toReal)
    ((hu.comp hgamma.continuous).continuousOn) (mul_nonneg hC ENNReal.toReal_nonneg)
    (fun t _ht htpos ↦ by
      obtain ⟨phi, d, heq, hupper, hd, hbnd⟩ := hsupport gamma t (hgeodesic t) htpos
      refine ⟨phi, d, heq, hupper, hd, ?_⟩
      rw [hspeed] at hbnd
      simpa only [Function.comp_apply, mul_assoc, mul_comm, mul_left_comm] using hbnd) 1 (by constructor <;> norm_num)
  simpa only [Function.comp_apply, hgamma0, hgamma1, sub_zero, mul_one] using hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.sqrt_sub_le_distance_of_geodesic_upper_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.sqrt_sub_le_distance_of_geodesic_upper_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.sqrt_sub_le_distance_of_geodesic_upper_support ``Submission.DifferentialGeometry.Geometry.sqrt_sub_le_distance_of_geodesic_upper_support

end DifferentialGeometry.Geometry
