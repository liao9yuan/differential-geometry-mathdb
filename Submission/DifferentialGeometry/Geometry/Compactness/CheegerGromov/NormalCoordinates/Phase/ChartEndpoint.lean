import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Phase.Endpoint
import Submission.DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Convergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [T2Space (TangentBundle I M)] in
theorem _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.phase_endpoint_eq_expMapIntrinsic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {p : M} (c : NormalBallChart (I := I) p)
    {r : ℝ} {R : NNReal} {Z : ℝ → E × E}
    (hrQuarter : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) (c.radius / 4))
    (hZcont : ContinuousOn Z (_root_.Set.Icc (-1) 1))
    (hZwithin : ∀ t ∈ _root_.Set.Icc (-1) 1, HasDerivWithinAt Z
      (PhaseFlow.phaseField (c.accel g) (Z t)) (_root_.Set.Icc (-1) 1) t)
    (hZmem : ∀ t ∈ _root_.Set.Icc (-1) 1, Z t ∈ normalPhaseBox r R) :
    c.hom (Z 1).1 = expMapIntrinsic g hEnorm (c.hom (Z 0).1)
      (mfderiv 𝓘(ℝ, E) I c.hom (Z 0).1 (Z 0).2) := by
  let gamma : ℝ → E := fun t => (Z t).1
  let Gamma : ℝ → M := fun t => c.hom (gamma t)
  have hright : ∀ t ∈ _root_.Set.Ico (-1) 1, HasDerivWithinAt Z
      (PhaseFlow.phaseField (c.accel g) (Z t)) (_root_.Set.Ici t) t := by
    intro t ht
    exact Analysis.ODE.Flow.hasDerivWithinAt_Ici_of_Icc
      (hZwithin t ⟨ht.1, ht.2.le⟩) ht
  have hZsmooth : ContDiffOn ℝ ∞ Z (_root_.Set.Ioo (-1) 1) :=
    chartFlow_contDiff g c (by norm_num) hZcont hright
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ gamma (_root_.Set.Ioo (-1) 1) := by
    rw [contMDiffOn_iff_contDiffOn]
    exact hZsmooth.fst
  have hZat : ∀ t ∈ _root_.Set.Ioo (-1) 1, HasDerivAt Z
      (PhaseFlow.phaseField (c.accel g) (Z t)) t := by
    intro t ht
    exact (hZwithin t (_root_.Set.Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hgeo : Geodesic.IsGeodesicOn (I := 𝓘(ℝ, E))
      (c.totalMetric g) gamma (_root_.Set.Ioo (-1) 1) := by
    exact chartGeoOn_of_phase g c isOpen_Ioo hZat
  have hmem : ∀ t ∈ _root_.Set.Ioo (-1) 1, gamma t ∈ (c.inner : Set E) := by
    intro t ht
    exact hrQuarter (hZmem t (_root_.Set.Ioo_subset_Icc_self ht)).1
  have hGammaGeo : Geodesic.IsGeodesicOn g Gamma (_root_.Set.Ioo (-1) 1) :=
    c.geo_map g gamma (_root_.Set.Ioo (-1) 1) isOpen_Ioo hmem hgamma hgeo
  have hGammaCont : ContinuousOn Gamma (_root_.Set.Icc (-1) 1) := by
    apply c.smooth_to.continuousOn.comp hZcont.fst
    intro t ht
    exact c.inner_subset (hrQuarter (hZmem t ht).1)
  have hv : (mfderiv 𝓘(ℝ, ℝ) I Gamma 0 (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, E) I c.hom (Z 0).1 (Z 0).2 : E) := by
    have hp : (Z 0).1 ∈ Metric.ball (0 : E) c.radius :=
      c.inner_subset (hrQuarter (hZmem 0 (by norm_num)).1)
    have hgammaDeriv : HasDerivAt gamma (Z 0).2 0 := by
      have hfst := ((hZat 0 (by norm_num)).hasFDerivAt.fst).hasDerivAt
      simpa only [gamma, PhaseFlow.phaseField, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.toSpanSingleton_apply,
        one_smul] using hfst
    have hgammaMd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 := by
      rw [mdifferentiableAt_iff_differentiableAt]
      exact hgammaDeriv.differentiableAt
    have hcMd := ((c.smooth_to (Z 0).1 hp).contMDiffAt
      (Metric.isOpen_ball.mem_nhds hp)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (I'' := I)
      (g := c.hom) (f := gamma) (x := (0 : ℝ)) hcMd hgammaMd (1 : ℝ)
    have hgammaMfd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 1 = (Z 0).2 := by
      rw [mfderiv_eq_fderiv]
      exact (fderiv_apply_one_eq_deriv (f := gamma) (x := (0 : ℝ))).trans hgammaDeriv.deriv
    change mfderiv 𝓘(ℝ, ℝ) I Gamma 0 1 =
      mfderiv 𝓘(ℝ, E) I c.hom (Z 0).1 (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) gamma 0 1) at hcomp
    exact hcomp.trans (congrArg (fun v : E => mfderiv 𝓘(ℝ, E) I c.hom (Z 0).1 v) hgammaMfd)
  exact geo_end_eq_intr g hEnorm (Gamma 0)
    (mfderiv 𝓘(ℝ, E) I c.hom (Z 0).1 (Z 0).2) hGammaCont hGammaGeo rfl hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.phase_endpoint_eq_expMapIntrinsic then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.phase_endpoint_eq_expMapIntrinsic"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.phase_endpoint_eq_expMapIntrinsic ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.phase_endpoint_eq_expMapIntrinsic

end DifferentialGeometry.CheegerGromovCompactness

end

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem isIntegralCurveOn_metricSpray_of_phase
    (g : SmoothRiemannianMetric I M) {p : M} (c : NormalBallChart (I := I) p)
    (b : c.MetricBounds g) {r : ℝ} {R : NNReal} {Z : ℝ → E × E}
    (hrMetric : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) b.radius)
    (hrQuarter : Metric.ball (0 : E) r ⊆ Metric.ball (0 : E) (c.radius / 4))
    (hZwithin : ∀ t ∈ _root_.Set.Icc (-1) 1, HasDerivWithinAt Z
      (PhaseFlow.phaseField (c.accel g) (Z t)) (_root_.Set.Icc (-1) 1) t)
    (hZmem : ∀ t ∈ _root_.Set.Icc (-1) 1, Z t ∈ normalPhaseBox r R) :
    IsIntegralCurveOn Z (fun _ => MetricKoszul.metricSpray (c.metric g)) (_root_.Set.Icc 0 1) := by
  have hsmall : _root_.Set.Icc (0 : ℝ) 1 ⊆ _root_.Set.Icc (-1) 1 := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  intro t ht
  have hder := (hZwithin t (hsmall ht)).mono hsmall
  have hpos := (hZmem t (hsmall ht)).1
  have hco : IsCoercive (c.metric g (Z t).1) := b.equiv.coercive g (hrMetric hpos)
  have hfield : PhaseFlow.phaseField (c.accel g) (Z t) =
      MetricKoszul.metricSpray (c.metric g) (Z t) := by
    rw [MetricKoszul.metricSpray_eq _ _ hco]
    apply Prod.ext
    · rfl
    · exact c.accel_eq g (Z t) (hrQuarter hpos) hco
  rwa [hfield] at hder

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.isIntegralCurveOn_metricSpray_of_phase then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.isIntegralCurveOn_metricSpray_of_phase"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.isIntegralCurveOn_metricSpray_of_phase ``Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart.isIntegralCurveOn_metricSpray_of_phase

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates.NormalBallChart

end
