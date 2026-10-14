import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.Defs
import Submission.DifferentialGeometry.Geometry.Metric.Completeness
import Submission.DifferentialGeometry.Geometry.Curvature.Metric.Defs
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceMorse
import Submission.DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceIsometry
import Submission.DifferentialGeometry.Geometry.Curvature.Coordinates.RiemannTensorBridge
import Submission.DifferentialGeometry.Geometry.Metric.ModelChange
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem complete_surface_shrinker_compact_constant_scalar
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    {sigma : ℝ} (hsigma : 0 < sigma) (hdim : Module.finrank ℝ E = 2)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsoliton : gradientRicciSoliton (I := I) g f sigma)
    (hnonflat : ∃ x : M, metricScalarAt (I := I) g x ≠ 0) :
    CompactSpace M ∧ ∀ x : M, metricScalarAt (I := I) g x = sigma := by
  have hcompact : CompactSpace M := by
    by_contra hnc
    let _ : NoncompactSpace M := not_compactSpace_iff.mp hnc
    let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin 2) := (toEuclidean (E := E)).trans
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdim)).toContinuousLinearEquiv
    let J := I.transContinuousLinearEquiv L
    let Phi : M ≃ₘ⟮I, J⟯ M := ContinuousLinearEquiv.toTransContinuousLinearEquiv I M L
    let k : SmoothRiemannianMetric J M := g.transContinuousLinearEquiv L
    let u : C^∞⟮J, M; ℝ⟯ := f.comp Phi.symm.toContMDiffMap
    have hk : RiemannianMetricComplete (I := J) k :=
      RiemannianMetricComplete.pullbackCross g Phi.symm hcomplete
    have hu : gradientRicciSoliton (I := J) k u sigma :=
      gradientRicciSoliton_pullbackCross hsoliton Phi.symm
    have hdimJ : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 :=
      finrank_euclideanSpace_fin
    obtain ⟨e, b, hmetric, hp⟩ :=
      gradientRicciSoliton_exists_gaussian_isometry_of_finrank_eq_two_of_noncompact
        (I := J) hk hu hsigma hdimJ
    have hmetric' : Diffeomorph.pullbackMetricCross
        (euclideanMetric (E := EuclideanSpace ℝ (Fin 2))) (Phi.trans e) = g := by
      rw [← Diffeomorph.pullbackMetricCross_trans, hmetric]
      exact SmoothRiemannianMetric.pullback_transContinuousLinearEquiv g L
    obtain ⟨x, hx⟩ := hnonflat
    refine hx ?_
    have hcross := DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross (I := I) (J := 𝓡 2)
      (euclideanMetric (E := EuclideanSpace ℝ (Fin 2))) (Phi.trans e) x
    rw [hmetric'] at hcross
    rw [hcross]
    exact metricScalarAt_eq_zero_of_metricRm04At_eq_zero _ _
      (euclideanMetric_metricRm04At_eq_zero _)
  refine ⟨hcompact, ?_⟩
  obtain ⟨C, hnormalized⟩ :=
    gradientRicciSoliton_exists_normalized (I := I) hcomplete hsoliton hsigma
  intro x
  have hhat : metricScalarAt (I := I)
      (scaleMetric (I := I) sigma hsigma g) x = 1 :=
    normalizedGradientRicciSoliton_scalar_eq_one_of_compact_of_finrank_eq_two
      (I := I) hnormalized hdim x
  rw [metricScalarAt_scaleMetric] at hhat
  have hmul := congrArg (fun t : ℝ => sigma * t) hhat
  field_simp at hmul
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.complete_surface_shrinker_compact_constant_scalar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.complete_surface_shrinker_compact_constant_scalar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.complete_surface_shrinker_compact_constant_scalar ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.complete_surface_shrinker_compact_constant_scalar

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
