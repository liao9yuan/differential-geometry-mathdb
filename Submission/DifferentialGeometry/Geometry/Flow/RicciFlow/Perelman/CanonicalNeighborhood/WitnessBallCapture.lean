import Submission.DifferentialGeometry.Geometry.Metric.Comparison.BallCapture
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import Submission.DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal
import Submission.DifferentialGeometry.Geometry.Metric.DirectLimit.Distance
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import Submission.DifferentialGeometry.Topology.FirstExit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}



section Witness

variable [I.Boundaryless] [NeZero (Module.finrank ℝ E)]

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}
  {x : M} {t kappa : ℝ}

omit [SigmaCompactSpace M] in
theorem witnessSourceBallCapture_on_window
    (W : KappaModelWitness.{u, uE, uH} (I := I) (1 / 4) kappa S x t)
    {s : ℝ} (hs : s ∈ Set.Icc (-(4 : ℝ)) 0) :
    IsCompact (riemannianClosedBallOf (I := I) (witnessGhat (I := I) W s) x 1) ∧
      riemannianClosedBallOf (I := I) (witnessGhat (I := I) W s) x 1 ⊆
        witnessImage (I := I) W := by
  let : TopologicalSpace W.model.M := W.model.topology
  let : ChartedSpace H W.model.M := W.model.charted
  let : IsManifold I ∞ W.model.M := W.model.smooth
  let : IsManifold I 1 W.model.M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by decide)
  let : SigmaCompactSpace W.model.M := W.model.sigmaCompact
  let : T2Space W.model.M := W.model.t2
  let : T2Space (TangentBundle I W.model.M) := W.model.t2TangentBundle
  let B := riemannianClosedBallOf (I := I) (W.model.S.base.metric 0) W.model.basepoint 2
  have hBcompact : IsCompact B := by
    apply RiemannianMetricComplete.closedEBall_isCompact
    refine ⟨?_⟩
    with_unfolding_all
      exact MetricComplete.complete (I := I) (W.model.atTime (I := I) 0)
        (W.model_ancient.complete 0 (by simp))
  have hBsource : B ⊆ W.embedding.source :=
    (riemannianClosedBallOf_mono (I := I) (W.model.S.base.metric 0) W.model.basepoint
      (by rw [modelRadius_quarter]; norm_num : (2 : ℝ) ≤ modelRadius (1 / 4) + 1)).trans
      W.comparison.buffered_ball_subset
  have hcapture : riemannianClosedBallOf (I := I) (witnessGhat (I := I) W s)
      (W.embedding W.model.basepoint) 1 ⊆ (W.embedding : W.model.M → M) '' B := by
    apply closedBall_subset_image_of_metric_lower (W.model.S.base.metric 0)
      (witnessGhat (I := I) W s) W.embedding W.model.basepoint
      (L := (3 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) hBcompact hBsource
    intro y hy v
    have htime := ancientModel_metric_zero_le W.model W.model_ancient hs.2 y v
    have hswin : s ∈ Set.Icc (-(modelDepth (1 / 4))) (0 : ℝ) := by
      simpa only [modelDepth, one_div, inv_inv] using hs
    have hywin : y ∈ riemannianClosedBallOf (I := I) (W.model.S.base.metric 0)
        W.model.basepoint (modelRadius (1 / 4)) := by
      simpa only [modelRadius_quarter] using hy
    have hlower := (W.comparison.metric_equivalence s hswin y hywin v).1
    rw [W.comparison.pullback_apply s y (W.comparison.buffered_ball_subset
      (riemannianClosedBallOf_mono (I := I) _ _ (by linarith) hywin))]
      at hlower
    have hnonneg := inner_self_nonneg (I := I) (witnessGhat (I := I) W s)
      (W.embedding y) (mfderiv I I (W.embedding : W.model.M → M) y v)
    change (1 - (1 / 4 : ℝ)) * (W.model.S.base.metric s).inner y v v ≤
      (witnessGhat (I := I) W s).inner (W.embedding y)
        (mfderiv I I (W.embedding : W.model.M → M) y v)
        (mfderiv I I (W.embedding : W.model.M → M) y v) at hlower
    nlinarith
  rw [W.comparison.base_map] at hcapture
  have hmodelBall : B = witnessModelBall (I := I) W := by
    change riemannianClosedBallOf (I := I) (W.model.S.base.metric 0) W.model.basepoint 2 =
      riemannianClosedBallOf (I := I) (W.model.S.base.metric 0) W.model.basepoint
        (modelRadius (1 / 4))
    rw [modelRadius_quarter]
  have himageCompact : IsCompact ((W.embedding : W.model.M → M) '' B) :=
    hBcompact.image_of_continuousOn
      (W.embedding.contMDiffOn_toFun.continuousOn.mono hBsource)
  constructor
  · exact himageCompact.of_isClosed_subset
      (isClosed_le (continuous_riemannianEDist (witnessGhat (I := I) W s) x)
        continuous_const) hcapture
  · simpa only [hmodelBall, witnessImage] using hcapture

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.witnessSourceBallCapture_on_window then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.witnessSourceBallCapture_on_window"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.witnessSourceBallCapture_on_window ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.witnessSourceBallCapture_on_window

theorem witnessSourceBallCapture : WitnessSourceBallCapture.{u, uE, uH} I kappa := by
  intro M _ _ _ _ _ _ D S x t W
  exact witnessSourceBallCapture_on_window W (by norm_num)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.witnessSourceBallCapture then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.witnessSourceBallCapture"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.witnessSourceBallCapture ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.witnessSourceBallCapture

end Witness

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
