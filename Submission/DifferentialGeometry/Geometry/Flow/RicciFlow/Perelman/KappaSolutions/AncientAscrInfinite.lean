import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.FiniteAscrPositiveAvr
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientVolumeRatioInvariant
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StandardHarnackLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NoncompactShrinkerAvr
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedAsymptoticVolumeRatio

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientAscrTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrTopology
local instance ancientAscrCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrCharted
local instance ancientAscrSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrSmooth
local instance ancientAscrT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrT2
local instance ancientAscrSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrSigma
local instance ancientAscrTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrTangentT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrTangentT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrTangentT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientAscrTangentT2

theorem ancientKappaThree_terminal_ascr_eq_top {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoncompact : NoncompactSpace F.M) (p : F.M) :
    asymptoticScalarCurvatureRatio (I := I) (F.S.base.metric 0) p = ⊤ := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NoncompactSpace F.M := hnoncompact
  by_contra hfinite
  have hcomplete (t : ℝ) (ht : t ≤ 0) :
      RiemannianMetricComplete (I := I) (F.S.base.metric t) := ⟨hF.complete t ht⟩
  have hoperator (t : ℝ) (ht : t ≤ 0) (x : F.M) :
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator t ht x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval,
      metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
      metricRm04_apply] using h
  have hRicBelow (t : ℝ) (ht : t ≤ 0) :
      RicciBoundedBelow (I := I) (F.S.base.metric t) 0 := by
    intro x v
    rw [_root_.MulZeroClass.zero_mul, ← metricRicciAt_apply_eq_ricciTensor]
    exact metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (F.S.base.metric t) x (hoperator t ht x) v
  have hnc : ∀ (x : F.M) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (I := I) (F.S.base.metric 0) x r,
        r ^ 4 * normSq0S (I := I) (F.S.base.metric 0) y 4
          (metricRm04At (I := I) (F.S.base.metric 0) y) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := F.M) (F.S.base.metric 0)
          (riemannianBallOf (I := I) (F.S.base.metric 0) x r) := by
    intro x r hr hcontrol
    let time : ancientTimeInterval.FlowTime := ⟨0, by simp⟩
    let ball : FlowMetricBall F.S time := ⟨x, r, hr⟩
    have hball : ball.IsSpatiallyRmControlled := by
      intro y hy
      simpa only [ball, time, FlowMetricBall.rmNormSq, SolutionFamily.rm04,
        metricRm04_apply, SolutionOn.family] using hcontrol y hy
    exact (hF.noncollapsed time ball hball).2
  let v := asymptoticVolumeRatio (I := I) (F.S.base.metric 0) p
  have hv : 0 < v :=
    (finite_ascr_positive_avr (F.S.base.metric 0) (hcomplete 0 le_rfl)
      (hoperator 0 le_rfl) kappa hF.kappa_pos hnc p hfinite).2.2.2
  have hdecay := scalar_decay_of_ascr_ne_top (F.S.base.metric 0) p hfinite
  have hK := ancientKappaThree_toKLim F hF hdim
  have htime (t : ℝ) (ht : t < 0) :
      asymptoticVolumeRatio (I := I) (F.S.base.metric t) p = v := by
    exact ancient_asymptoticVolumeRatio_eq_of_later_scalar_decay F.S F.isSolution
      (by omega) hcomplete hoperator hK.traceHarnack ht le_rfl p hdecay
  let tau : ℕ → ℝ := fun i => (i : ℝ) + 1
  have htau : ∀ i, 0 < tau i := by
    intro i
    dsimp only [tau]
    positivity
  have hescape : _root_.Filter.Tendsto tau _root_.Filter.atTop atTop := by
    apply _root_.Filter.tendsto_atTop_mono (fun i => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    dsimp only [tau]
    linarith
  obtain ⟨q, L, phi, _, Phi, C, _, hreference, hcompleteLimit, hgeometry⟩ :=
    exists_noncompact_backward_three_limit_avr_zero F hF hdim hnoncompact tau htau hescape
  let _ : TopologicalSpace L.M := L.topology
  let _ : ChartedSpace H L.M := L.charted
  let _ : IsManifold I ∞ L.M := L.smooth
  let _ : T2Space L.M := L.t2
  let _ : SigmaCompactSpace L.M := L.sigmaCompact
  obtain ⟨_, _, hzero⟩ := hgeometry
  have hsource (i : ℕ) :
      v ≤ asymptoticVolumeRatio (I := I) (M := F.M)
        ((backwardSliceSequence F tau htau q).obj i).metric (q i) := by
    change v ≤ asymptoticVolumeRatio (I := I)
      (scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i)) (F.S.base.metric (-tau i))) (q i)
    rw [asymptoticVolumeRatio_scaleMetric,
      asymptoticVolumeRatio_basepoint_eq (F.S.base.metric (-tau i))
        (hcomplete (-tau i) (neg_nonpos.mpr (htau i).le))
        (hRicBelow (-tau i) (neg_nonpos.mpr (htau i).le)) (q i) p,
      htime (-tau i) (neg_lt_zero.mpr (htau i))]
  have hlower := asymptoticVolumeRatio_lower_of_pointed_metric_convergence
    C hreference hcompleteLimit v hsource
  rw [hzero L.basepoint] at hlower
  exact (not_le_of_gt hv) hlower

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_terminal_ascr_eq_top then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_terminal_ascr_eq_top"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_terminal_ascr_eq_top ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappaThree_terminal_ascr_eq_top

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
