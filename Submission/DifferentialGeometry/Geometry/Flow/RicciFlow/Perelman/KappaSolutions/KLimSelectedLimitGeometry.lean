import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimUniformLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimNormalization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section NormalizedSequence

variable {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance klimSelectedLimitSourceTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceTopology
local instance klimSelectedLimitSourceCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceCharted
local instance klimSelectedLimitSourceSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceSmooth
local instance klimSelectedLimitSourceT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceT2
local instance klimSelectedLimitSourceSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.klimSelectedLimitSourceSigma

theorem terminalCurvatureNormalizedFlowSeq_klim_ancient_limit_geometry
    {kappa : ℝ} (hK : KLim kappa F)
    (hdim : Module.finrank ℝ E = 3) (x : ℕ → F.M) (r : ℕ → ℝ)
    (hQ : ∀ i, 0 < F.S.scalar 0 (x i))
    (hlocal : ∀ i z, (riemannianEDistOf (I := I) (F.S.base.metric 0) z (x i)).toReal <
      r i → F.S.scalar 0 z ≤ 4 * F.S.scalar 0 (x i))
    (hexpand : _root_.Filter.Tendsto (fun i => r i * Real.sqrt (F.S.scalar 0 (x i))) _root_.Filter.atTop _root_.Filter.atTop)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (Phi : PointedCGHMaps (I := I) (terminalCurvatureNormalizedFlowSeq F hK x hQ)
      (L.atTime (I := I) 0) phi)
    (hconnected : @ConnectedSpace L.M L.topology)
    (hcomplete : ∀ t ≤ 0, MetricComplete (I := I) (L.atTime (I := I) t))
    (hconv : ∀ t ≤ 0,
      ∃ C : MetricConvergenceData (I := I)
          (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x hQ)
            (L := L) (phi := phi) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (X := terminalCurvatureNormalizedFlowSeq F hK x hQ)
            (L := L) (phi := phi) t) k) :
    IsAncientKappaSolution (I := I) kappa L ∧
      PointedFlowScalarAtBase (I := I) L 1 ∧
      PointedFlowScalarBounded (I := I) L 4 ∧
      PointedFlowRmNormSqBounded (I := I) L 48 := by
  let X := terminalCurvatureNormalizedFlowSeq F hK x hQ
  have htime : X.D.carrier = Set.Iic (0 : ℝ) := by
    change ancientTimeInterval.carrier = Set.Iic (0 : ℝ)
    simp
  have hsource (i : ℕ) : KLim kappa (X.term i) :=
    KLim.curvatureNormalizedFlow F hK
      0 (F.S.scalar 0 (x i)) (hQ i)
      (by simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0))
      (x i) rfl
  have hlocalInput : ∀ A : ℝ, ∀ᶠ i in _root_.Filter.atTop, ∀ t ∈ X.D.carrier,
      ∀ z : (X.term i).M,
        (riemannianEDistOf (I := I) ((X.term i).S.base.metric 0)
          (X.term i).basepoint z).toReal ≤ A →
            0 ≤ (X.term i).S.scalar t z ∧ (X.term i).S.scalar t z ≤ 4 := by
    intro A
    filter_upwards [hexpand (_root_.Filter.eventually_gt_atTop A)] with i hi
    intro t ht z hz
    change F.M at z
    let g : SmoothRiemannianMetric I F.M := ((X.atZero (I := I)).obj i).metric
    have hcomm : riemannianEDistOf (I := I) g z (x i) =
        riemannianEDistOf (I := I) g (x i) z := by
      let _ : _root_.Bundle.RiemannianBundle (fun y : F.M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
      change Manifold.riemannianEDist I z (x i) = Manifold.riemannianEDist I (x i) z
      exact Manifold.riemannianEDist_comm (I := I) (x := z) (y := x i)
    have hz' : (riemannianEDistOf (I := I) g z (x i)).toReal ≤ A := by
      rw [hcomm]
      exact hz
    exact terminalCurvatureNormalizedFlowSeq_scalar_bound F hK x hQ i (r i)
      (hlocal i) (by simpa only [htime, Set.mem_Iic] using ht) z (hz'.trans_lt hi)
  have hlimit := ancientKappaThree_of_uniformly_bounded_KLim_limit X L Phi hdim rfl
    4 (by norm_num) hsource
    (terminalCurvatureNormalizedFlowSeq_scalar_base F hK x hQ) hphi
    hlocalInput hconnected
    (fun t ht => hcomplete t (by simpa only [htime, Set.mem_Iic] using ht))
    (fun t ht => hconv t (by simpa only [htime, Set.mem_Iic] using ht))
  norm_num at hlimit
  exact hlimit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_klim_ancient_limit_geometry then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_klim_ancient_limit_geometry"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_klim_ancient_limit_geometry ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.terminalCurvatureNormalizedFlowSeq_klim_ancient_limit_geometry

end NormalizedSequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
