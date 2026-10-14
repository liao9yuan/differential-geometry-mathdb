import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimFixedKappaCompactness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RankOneTerminalBounded

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
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

section General

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance threeDimBoundedTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedTopology
local instance threeDimBoundedCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedCharted
local instance threeDimBoundedSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedSmooth
local instance threeDimBoundedT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedT2
local instance threeDimBoundedSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeDimBoundedSigma

attribute [local instance] terminalTrichotomyInhabited
  terminalTrichotomyLocallyPathConnected
  terminalTrichotomySemilocallySimplyConnected


theorem KLim.rankOne_branch {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hdim : Module.finrank ℝ E = 3) :
    ∀ _P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0),
      BddAbove (Set.range (F.S.scalar 0)) :=
  fun P => hK.rankOne_terminal_scalar_bddAbove hdim P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.rankOne_branch then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.rankOne_branch"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.rankOne_branch ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.rankOne_branch


theorem KLim.three_terminal_scalar_bddAbove {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    BddAbove (Set.range (F.S.scalar 0)) :=
  KLim.three_terminal_scalar_bddAbove_of_rankOne F hK hdim
    (hK.rankOne_branch F hdim)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.three_terminal_scalar_bddAbove then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.three_terminal_scalar_bddAbove"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.three_terminal_scalar_bddAbove ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.three_terminal_scalar_bddAbove


theorem KLim.scalar_bounded {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    ∃ C : ℝ, PointedFlowScalarBounded (I := I) F C :=
  KLim.scalar_bounded_of_rankOne F hK hdim (hK.rankOne_branch F hdim)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.scalar_bounded then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.scalar_bounded"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.scalar_bounded ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.scalar_bounded


theorem KLim.isAncientKappaSolution {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    IsAncientKappaSolution (I := I) kappa F :=
  KLim.isAncientKappaSolution_of_rankOne F hK hdim (hK.rankOne_branch F hdim)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.isAncientKappaSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.isAncientKappaSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.isAncientKappaSolution ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.isAncientKappaSolution

end General

section FixedKappa

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  terminalTrichotomyInhabited terminalTrichotomyLocallyPathConnected
  terminalTrichotomySemilocallySimplyConnected


theorem exists_fixed_kappa_compactness
    (X : PointedFlowSeq.{u, 0, 0} (I := I3))
    (hD : X.D = ancientTimeInterval) {κ : ℝ}
    (hsource : ∀ i, KLim (I := I3) κ (X.term i))
    (hbase : ∀ i, PointedFlowScalarAtBase (I := I3) (X.term i) 1) :
    ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) X.D) (phi : ℕ → ℕ),
      StrictMono phi ∧
      ∃ Phi : PointedCGHMaps (I := I3) X (L.atTime (I := I3) 0) phi,
        KLim (I := I3) κ L ∧ PointedFlowScalarAtBase (I := I3) L 1 ∧
        (∀ t : ℝ, t ≤ 0 →
          ∃ C : MetricConvergenceData (I := I3) (Phi.atTime (L := L) t),
            ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
              (I := I3) (Phi.atTime (L := L) t) k) ∧
        (∀ a b : ℝ, a ≤ b → b ≤ 0 → ∀ K : Set L.M, IsCompact K →
          ∀ order : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in _root_.Filter.atTop,
            Nonempty (MetricComparisonOn
              (fun t => L.S.base.metric t) (fun t => (X.term (phi i)).S.base.metric t)
              (Phi.map i) K (_root_.Set.Icc a b) order ε)) ∧
        IsAncientKappaSolution (I := I3) κ L := by
  obtain ⟨L, phi, hphi, Phi, hKL, hbaseL, hconv, hcmp, himp⟩ :=
    exists_fixed_kappa_compactness_of_rankOne X hD hsource hbase
  refine ⟨L, phi, hphi, Phi, hKL, hbaseL, hconv, hcmp, himp ?_⟩
  intro P
  exact hKL.rankOne_terminal_scalar_bddAbove finrank_euclideanSpace_fin P

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_fixed_kappa_compactness then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_fixed_kappa_compactness"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_fixed_kappa_compactness ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_fixed_kappa_compactness

end FixedKappa

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
