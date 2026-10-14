import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCurvatureTrichotomy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimTerminalFlat
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimPositiveTerminalBounded

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Topology
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance threeBoundedTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedTopology ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedTopology
local instance threeBoundedCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedCharted then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedCharted"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedCharted ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedCharted
local instance threeBoundedSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedSmooth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedSmooth
local instance threeBoundedT2 : T2Space F.M := F.t2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedT2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedT2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedT2 ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedT2
local instance threeBoundedSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.threeBoundedSigma

attribute [local instance] terminalTrichotomyInhabited
  terminalTrichotomyLocallyPathConnected
  terminalTrichotomySemilocallySimplyConnected


theorem KLim.three_terminal_scalar_bddAbove_of_rankOne {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hrankOne : ∀ _P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0),
      BddAbove (Set.range (F.S.scalar 0))) :
    BddAbove (Set.range (F.S.scalar 0)) := by
  rcases klim_terminal_curvature_trichotomy F hK hdim with hpos | hflat | hprod
  · exact hK.three_terminal_bddAbove_of_positive F hdim hpos
  · exact absurd hflat (hK.not_terminal_flat F hdim)
  · exact hprod.elim hrankOne

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.three_terminal_scalar_bddAbove_of_rankOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.three_terminal_scalar_bddAbove_of_rankOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.three_terminal_scalar_bddAbove_of_rankOne ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.three_terminal_scalar_bddAbove_of_rankOne


theorem KLim.scalar_bounded_of_rankOne {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hrankOne : ∀ _P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0),
      BddAbove (Set.range (F.S.scalar 0))) :
    ∃ C : ℝ, PointedFlowScalarBounded (I := I) F C := by
  obtain ⟨C, hC⟩ :=
    hK.three_terminal_scalar_bddAbove_of_rankOne F hdim hrankOne
  exact ⟨C, hK.scalarBounded_of_terminal_bound fun x => hC (Set.mem_range_self x)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.scalar_bounded_of_rankOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.scalar_bounded_of_rankOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.scalar_bounded_of_rankOne ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.scalar_bounded_of_rankOne


theorem KLim.isAncientKappaSolution_of_rankOne {kappa : ℝ}
    (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hrankOne : ∀ _P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0),
      BddAbove (Set.range (F.S.scalar 0))) :
    IsAncientKappaSolution (I := I) kappa F := by
  obtain ⟨C, hC⟩ :=
    hK.three_terminal_scalar_bddAbove_of_rankOne F hdim hrankOne
  exact hK.toIsAncientKappaSolution fun x => hC (Set.mem_range_self x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.isAncientKappaSolution_of_rankOne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.isAncientKappaSolution_of_rankOne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.isAncientKappaSolution_of_rankOne ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.KLim.isAncientKappaSolution_of_rankOne

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
