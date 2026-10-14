import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.IteratedCovariantDerivativeFields

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

universe u uE uH

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

def TerminalJetContinuous (F : PointedFlowData.{u, uE, uH} (I := I) D) (b : ℝ) : Prop :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I 1 F.M :=
    IsManifold.of_le (I := I) (M := F.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  ∀ (k : ℕ) (x : F.M) (v : Fin (4 + k) → TangentSpace I x),
    ContinuousWithinAt (fun t : ℝ => nablaKRm04Field (I := I) F.S t k x v) (Set.Iic b) b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.TerminalJetContinuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.TerminalJetContinuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.TerminalJetContinuous ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.TerminalJetContinuous

structure IsAncientKappaSolutionTerminal (kappa : ℝ)
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : Prop where
  toAncient : IsAncientKappaSolution (I := I) kappa F
  terminalJets : TerminalJetContinuous (I := I) F 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolutionTerminal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolutionTerminal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolutionTerminal ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolutionTerminal

theorem IsAncientKappaSolutionTerminal.ancient {kappa : ℝ}
    {F : PointedFlowData.{u, uE, uH} (I := I) D}
    (h : IsAncientKappaSolutionTerminal (I := I) kappa F) :
    IsAncientKappaSolution (I := I) kappa F :=
  h.toAncient

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolutionTerminal
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolutionTerminal.ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolutionTerminal.ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolutionTerminal.ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolutionTerminal.ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
