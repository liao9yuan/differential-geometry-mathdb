import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CompactDoubleCoreCharts
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCapMetricLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Source.CovariantLipschitz
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.WindowPullback
import Submission.DifferentialGeometry.Topology.Exhaustion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private abbrev E4 := EuclideanSpace ℝ (Fin 4)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E4
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E4 target :: scope.openDecls } }
private abbrev S3 := Metric.sphere (0 : E4) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.S3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.S3 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE4HAddOfNat : Fact (Module.finrank ℝ E4 = 3 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE4HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE4HAddOfNat target :: scope.openDecls } }

theorem compactCapCoreApproximationRadius_large (j : ℕ) :
    transitionEnd + 4 ≤ compactCapApproximationRadius (j + 2) := by
  have hm := le_max_left transitionEnd 2
  simp only [compactCapApproximationRadius, Nat.cast_add, Nat.cast_ofNat]
  linarith [show (0 : ℝ) ≤ j from Nat.cast_nonneg j]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.compactCapCoreApproximationRadius_large then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.compactCapCoreApproximationRadius_large"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.compactCapCoreApproximationRadius_large ``Submission.DifferentialGeometry.PDE.RicciFlow.compactCapCoreApproximationRadius_large

private theorem core_balls_exhaust : ExhaustsByOpen
    (fun j => Metric.ball (0 : E3) (compactCapApproximationRadius (j + 2) - 2)) where
  isOpen := fun _ => Metric.isOpen_ball
  mono_step := by
    intro j
    apply Metric.ball_subset_ball
    simp only [compactCapApproximationRadius, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    linarith
  subset := by
    intro K hK
    obtain ⟨r, hrK⟩ := hK.isBounded.subset_ball (0 : E3)
    obtain ⟨j₀, hj₀⟩ := exists_nat_gt (r - (_root_.Max.max transitionEnd 2 + 2))
    refine ⟨j₀, ?_⟩
    intro j hj
    apply hrK.trans (Metric.ball_subset_ball ?_)
    have hcast : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
    simp only [compactCapApproximationRadius, Nat.cast_add, Nat.cast_ofNat]
    linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.core_balls_exhaust
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.core_balls_exhaust target :: scope.openDecls } }

abbrev compactCorePointedModel (g : SmoothRiemannianMetric (𝓡 3) E3) :
    PointedRiemannianManifold (𝓡 3) where
  M := E3
  basepoint := 0
  metric := g

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.compactCorePointedModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.compactCorePointedModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.compactCorePointedModel ``Submission.DifferentialGeometry.PDE.RicciFlow.compactCorePointedModel

abbrev compactCorePointedFlowSequence {D : RealTimeInterval} (north : S3)
    (S : ℕ → SolutionOn (I := 𝓡 3) (M := S3) D) (hS : ∀ j, IsSolutionOn (S j)) :
    PointedFlowSeq (𝓡 3) where
  D := D
  term j := {
    M := S3
    basepoint := compactDoubleCapMap north (compactCapApproximationRadius (j + 2)) 0
    S := S j
    isSolution := hS j }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.compactCorePointedFlowSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.compactCorePointedFlowSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.compactCorePointedFlowSequence ``Submission.DifferentialGeometry.PDE.RicciFlow.compactCorePointedFlowSequence

def compactCorePointedMaps {D : RealTimeInterval}
    (g : SmoothRiemannianMetric (𝓡 3) E3) (north : S3)
    (S : ℕ → SolutionOn (I := 𝓡 3) (M := S3) D) (hS : ∀ j, IsSolutionOn (S j)) :
    PointedCGHMaps (compactCorePointedFlowSequence north S hS) (compactCorePointedModel g) id where
  partialDiffeomorph j := compactDoubleCorePartialDiffeomorph north (compactCapApproximationRadius (j + 2))
  source_exhausts := core_balls_exhaust
  base_mem := by
    intro j
    change (0 : E3) ∈ Metric.ball 0 (compactCapApproximationRadius (j + 2) - 2)
    rw [Metric.mem_ball, dist_self]
    linarith [compactCapApproximationRadius_large (j + 2), le_max_right transitionEnd 2]
  basepoint_map := fun _ => rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps ``Submission.DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps

section Sequence
variable {D : RealTimeInterval} (g : SmoothRiemannianMetric (𝓡 3) E3) (north : S3)
  (S : ℕ → SolutionOn (I := 𝓡 3) (M := S3) D) (hS : ∀ j, IsSolutionOn (S j))
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceSourceDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps (j : ℕ) : TopologicalSpace (SourceDomain (compactCorePointedMaps g north S hS) j) :=
  sourceDomTop (compactCorePointedMaps g north S hS) j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceSourceDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceSourceDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3SourceDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps (j : ℕ) : ChartedSpace E3 (SourceDomain (compactCorePointedMaps g north S hS) j) :=
  sourceDomCharted (compactCorePointedMaps g north S hS) j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3SourceDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3SourceDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceSourceDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps (j : ℕ) : T2Space (SourceDomain (compactCorePointedMaps g north S hS) j) :=
  sourceDomT2 (compactCorePointedMaps g north S hS) j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceSourceDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instT2SpaceSourceDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopSourceDomainCompactCorePointedMaps (j : ℕ) : IsManifold (𝓡 3) ∞ (SourceDomain (compactCorePointedMaps g north S hS) j) :=
  sourceDomSmooth (compactCorePointedMaps g north S hS) j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopSourceDomainCompactCorePointedMaps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopSourceDomainCompactCorePointedMaps target :: scope.openDecls } }

theorem compactCorePointedMaps_sourceSigma : SourceIsSigmaCompact (compactCorePointedMaps g north S hS) :=
  fun j => Geometry.isSigmaCompact_of_isOpen (𝓡 3)
    (PointedCGHMaps.source_open (compactCorePointedMaps g north S hS) j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_sourceSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_sourceSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_sourceSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_sourceSigma

theorem compactCorePointedMaps_targetSigma : TargetIsSigmaCompact (compactCorePointedMaps g north S hS) :=
  fun j => Geometry.isSigmaCompact_of_isOpen (𝓡 3)
    (PointedCGHMaps.target_open (compactCorePointedMaps g north S hS) j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_targetSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_targetSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_targetSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_targetSigma

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSourceDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps (j : ℕ) : SigmaCompactSpace (SourceDomain (compactCorePointedMaps g north S hS) j) :=
  sourceDomSigmaOf (compactCorePointedMaps g north S hS) j
    (compactCorePointedMaps_sourceSigma g north S hS j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSourceDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSourceDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps target :: scope.openDecls } }

theorem compactCorePointedMaps_initial
    (hzero : ∀ j, (S j).base.metric 0 =
      compactDoubleTruncationMetric north (compactCapApproximationRadius (j + 2))
        (compactCapApproximationRadius_large (j + 2)) g) (j : ℕ) :
    sourceMetric (compactCorePointedMaps g north S hS)
      (compactCorePointedMaps_sourceSigma g north S hS)
      (compactCorePointedMaps_targetSigma g north S hS) j 0 =
        sourceMetricRestriction (compactCorePointedMaps g north S hS) g j := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  let Φ := compactCorePointedMaps g north S hS
  let data := SourceDomainMetricData.ofRestrictPullback
    (Φ := Φ) (k := j) (compactCorePointedMaps_sourceSigma g north S hS j)
    (fun _ => g.restrictOpen (sourceOpen Φ j)) (fun _ => g)
  let : TopologicalSpace (SourceDomain Φ j) := data.topology
  let : ChartedSpace E3 (SourceDomain Φ j) := data.charted
  let : T2Space (SourceDomain Φ j) := data.t2
  let : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := data.smooth
  let : SigmaCompactSpace (SourceDomain Φ j) := data.sigmaCompact
  change (data.pullbackMetric 0).inner x v w = g.inner x.val v w
  dsimp only [TangentSpace] at v w ⊢
  erw [data.pullback_inner]
  have hd (u : E3) : mfderiv (𝓡 3) (𝓡 3)
      (fun y : SourceDomain Φ j => Φ.map j y.val) x u =
      mfderiv (𝓡 3) (𝓡 3)
        (compactDoubleCapMap north (compactCapApproximationRadius (j + 2))) x.val u := by
    have hh := mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3)
      (f := (Subtype.val : SourceDomain Φ j → E3))
      (g := compactDoubleCapMap north (compactCapApproximationRadius (j + 2))) x
      ((contMDiff_compactDoubleCapMap north (compactCapApproximationRadius (j + 2))).mdifferentiableAt (by simp))
      (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)) u
    have hinc : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : SourceDomain Φ j → E3) x u = u :=
      mfderiv_subtype_val_apply (I := 𝓡 3) (sourceOpen Φ j) x u
    exact hh.trans (congrArg
      (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north (compactCapApproximationRadius (j + 2))) x.val) hinc)
  simp only [hd]
  change ((S j).base.metric 0).inner
    (compactDoubleCapMap north (compactCapApproximationRadius (j + 2)) x.val)
    (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north (compactCapApproximationRadius (j + 2))) x.val v)
    (mfderiv (𝓡 3) (𝓡 3) (compactDoubleCapMap north (compactCapApproximationRadius (j + 2))) x.val w) = _
  have hslot (p : S3) (u z : TangentSpace (𝓡 3) p) :=
    congrArg (fun m : SmoothRiemannianMetric (𝓡 3) S3 => m.inner p u z) (hzero j)
  exact (hslot _ _ _).trans
    (compactDoubleCorePartialDiffeomorph_truncation_pullback north
      (compactCapApproximationRadius (j + 2)) (compactCapApproximationRadius_large (j + 2))
      g x.val x.property v w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_initial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_initial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_initial ``Submission.DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_initial

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceTargetDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps (j : ℕ) : TopologicalSpace (TargetDomain (compactCorePointedMaps g north S hS) j) :=
  targetDomTop (compactCorePointedMaps g north S hS) j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceTargetDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceTargetDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3TargetDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps (j : ℕ) : ChartedSpace E3 (TargetDomain (compactCorePointedMaps g north S hS) j) :=
  targetDomCharted (compactCorePointedMaps g north S hS) j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3TargetDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3TargetDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceTargetDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps (j : ℕ) : T2Space (TargetDomain (compactCorePointedMaps g north S hS) j) :=
  targetDomT2 (compactCorePointedMaps g north S hS) j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceTargetDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instT2SpaceTargetDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopTargetDomainCompactCorePointedMaps (j : ℕ) : IsManifold (𝓡 3) ∞ (TargetDomain (compactCorePointedMaps g north S hS) j) :=
  targetDomSmooth (compactCorePointedMaps g north S hS) j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopTargetDomainCompactCorePointedMaps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopTargetDomainCompactCorePointedMaps target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceTargetDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps (j : ℕ) : SigmaCompactSpace (TargetDomain (compactCorePointedMaps g north S hS) j) :=
  targetDomSigmaOf (compactCorePointedMaps g north S hS) j
    (compactCorePointedMaps_targetSigma g north S hS j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceTargetDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceTargetDomainEuclideanSpaceRealFinOfNatNatCompactCorePointedMaps target :: scope.openDecls } }

private theorem canonical_metric (j : ℕ) (t : ℝ) :
    sourceMetric (compactCorePointedMaps g north S hS)
      (compactCorePointedMaps_sourceSigma g north S hS)
      (compactCorePointedMaps_targetSigma g north S hS) j t =
      Diffeomorph.pullbackMetric
        (((S j).base.metric t).restrictOpen (targetOpen (compactCorePointedMaps g north S hS) j))
        (sourceTargetDiff (compactCorePointedMaps g north S hS) j) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.canonical_metric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.canonical_metric target :: scope.openDecls } }

theorem compactCorePointedMaps_reference_bounds
    (hzero : ∀ j, (S j).base.metric 0 =
      compactDoubleTruncationMetric north (compactCapApproximationRadius (j + 2))
        (compactCapApproximationRadius_large (j + 2)) g)
    (τ Λ : ℝ) (C L : ℕ → ℝ) (hC : ∀ N, 0 ≤ C N) (hL : ∀ N, 0 ≤ L N)
    (he : ∀ j, ∀ t ∈ _root_.Set.Icc 0 τ,
      MetricUniformEquivalentOn _root_.Set.univ ((S j).base.metric 0) ((S j).base.metric t) Λ)
    (hc : ∀ j N, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ x : S3,
      metricCovDerivNorm N ((S j).base.metric t) ((S j).base.metric 0) x ≤ C N)
    (hl : ∀ j N, ∀ s ∈ _root_.Set.Icc 0 τ, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ x : S3,
      metricDerivNorm N ((S j).base.metric s) ((S j).base.metric t)
        ((S j).base.metric 0) x ≤ L N * |s - t|) :
    (∀ j, ∀ t ∈ _root_.Set.Icc 0 τ,
      MetricUniformEquivalentOn _root_.Set.univ (sourceMetricRestriction (compactCorePointedMaps g north S hS) g j)
        (sourceMetric (compactCorePointedMaps g north S hS)
          (compactCorePointedMaps_sourceSigma g north S hS)
          (compactCorePointedMaps_targetSigma g north S hS) j t) Λ) ∧
    SourceMetricCovariantLipschitzBounds (compactCorePointedMaps g north S hS) g
      (compactCorePointedMaps_sourceSigma g north S hS)
      (compactCorePointedMaps_targetSigma g north S hS) 0 τ := by
  let Φ := compactCorePointedMaps g north S hS
  let hsrc := compactCorePointedMaps_sourceSigma g north S hS
  let htgt := compactCorePointedMaps_targetSigma g north S hS
  have hi := compactCorePointedMaps_initial g north S hS hzero
  have hcov (N j : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ) (y : SourceDomain Φ j) :
      metricCovDerivNorm N (sourceMetric Φ hsrc htgt j t) (sourceMetricRestriction Φ g j) y ≤ C N := by
    rw [← hi j, canonical_metric, canonical_metric,
      metricCovDerivNorm_pullback, covNorm_restrictOpen]
    exact hc j N t ht _
  have hlip (N j : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc 0 τ)
      (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ) (y : SourceDomain Φ j) :
      metricDerivNorm N (sourceMetric Φ hsrc htgt j s) (sourceMetric Φ hsrc htgt j t)
        (sourceMetricRestriction Φ g j) y ≤ L N * |s - t| := by
    rw [← hi j, canonical_metric, canonical_metric, canonical_metric,
      metricDerivNorm_pullback, metricDerivNorm_restrictOpen]
    exact hl j N s hs t ht _
  constructor
  · intro j t ht
    have hr := metricUniformEquivalentOn_restrictOpen _root_.Set.univ
      ((S j).base.metric 0) ((S j).base.metric t) Λ (he j t ht)
      (targetOpen Φ j) (V := _root_.Set.univ) (fun _ _ => _root_.Set.mem_univ _)
    have hp := metricUniformEquivalentOn_pullback _root_.Set.univ _ _ Λ hr
      (sourceTargetDiff Φ j) (V := _root_.Set.univ) (fun _ _ => _root_.Set.mem_univ _)
    rw [← canonical_metric, ← canonical_metric, hi j] at hp
    exact hp
  · constructor
    · intro N
      exact ⟨C N, hC N, fun j t ht y => hcov N j t ht y⟩
    · intro N
      refine ⟨∑ a ∈ Finset.range (N + 1), L a, Finset.sum_nonneg (fun a _ => hL a), ?_⟩
      intro j s t hs ht a ha y
      refine (hlip a j s hs t ht y).trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
      exact Finset.single_le_sum (s := Finset.range (N + 1)) (a := a) (f := L)
        (fun b _ => hL b) (Finset.mem_range.mpr (by omega))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_reference_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_reference_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_reference_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.compactCorePointedMaps_reference_bounds

end Sequence
end DifferentialGeometry.PDE.RicciFlow
