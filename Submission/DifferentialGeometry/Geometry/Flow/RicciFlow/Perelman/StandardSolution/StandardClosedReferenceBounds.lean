import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.UniformLifetime
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Source.CovariantLipschitz
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.WindowPullback

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
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

private theorem standard_closed_isSolutionOn (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime) (S : StandardSolution) :
    IsSolutionOn
      (S.val.toSolutionOn.timeRestrict (RealTimeInterval.closed 0 τ hτ.le)) := by
  have hlife : ENNReal.ofReal τ < S.val.lifetime :=
    hlt.trans_le (uniformStandardLifetime_le_lifetime S)
  apply isSolutionOn_timeRestrict S.val.isSolutionOn
  · exact (Icc_subset_lifetimeInterval_iff S.val.lifetime S.val.lifetime_pos τ hτ.le).mpr hlife
  · intro t ht
    change t ∈ _root_.Set.Ioo 0 τ at ht
    exact (mem_lifetimeInterval_regular S.val.lifetime S.val.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2.le).trans_lt hlife⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_closed_isSolutionOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.standard_closed_isSolutionOn target :: scope.openDecls } }

abbrev standardClosedPointedFlowSequence (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3) : PointedFlowSeq (𝓡 3) where
  D := RealTimeInterval.closed 0 τ hτ.le
  term i := {
    M := E3
    basepoint := x i
    S := (S i).val.toSolutionOn.timeRestrict (RealTimeInterval.closed 0 τ hτ.le)
    isSolution := standard_closed_isSolutionOn τ hτ hlt (S i) }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standardClosedPointedFlowSequence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standardClosedPointedFlowSequence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standardClosedPointedFlowSequence ``Submission.DifferentialGeometry.PDE.RicciFlow.standardClosedPointedFlowSequence

@[simp] theorem standardClosedPointedFlowSequence_metric (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3) (i : ℕ) (t : ℝ) :
    ((standardClosedPointedFlowSequence τ hτ hlt S x).term i).S.base.metric t =
      (S i).val.metric t := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standardClosedPointedFlowSequence_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standardClosedPointedFlowSequence_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standardClosedPointedFlowSequence_metric ``Submission.DifferentialGeometry.PDE.RicciFlow.standardClosedPointedFlowSequence_metric

@[simp] theorem standardClosedPointedFlowSequence_basepoint (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime)
    (S : ℕ → StandardSolution) (x : ℕ → E3) (i : ℕ) :
    ((standardClosedPointedFlowSequence τ hτ hlt S x).term i).basepoint = x i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standardClosedPointedFlowSequence_basepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standardClosedPointedFlowSequence_basepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standardClosedPointedFlowSequence_basepoint ``Submission.DifferentialGeometry.PDE.RicciFlow.standardClosedPointedFlowSequence_basepoint

section Maps

variable {τ : ℝ} {hτ : 0 < τ} {hlt : ENNReal.ofReal τ < uniformStandardLifetime}
  {S : ℕ → StandardSolution} {x : ℕ → E3}
  {P : PointedRiemannianManifold (𝓡 3)} {φ : ℕ → ℕ}
  (Φ : PointedCGHMaps (standardClosedPointedFlowSequence τ hτ hlt S x) P φ)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNat : TopologicalSpace P.M := P.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceMEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNat : ChartedSpace E3 P.M := P.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3MEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNat : T2Space P.M := P.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instT2SpaceMEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopM : IsManifold (𝓡 3) ∞ P.M := P.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNat : SigmaCompactSpace P.M := P.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceMEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }

theorem standardClosedPointedMaps_sourceSigma : SourceIsSigmaCompact Φ :=
  fun j => Geometry.isSigmaCompact_of_isOpen (𝓡 3) (Φ.source_open j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standardClosedPointedMaps_sourceSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standardClosedPointedMaps_sourceSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standardClosedPointedMaps_sourceSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.standardClosedPointedMaps_sourceSigma

theorem standardClosedPointedMaps_targetSigma : TargetIsSigmaCompact Φ :=
  fun j => Geometry.isSigmaCompact_of_isOpen (𝓡 3) (Φ.target_open j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standardClosedPointedMaps_targetSigma then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standardClosedPointedMaps_targetSigma"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standardClosedPointedMaps_targetSigma ``Submission.DifferentialGeometry.PDE.RicciFlow.standardClosedPointedMaps_targetSigma

variable (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceSourceDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceSourceDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceSourceDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3SourceDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : ChartedSpace E3 (SourceDomain Φ j) := sourceDomCharted Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3SourceDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3SourceDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceSourceDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : T2Space (SourceDomain Φ j) := sourceDomT2 Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceSourceDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instT2SpaceSourceDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopSourceDomain (j : ℕ) : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopSourceDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopSourceDomain target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSourceDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : SigmaCompactSpace (SourceDomain Φ j) :=
  sourceDomSigmaOf Φ j (standardClosedPointedMaps_sourceSigma Φ j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSourceDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceSourceDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceTargetDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : TopologicalSpace (TargetDomain Φ j) := targetDomTop Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceTargetDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instTopologicalSpaceTargetDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3TargetDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : ChartedSpace E3 (TargetDomain Φ j) := targetDomCharted Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3TargetDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instChartedSpaceE3TargetDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceTargetDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : T2Space (TargetDomain Φ j) := targetDomT2 Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instT2SpaceTargetDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instT2SpaceTargetDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopTargetDomain (j : ℕ) : IsManifold (𝓡 3) ∞ (TargetDomain Φ j) := targetDomSmooth Φ j

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopTargetDomain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instIsManifoldRealEuclideanSpaceFinOfNatNatModelWithCornersSelfSomeENatTopTargetDomain target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceTargetDomainEuclideanSpaceRealFinOfNatNat (j : ℕ) : SigmaCompactSpace (TargetDomain Φ j) :=
  targetDomSigmaOf Φ j (standardClosedPointedMaps_targetSigma Φ j)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceTargetDomainEuclideanSpaceRealFinOfNatNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instSigmaCompactSpaceTargetDomainEuclideanSpaceRealFinOfNatNat target :: scope.openDecls } }

private theorem standard_closed_canonical_metric (j : ℕ) (t : ℝ) :
    sourceMetric Φ hsrc htgt j t =
      Diffeomorph.pullbackMetric
        (((S (φ j)).val.metric t).restrictOpen (targetOpen Φ j))
        (sourceTargetDiff Φ j) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_closed_canonical_metric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.standard_closed_canonical_metric target :: scope.openDecls } }

private theorem standard_closed_transport_bounds
    (hinit : ∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ P.metric j)
    (Λ : ℝ) (C L : ℕ → ℝ) (hC : ∀ N, 0 ≤ C N) (hL : ∀ N, 0 ≤ L N)
    (he : ∀ j, ∀ t ∈ _root_.Set.Icc 0 τ,
      MetricUniformEquivalentOn _root_.Set.univ ((S (φ j)).val.metric 0)
        ((S (φ j)).val.metric t) Λ)
    (hc : ∀ j N, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ z : E3,
      metricCovDerivNorm N ((S (φ j)).val.metric t)
        ((S (φ j)).val.metric 0) z ≤ C N)
    (hl : ∀ j N, ∀ s ∈ _root_.Set.Icc 0 τ, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ z : E3,
      metricDerivNorm N ((S (φ j)).val.metric s) ((S (φ j)).val.metric t)
        ((S (φ j)).val.metric 0) z ≤ L N * |s - t|) :
    (∀ j,
      (∀ t ∈ _root_.Set.Icc 0 τ,
        MetricUniformEquivalentOn _root_.Set.univ (sourceMetricRestriction Φ P.metric j)
          (sourceMetric Φ hsrc htgt j t) Λ) ∧
      (∀ N, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ y : SourceDomain Φ j,
        metricCovDerivNorm N (sourceMetric Φ hsrc htgt j t)
          (sourceMetricRestriction Φ P.metric j) y ≤ C N) ∧
      (∀ N, ∀ s ∈ _root_.Set.Icc 0 τ, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ y : SourceDomain Φ j,
        metricDerivNorm N (sourceMetric Φ hsrc htgt j s) (sourceMetric Φ hsrc htgt j t)
          (sourceMetricRestriction Φ P.metric j) y ≤ L N * |s - t|)) ∧
      SourceMetricCovariantLipschitzBounds Φ P.metric hsrc htgt 0 τ := by
  have hcov (N j : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ) (y : SourceDomain Φ j) :
      metricCovDerivNorm N (sourceMetric Φ hsrc htgt j t) (sourceMetricRestriction Φ P.metric j) y ≤ C N := by
    rw [← hinit j, standard_closed_canonical_metric, standard_closed_canonical_metric,
      metricCovDerivNorm_pullback, covNorm_restrictOpen]
    exact hc j N t ht _
  have hlip (N j : ℕ) (s : ℝ) (hs : s ∈ _root_.Set.Icc 0 τ)
      (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ) (y : SourceDomain Φ j) :
      metricDerivNorm N (sourceMetric Φ hsrc htgt j s) (sourceMetric Φ hsrc htgt j t)
        (sourceMetricRestriction Φ P.metric j) y ≤ L N * |s - t| := by
    rw [← hinit j, standard_closed_canonical_metric, standard_closed_canonical_metric,
      standard_closed_canonical_metric, metricDerivNorm_pullback, metricDerivNorm_restrictOpen]
    exact hl j N s hs t ht _
  constructor
  · intro j
    refine ⟨?_, fun N t ht y => hcov N j t ht y, fun N s hs t ht y => hlip N j s hs t ht y⟩
    intro t ht
    have hr := metricUniformEquivalentOn_restrictOpen _root_.Set.univ
      ((S (φ j)).val.metric 0) ((S (φ j)).val.metric t) Λ (he j t ht)
      (targetOpen Φ j) (V := _root_.Set.univ) (fun _ _ => _root_.Set.mem_univ _)
    have hp := metricUniformEquivalentOn_pullback _root_.Set.univ _ _ Λ hr
      (sourceTargetDiff Φ j) (V := _root_.Set.univ) (fun _ _ => _root_.Set.mem_univ _)
    rw [← standard_closed_canonical_metric Φ hsrc htgt,
      ← standard_closed_canonical_metric Φ hsrc htgt, hinit j] at hp
    exact hp
  · constructor
    · intro N
      exact ⟨C N, hC N, fun j t ht y => hcov N j t ht y⟩
    · intro N
      refine ⟨∑ a ∈ Finset.range (N + 1), L a,
        Finset.sum_nonneg (fun a _ => hL a), ?_⟩
      intro j s t hs ht a ha y
      refine (hlip a j s hs t ht y).trans
        (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
      exact Finset.single_le_sum (s := Finset.range (N + 1)) (a := a) (f := L)
        (fun b _ => hL b) (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_closed_transport_bounds
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.standard_closed_transport_bounds target :: scope.openDecls } }

end Maps

theorem standard_closed_reference_bounds (τ : ℝ) (hτ : 0 < τ)
    (hlt : ENNReal.ofReal τ < uniformStandardLifetime) :
    ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ (S : ℕ → StandardSolution) (x : ℕ → E3)
        (P : PointedRiemannianManifold (𝓡 3)) (φ : ℕ → ℕ)
        (Φ : PointedCGHMaps (standardClosedPointedFlowSequence τ hτ hlt S x) P φ)
        (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ),
        (∀ j, sourceMetric Φ hsrc htgt j 0 = sourceMetricRestriction Φ P.metric j) →
        letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace E3 P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold (𝓡 3) ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
        (∀ j,
          letI : TopologicalSpace (SourceDomain Φ j) := sourceDomTop Φ j
          letI : ChartedSpace E3 (SourceDomain Φ j) := sourceDomCharted Φ j
          letI : T2Space (SourceDomain Φ j) := sourceDomT2 Φ j
          letI : IsManifold (𝓡 3) ∞ (SourceDomain Φ j) := sourceDomSmooth Φ j
          letI : SigmaCompactSpace (SourceDomain Φ j) := sourceDomSigmaOf Φ j (hsrc j)
          (∀ t ∈ _root_.Set.Icc 0 τ,
            MetricUniformEquivalentOn _root_.Set.univ (sourceMetricRestriction Φ P.metric j)
              (sourceMetric Φ hsrc htgt j t) Λ) ∧
          (∀ N, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ y : SourceDomain Φ j,
            metricCovDerivNorm N (sourceMetric Φ hsrc htgt j t)
              (sourceMetricRestriction Φ P.metric j) y ≤ C N) ∧
          (∀ N, ∀ s ∈ _root_.Set.Icc 0 τ, ∀ t ∈ _root_.Set.Icc 0 τ, ∀ y : SourceDomain Φ j,
            metricDerivNorm N (sourceMetric Φ hsrc htgt j s) (sourceMetric Φ hsrc htgt j t)
              (sourceMetricRestriction Φ P.metric j) y ≤ L N * |s - t|)) ∧
          SourceMetricCovariantLipschitzBounds Φ P.metric hsrc htgt 0 τ := by
  obtain ⟨hlife, K, hK, hRm⟩ := uniformStandardLifetime_slab τ hτ.le hlt
  obtain ⟨Λ, hΛ, C, L, hC, hL, hb⟩ :=
    standard_metric_bounds_on_shorter_windows τ K hτ.le hK
  refine ⟨Λ, hΛ, C, L, hC, hL, ?_⟩
  intro S x P φ Φ hsrc htgt hinit
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace E3 P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold (𝓡 3) ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  have hactual (j : ℕ) :=
    hb (S (φ j)).val τ hτ.le le_rfl (hlife (S (φ j))) (hRm (S (φ j)))
  apply standard_closed_transport_bounds Φ hsrc htgt hinit Λ C L hC hL
  · intro j t ht
    rw [(S (φ j)).val.initial]
    exact (hactual j).1 t ht
  · intro j N t ht z
    rw [(S (φ j)).val.initial]
    exact (hactual j).2.1 N t ht z
  · intro j N s hs t ht z
    rw [(S (φ j)).val.initial]
    exact (hactual j).2.2 N s hs t ht z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_closed_reference_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_closed_reference_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_closed_reference_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_closed_reference_bounds

end DifferentialGeometry.PDE.RicciFlow
