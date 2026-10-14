import Submission.DifferentialGeometry.Geometry.Curvature.RicciNonnegativeConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosedReferenceBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCurvatureOperator
import Submission.DifferentialGeometry.Geometry.Curvature.RicciRestriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Equation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.BigOperators _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }

theorem PartialStandardSolution.ricciTensor_nonnegative
    (S : PartialStandardSolution) (t : ℝ) (ht : t ∈ S.domain)
    (q : E3) (v : TangentSpace (𝓡 3) q) :
    0 ≤ ricciTensor (S.metric t) q v v :=
  ricciTensor_nonnegative_of_curvatureOperator_nonnegative (S.metric t) q
    (S.curvatureOperator_nonnegative t ht q) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.ricciTensor_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.ricciTensor_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.ricciTensor_nonnegative ``Submission.DifferentialGeometry.PDE.RicciFlow.PartialStandardSolution.ricciTensor_nonnegative

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

private theorem standard_closed_source_ricci_nonnegative
    (j : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc 0 τ)
    (q : SourceDomain Φ j) (v : TangentSpace (𝓡 3) q) :
    0 ≤ ricciTensor (sourceMetric Φ hsrc htgt j t) q v v := by
  change 0 ≤ ricciTensor
    (Diffeomorph.pullbackMetric
      (((S (φ j)).val.metric t).restrictOpen (targetOpen Φ j))
      (sourceTargetDiff Φ j)) q v v
  rw [DifferentialGeometry.CheegerGromovCompactness.ricciTensor_pullback,
    DifferentialGeometry.Geometry.Curvature.ricciTensor_restrictOpen]
  apply PartialStandardSolution.ricciTensor_nonnegative
  exact (Icc_subset_lifetimeInterval_iff (S (φ j)).val.lifetime
    (S (φ j)).val.lifetime_pos τ hτ.le).mpr
      (hlt.trans_le (uniformStandardLifetime_le_lifetime (S (φ j)))) ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_closed_source_ricci_nonnegative
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.standard_closed_source_ricci_nonnegative target :: scope.openDecls } }

theorem standard_closed_limit_ricci_nonnegative
    (bf : BumpFamily Φ) (co : FlowMetricConvergenceData Φ P.metric bf hsrc htgt 0 τ) :
    ∀ t ∈ _root_.Set.Icc 0 τ, ∀ (q : P.M) (v : TangentSpace (𝓡 3) q),
      0 ≤ ricciTensor (co.gInf t) q v v := by
  intro t ht q v
  apply ricciTensor_nonnegative_of_local_metric_jet_convergence
    (fun k => gSeqExt Φ P.metric bf hsrc htgt (co.φ k) t) (co.gInf t) P.metric q v
  · intro ε hε
    obtain ⟨kc, hkc⟩ := co.convergencePt {q} isCompact_singleton 2 ε hε
    exact ⟨kc, fun k hk a ha => hkc k hk t ht a ha q (_root_.Set.mem_singleton q)⟩
  · obtain ⟨kg, hkg⟩ := bf.grow_cover {q} isCompact_singleton
    refine eventually_atTop.2 ⟨kg, ?_⟩
    intro k hk
    have hq : q ∈ bf.grow (co.φ k) :=
      hkg (co.φ k) (hk.trans (co.strictMono.id_le k)) (_root_.Set.mem_singleton q)
    rw [gSeqExt_ricci Φ P.metric bf hsrc htgt (co.φ k) t q hq v v]
    exact standard_closed_source_ricci_nonnegative Φ hsrc htgt (co.φ k) t ht
      ⟨q, bf.grow_subset (co.φ k) hq⟩ v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.standard_closed_limit_ricci_nonnegative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.standard_closed_limit_ricci_nonnegative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.standard_closed_limit_ricci_nonnegative ``Submission.DifferentialGeometry.PDE.RicciFlow.standard_closed_limit_ricci_nonnegative

end Maps
end DifferentialGeometry.PDE.RicciFlow

end
