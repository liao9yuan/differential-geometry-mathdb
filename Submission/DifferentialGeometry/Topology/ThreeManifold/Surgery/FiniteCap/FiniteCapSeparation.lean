import Submission.DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionSeparation
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapQuotient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment _root_.Submission.DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
private abbrev S2 := Metric.sphere (0 : E3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.S2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.S2 target :: scope.openDecls } }

theorem continuous_indexedCapBoundary {ι : Type*} {L : ℝ} (hL : 0 < L) :
    Continuous (indexedCapBoundary (ι := ι) hL) := by
  apply continuous_sigma
  intro b
  change Continuous (fun y : S2 => (⟨b, radialCapBoundary hL y⟩ : IndexedCaps ι L))
  have hr : Continuous (radialCapBoundary hL) :=
    (show Continuous (fun y : S2 => L • y.val) from
      (continuous_const : Continuous (fun _ : S2 => L)).fun_smul
        (continuous_subtype_val : Continuous (fun y : S2 => y.val))).subtype_mk _
  exact continuous_sigmaMk.comp hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.continuous_indexedCapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.continuous_indexedCapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.continuous_indexedCapBoundary ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.continuous_indexedCapBoundary

theorem isClosedEmbedding_indexedCapBoundary {ι : Type*} [Finite ι] {L : ℝ} (hL : 0 < L) :
    _root_.Topology.IsClosedEmbedding (indexedCapBoundary (ι := ι) hL) :=
  (continuous_indexedCapBoundary hL).isClosedEmbedding (injective_indexedCapBoundary hL)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_indexedCapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_indexedCapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_indexedCapBoundary ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_indexedCapBoundary

variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
variable {precision : ι → ℝ} {L : ℝ}

theorem isClosedMap_finiteCapProjection (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    IsClosedMap (adjunctionMk (indexedCapBoundary hL)
      (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj)) := by
  have ha := isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj
  exact isClosedMap_adjunctionMk _ _ (injective_indexedCapBoundary hL) ha.injective
    (continuous_indexedCapBoundary hL) ha.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedMap_finiteCapProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedMap_finiteCapProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedMap_finiteCapProjection ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedMap_finiteCapProjection

theorem finiteCapQuotient_t2Space (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    T2Space (FiniteCapQuotient hL hδ f (fun i => (hf i).injective) hdisj) := by
  have ha := isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj
  exact adjunction_t2Space _ _ (injective_indexedCapBoundary hL) ha.injective
    (continuous_indexedCapBoundary hL) ha.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_t2Space then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_t2Space"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_t2Space ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_t2Space

theorem isClosedEmbedding_finiteCapInclusion (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    _root_.Topology.IsClosedEmbedding (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj) := by
  have ha := isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj
  exact isClosedEmbedding_adjunctionCell _ _ (injective_indexedCapBoundary hL) ha.injective
    (continuous_indexedCapBoundary hL) ha.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_finiteCapInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_finiteCapInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_finiteCapInclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_finiteCapInclusion

theorem isClosedEmbedding_finiteCoreInclusion (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    _root_.Topology.IsClosedEmbedding (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) := by
  have ha := isClosedEmbedding_cuttingSphereAttachment hδ f hf hdisj
  exact isClosedEmbedding_adjunctionLower _ _ (injective_indexedCapBoundary hL) ha.injective
    (continuous_indexedCapBoundary hL) ha.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_finiteCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_finiteCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_finiteCoreInclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isClosedEmbedding_finiteCoreInclusion
end DifferentialGeometry.Topology.ThreeManifold.Surgery
