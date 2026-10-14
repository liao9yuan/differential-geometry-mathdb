import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeighborhood

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace
open _root_.Submission.DifferentialGeometry.Geometry.Neck
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
private abbrev Collar (δ : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.Collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.Collar target :: scope.openDecls } }
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
variable {precision : ι → ℝ}

theorem cuttingCollar_frontier_iff (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))))
    (b : ι × Bool) (q : Collar (precision b.1)) :
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q).val ∈ frontier (cutCore f) ↔
      q.2.val = 0 := by
  constructor
  · intro hq
    have hr : cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q ∈
        range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
      rw [range_cuttingSphereAttachment hδ f hf hdisj]
      exact hq
    obtain ⟨a, ha⟩ := hr
    have hb := (cuttingSphereAttachment_mem_collar_iff hδ f (fun i => (hf i).injective) hdisj a b).mp
      ⟨q, ha.symm⟩
    rcases a with ⟨c, y⟩
    change c = b at hb
    subst c
    have hz := (cuttingCollarMap_zero hδ f (fun i => (hf i).injective) hdisj b y).trans ha
    have he := (isOpenEmbedding_cuttingCollarMap hδ f hf hdisj b).injective hz
    exact (congrArg (fun p : Collar (precision b.1) => p.2.val) he).symm
  · intro hq
    have he : q = (q.1, ⟨0, ⟨le_rfl, cuttingCollarWidth_pos (hδ b.1)⟩⟩) :=
      Prod.ext rfl (Subtype.ext hq)
    rw [he, cuttingCollarMap_zero]
    have hr : cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, q.1⟩ ∈
        range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := ⟨⟨b, q.1⟩, rfl⟩
    rw [range_cuttingSphereAttachment hδ f hf hdisj] at hr
    exact hr

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollar_frontier_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollar_frontier_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollar_frontier_iff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollar_frontier_iff

theorem cuttingCollar_interior_iff (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))))
    (b : ι × Bool) (q : Collar (precision b.1)) :
    (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q).val ∈ interior (cutCore f) ↔
      0 < q.2.val := by
  have hc := (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q).property
  constructor
  · intro hi
    have hn : q.2.val ≠ 0 := by
      intro hz
      have hfront := (cuttingCollar_frontier_iff hδ f hf hdisj b q).mpr hz
      exact hfront.2 hi
    exact lt_of_le_of_ne q.2.property.1 hn.symm
  · intro ht
    by_contra hi
    have hfront : (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q).val ∈
        frontier (cutCore f) := ⟨subset_closure hc, hi⟩
    exact (ne_of_gt ht) ((cuttingCollar_frontier_iff hδ f hf hdisj b q).mp hfront)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollar_interior_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollar_interior_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollar_interior_iff ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingCollar_interior_iff
end DifferentialGeometry.Topology.ThreeManifold.Surgery
