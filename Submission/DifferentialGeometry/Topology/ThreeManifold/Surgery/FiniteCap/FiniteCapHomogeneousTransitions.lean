import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.ModelThreeSmooth

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev HomogeneousE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.HomogeneousE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.HomogeneousE3 target :: scope.openDecls } }
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
variable [IsManifold I ∞ M] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))

theorem contDiffOn_finiteCoreThree_transition (p q : coreInteriorDomain f) :
    ContDiffOn ℝ ∞
      ((finiteCoreThreeChart I hdim hL hδ f hf hdisj p).symm.trans
        (finiteCoreThreeChart I hdim hL hδ f hf hdisj q))
      ((finiteCoreThreeChart I hdim hL hδ f hf hdisj p).symm.trans
        (finiteCoreThreeChart I hdim hL hδ f hf hdisj q)).source := by
  let c := finiteCoreThreeChart I hdim hL hδ f hf hdisj p
  let d := finiteCoreThreeChart I hdim hL hδ f hf hdisj q
  let A := modelThreeDiffeomorph I hdim
  let old := finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj
  let r : HomogeneousE3 → coreInteriorDomain f := fun z => (chartAt H p).symm (A.symm z)
  intro x hx
  change x ∈ c.target ∧ c.symm x ∈ d.source at hx
  have hp : A.symm x ∈ (chartAt H p).target := hx.1
  have hrq : r x ∈ (chartAt H q).source := by
    have him : old (r x) ∈ old '' (chartAt H q).source := hx.2
    obtain ⟨q', hq', heq⟩ := him
    exact (isOpenEmbedding_finiteCoreInteriorMap hL hδ f hf hdisj).injective heq ▸ hq'
  have hr : ContMDiffAt (𝓡 3) I ∞ r x :=
    ((contMDiffOn_chart_symm (I := I) (n := ∞)).contMDiffAt
      ((chartAt H p).open_target.mem_nhds hp)).comp x A.symm.contMDiff.contMDiffAt
  have hq : ContMDiffAt I I ∞ (chartAt H q) (r x) :=
    (contMDiffOn_chart (I := I) (n := ∞)).contMDiffAt ((chartAt H q).open_source.mem_nhds hrq)
  have he : (fun z => d (c.symm z)) = (fun z => A (chartAt H q (r z))) := by
    funext z
    change d (old (r z)) = _
    rw [finiteCoreThreeChart_apply]
    rfl
  have ht : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun z => d (c.symm z)) x := by
    rw [he]
    exact A.contMDiff.contMDiffAt.comp x (hq.comp x hr)
  exact ht.contDiffAt.contDiffWithinAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.contDiffOn_finiteCoreThree_transition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.contDiffOn_finiteCoreThree_transition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.contDiffOn_finiteCoreThree_transition ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.contDiffOn_finiteCoreThree_transition

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [I.Boundaryless] [ChartedSpace H M] [IsManifold I ∞ M] in
theorem contDiffOn_finiteCap_transition (b c : ι × Bool) :
    ContDiffOn ℝ ∞
      ((finiteCapOpenChart hL hδ f hf hdisj b).symm.trans (finiteCapOpenChart hL hδ f hf hdisj c))
      ((finiteCapOpenChart hL hδ f hf hdisj b).symm.trans (finiteCapOpenChart hL hδ f hf hdisj c)).source := by
  by_cases hbc : b = c
  · subst c
    apply contDiffOn_id.congr
    intro x hx
    exact (finiteCapOpenChart hL hδ f hf hdisj b).right_inv hx.1
  · intro x hx
    have hb := (finiteCapOpenChart hL hδ f hf hdisj b).map_target hx.1
    exact (disjoint_left.mp (pairwise_disjoint_finiteCapOpenChart_sources hL hδ f hf hdisj hbc) hb hx.2).elim

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.contDiffOn_finiteCap_transition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.contDiffOn_finiteCap_transition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.contDiffOn_finiteCap_transition ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.contDiffOn_finiteCap_transition
end DifferentialGeometry.Topology.ThreeManifold.Surgery
