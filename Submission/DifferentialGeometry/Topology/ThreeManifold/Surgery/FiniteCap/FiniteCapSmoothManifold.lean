import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapForwardTransition
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapReverseTransition
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapHomogeneousTransitions

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
private abbrev SmoothE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.SmoothE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.SmoothE3 target :: scope.openDecls } }
private abbrev SmoothIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.SmoothIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.SmoothIC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealSmoothE3HAddOfNat : Fact (Module.finrank ℝ SmoothE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealSmoothE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealSmoothE3HAddOfNat target :: scope.openDecls } }
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
variable [IsManifold I ∞ M] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "SmoothQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

theorem finiteCapQuotient_isManifold
    (hs : ∀ i, IsLocalDiffeomorph SmoothIC I ∞ (f i)) :
    let : ChartedSpace SmoothE3 SmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsManifold (𝓡 3) ∞ SmoothQ := by
  let : ChartedSpace SmoothE3 SmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  apply isManifold_of_contDiffOn (𝓡 3) ∞ SmoothQ
  intro e e' he he'
  change e ∈ _root_.Set.range (finiteCoreThreeChart I hdim hL hδ f hf hdisj) ∪ _root_.Set.range (finiteCapOpenChart hL hδ f hf hdisj) at he
  change e' ∈ _root_.Set.range (finiteCoreThreeChart I hdim hL hδ f hf hdisj) ∪ _root_.Set.range (finiteCapOpenChart hL hδ f hf hdisj) at he'
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, _root_.Function.comp_id, _root_.Function.id_comp, _root_.Set.preimage_id, _root_.Set.range_id, _root_.Set.inter_univ]
  rcases he with ⟨p, rfl⟩ | ⟨b, rfl⟩
  · rcases he' with ⟨q, rfl⟩ | ⟨c, rfl⟩
    · exact contDiffOn_finiteCoreThree_transition hdim hL hδ f hf hdisj p q
    · exact contDiffOn_coreThree_to_finiteCap hdim hL hδ f hf hdisj hs c p
  · rcases he' with ⟨q, rfl⟩ | ⟨c, rfl⟩
    · exact contDiffOn_finiteCap_to_coreThree hdim hL hδ f hf hdisj (fun i => (hs i).contMDiff) b q
    · exact contDiffOn_finiteCap_transition hL hδ f hf hdisj b c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_isManifold ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_isManifold

omit [IsManifold I ∞ M] in
theorem finiteCapQuotient_boundary_eq_empty :
    let : ChartedSpace SmoothE3 SmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    (𝓡 3).boundary SmoothQ = ∅ := by
  let : ChartedSpace SmoothE3 SmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact ModelWithCorners.Boundaryless.boundary_eq_empty

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_boundary_eq_empty then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_boundary_eq_empty"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_boundary_eq_empty ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_boundary_eq_empty

theorem finiteCapQuotient_isManifold_of_immersion
    (hs : ∀ i, ContMDiff SmoothIC I ∞ (f i))
    (hi : ∀ i x, _root_.Function.Injective (mfderiv SmoothIC I (f i) x)) :
    let : ChartedSpace SmoothE3 SmoothQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    IsManifold (𝓡 3) ∞ SmoothQ :=
  finiteCapQuotient_isManifold hdim hL hδ f hf hdisj (fun i =>
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv (f i) (hs i) (hi i)
      (by rw [hdim]; simp))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_isManifold_of_immersion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_isManifold_of_immersion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_isManifold_of_immersion ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_isManifold_of_immersion
end DifferentialGeometry.Topology.ThreeManifold.Surgery
