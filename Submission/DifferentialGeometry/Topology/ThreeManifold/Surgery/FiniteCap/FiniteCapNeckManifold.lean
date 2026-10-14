import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSmoothManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry.Neck
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev NeckE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.NeckE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.NeckE3 target :: scope.openDecls } }
private abbrev NeckIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.NeckIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.NeckIC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealNeckE3HAddOfNat : Fact (Module.finrank ℝ NeckE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealNeckE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealNeckE3HAddOfNat target :: scope.openDecls } }
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem contMDiff_neckAmbientMap (U : _root_.TopologicalSpace.Opens M) {g : SmoothRiemannianMetric I U}
    {x₀ : U} {δ : ℝ} {k : ℕ} (d : normalizedDatum g x₀ δ k) :
    ContMDiff NeckIC I ∞ (neckAmbientMap U d) :=
  (contMDiff_subtype_val (I := I) (U := U)).comp d.smooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_neckAmbientMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_neckAmbientMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_neckAmbientMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.contMDiff_neckAmbientMap

theorem neckAmbientMap_mfderiv (U : _root_.TopologicalSpace.Opens M) {g : SmoothRiemannianMetric I U}
    {x₀ : U} {δ : ℝ} {k : ℕ} (d : normalizedDatum g x₀ δ k) (x : bufferedCylinder δ) :
    mfderiv NeckIC I (neckAmbientMap U d) x = mfderiv NeckIC I d.map x := by
  change mfderiv NeckIC I ((Subtype.val : U → M) ∘ d.map) x = _
  rw [mfderiv_comp x
    ((contMDiff_subtype_val (I := I) (U := U) (n := ∞)).mdifferentiable (by decide) (d.map x))
    (d.smooth.mdifferentiable (by decide) x), mfderiv_subtype_val]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.neckAmbientMap_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.neckAmbientMap_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.neckAmbientMap_mfderiv ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.neckAmbientMap_mfderiv

theorem normalizedNeckFamily_isManifold {ι : Type*} [Finite ι] {precision : ι → ℝ}
    {L : ℝ} (hL : 0 < L) (U : _root_.TopologicalSpace.Opens M) (g : SmoothRiemannianMetric I U)
    (x₀ : ι → U) (order : ι → ℕ) (d : ∀ i, normalizedDatum g (x₀ i) (precision i) (order i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (neckAmbientMap U (d i))) (_root_.Set.range (neckAmbientMap U (d j))))) :
    let f := fun i => neckAmbientMap U (d i)
    let hf := fun i => isOpenEmbedding_neckAmbientMap U (d i)
    let hδ := fun i => (d i).precision_pos
    let Q := FiniteCapQuotient hL hδ f (fun i => (hf i).injective) hdisj
    let : ChartedSpace NeckE3 Q := finiteCapChartedSpace I Fact.out hL hδ f hf hdisj
    IsManifold (𝓡 3) ∞ Q := by
  dsimp only
  apply finiteCapQuotient_isManifold_of_immersion Fact.out hL (fun i => (d i).precision_pos)
    (fun i => neckAmbientMap U (d i)) (fun i => isOpenEmbedding_neckAmbientMap U (d i)) hdisj
    (fun i => contMDiff_neckAmbientMap U (d i))
  intro i x
  rw [neckAmbientMap_mfderiv]
  exact (d i).immersion x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.normalizedNeckFamily_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.normalizedNeckFamily_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.normalizedNeckFamily_isManifold ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.normalizedNeckFamily_isManifold
end DifferentialGeometry.Topology.ThreeManifold.Surgery
