import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapChart
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

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
private abbrev Cap (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.Cap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.Cap target :: scope.openDecls } }
private abbrev Collar (δ : ℝ) := S2 × _root_.Set.Ico (0 : ℝ) (cuttingCollarWidth δ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.Collar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.Collar target :: scope.openDecls } }
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (b : ι × Bool)
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "N" => finiteCapNeighborhood hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj b

private def radialCoordinate (p : N) : E3 := (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b p).val

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.radialCoordinate
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.radialCoordinate target :: scope.openDecls } }
private theorem radialCoordinate_openEmbedding : _root_.Topology.IsOpenEmbedding
    (radialCoordinate hL hδ f hf hdisj b) := by
  have ho : IsOpen {x : E3 | ‖x‖ < L + cuttingCollarWidth (precision b.1)} :=
    isOpen_lt continuous_norm continuous_const
  exact ho.isOpenEmbedding_subtypeVal.comp
    (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b).isOpenEmbedding

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.radialCoordinate_openEmbedding
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.radialCoordinate_openEmbedding target :: scope.openDecls } }
omit [Finite ι] [T2Space M] in
private theorem neighborhood_nonempty : Nonempty N :=
  ⟨⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, ⟨0, by simp [hL.le]⟩⟩,
    Or.inl ⟨⟨0, by simp [hL.le]⟩, rfl⟩⟩⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.neighborhood_nonempty
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.neighborhood_nonempty target :: scope.openDecls } }

def finiteCapOpenChart : OpenPartialHomeomorph Q E3 := by
  let : Nonempty N := neighborhood_nonempty hL hδ f hf hdisj b
  let e := (radialCoordinate_openEmbedding hL hδ f hf hdisj b).toOpenPartialHomeomorph
    (radialCoordinate hL hδ f hf hdisj b)
  exact e.lift_openEmbedding (isOpen_finiteCapNeighborhood hL hδ f hf hdisj b).isOpenEmbedding_subtypeVal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart

theorem finiteCapOpenChart_source : (finiteCapOpenChart hL hδ f hf hdisj b).source = N := by
  simp only [finiteCapOpenChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, _root_.Set.image_univ, Subtype.range_coe]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_source ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_source

theorem finiteCapOpenChart_target : (finiteCapOpenChart hL hδ f hf hdisj b).target =
    {x : E3 | ‖x‖ < L + cuttingCollarWidth (precision b.1)} := by
  simp only [finiteCapOpenChart, OpenPartialHomeomorph.lift_openEmbedding_target,
    _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  change _root_.Set.range (Subtype.val ∘ finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b) = _
  rw [_root_.Set.range_comp, (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b).surjective.range_eq,
    _root_.Set.image_univ]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_target ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_target

theorem finiteCapOpenChart_apply (p : N) :
    finiteCapOpenChart hL hδ f hf hdisj b p.val =
      (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b p).val := by
  simp only [finiteCapOpenChart, OpenPartialHomeomorph.lift_openEmbedding_apply,
    _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply, radialCoordinate]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_apply

theorem finiteCapOpenChart_cap (x : Cap L) :
    finiteCapOpenChart hL hδ f hf hdisj b
      (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩) = x.val := by
  have he := finiteCapOpenChart_apply hL hδ f hf hdisj b
    ⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩, Or.inl ⟨x, rfl⟩⟩
  exact he.trans (finiteCapNeighborhoodHomeomorph_cap hL hδ f hf hdisj b x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_cap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_cap

theorem finiteCapOpenChart_collar (q : Collar (precision b.1)) :
    finiteCapOpenChart hL hδ f hf hdisj b
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q)) = (L + q.2.val) • q.1.val := by
  have he := finiteCapOpenChart_apply hL hδ f hf hdisj b
    ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q), Or.inr ⟨q, rfl⟩⟩
  exact he.trans (finiteCapNeighborhoodHomeomorph_collar hL hδ f hf hdisj b q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_collar ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_collar

theorem finiteCapOpenChart_symm_cap (x : Cap L) :
    (finiteCapOpenChart hL hδ f hf hdisj b).symm x.val =
      finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩ := by
  have hs : finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩ ∈
      (finiteCapOpenChart hL hδ f hf hdisj b).source := by
    rw [finiteCapOpenChart_source]
    exact Or.inl ⟨x, rfl⟩
  have hi := (finiteCapOpenChart hL hδ f hf hdisj b).left_inv hs
  rw [finiteCapOpenChart_cap] at hi
  exact hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_symm_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_symm_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_symm_cap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_symm_cap

theorem finiteCapOpenChart_symm_collar (q : Collar (precision b.1)) :
    (finiteCapOpenChart hL hδ f hf hdisj b).symm ((L + q.2.val) • q.1.val) =
      finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) := by
  have hs : finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) ∈
      (finiteCapOpenChart hL hδ f hf hdisj b).source := by
    rw [finiteCapOpenChart_source]
    exact Or.inr ⟨q, rfl⟩
  have hi := (finiteCapOpenChart hL hδ f hf hdisj b).left_inv hs
  rw [finiteCapOpenChart_collar] at hi
  exact hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_symm_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_symm_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_symm_collar ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_symm_collar

theorem pairwise_disjoint_finiteCapOpenChart_sources :
    Pairwise (fun b c : ι × Bool => Disjoint
      (finiteCapOpenChart hL hδ f hf hdisj b).source (finiteCapOpenChart hL hδ f hf hdisj c).source) := by
  simp_rw [finiteCapOpenChart_source]
  exact pairwise_disjoint_finiteCapNeighborhoods hL hδ f (fun i => (hf i).injective) hdisj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_finiteCapOpenChart_sources then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_finiteCapOpenChart_sources"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_finiteCapOpenChart_sources ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_finiteCapOpenChart_sources

theorem finiteCapOpenChart_source_cover :
    finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj ∪
      (⋃ b : ι × Bool, (finiteCapOpenChart hL hδ f hf hdisj b).source) = univ := by
  simp_rw [finiteCapOpenChart_source]
  exact finiteCapNeighborhood_cover hL hδ f hf hdisj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_source_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_source_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_source_cover ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapOpenChart_source_cover
end DifferentialGeometry.Topology.ThreeManifold.Surgery
