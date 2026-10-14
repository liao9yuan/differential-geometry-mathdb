import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSmoothManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.IsManifold
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
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph SmoothIC I ∞ (f i)) (b : ι × Bool)
local notation "NeighborhoodQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCapNeighborhoodOpens : _root_.TopologicalSpace.Opens NeighborhoodQ :=
  ⟨finiteCapNeighborhood hL hδ f (fun i => (hf i).injective) hdisj b,
    isOpen_finiteCapNeighborhood hL hδ f hf hdisj b⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodOpens then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodOpens"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodOpens ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodOpens

def finiteCapRadialBall : _root_.TopologicalSpace.Opens SmoothE3 :=
  ⟨{x | ‖x‖ < L + cuttingCollarWidth (precision b.1)}, isOpen_lt continuous_norm continuous_const⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialBall ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRadialBall

def finiteCapNeighborhoodDiffeomorph :
    let : ChartedSpace SmoothE3 NeighborhoodQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Diffeomorph (𝓡 3) (𝓡 3) (finiteCapNeighborhoodOpens hL hδ f hf hdisj b)
      (finiteCapRadialBall (L := L) (precision := precision) b) ∞ := by
  let : ChartedSpace SmoothE3 NeighborhoodQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ NeighborhoodQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let U := finiteCapNeighborhoodOpens hL hδ f hf hdisj b
  let V := finiteCapRadialBall (L := L) (precision := precision) b
  let e : U ≃ₜ V := finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b
  let c := finiteCapOpenChart hL hδ f hf hdisj b
  have hc : c ∈ _root_.IsManifold.maximalAtlas (𝓡 3) ∞ NeighborhoodQ :=
    StructureGroupoid.subset_maximalAtlas _ (show c ∈ @ChartedSpace.atlas SmoothE3 _ NeighborhoodQ _ (finiteCapChartedSpace I hdim hL hδ f hf hdisj) from Or.inr ⟨b, rfl⟩)
  have hsource (p : U) : p.val ∈ c.source := by
    rw [finiteCapOpenChart_source]
    exact p.property
  have htarget (x : V) : x.val ∈ c.target := by
    rw [finiteCapOpenChart_target]
    exact x.property
  have hforward (p : U) : c p.val = (e p).val := finiteCapOpenChart_apply hL hδ f hf hdisj b p
  have hinverse (x : V) : (e.symm x).val = c.symm x.val := by
    have he := c.left_inv (hsource (e.symm x))
    rw [hforward, e.apply_symm_apply] at he
    exact he.symm
  refine { toEquiv := e.toEquiv, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff V e).mp
    intro p
    have h := (contMDiffAt_of_mem_maximalAtlas hc (hsource p)).comp p
      (contMDiff_subtype_val (U := U)).contMDiffAt
    apply h.congr_of_eventuallyEq
    filter_upwards with q
    exact (hforward q).symm
  · apply (ContMDiff.subtypeVal_comp_iff U e.symm).mp
    intro x
    have h := (contMDiffAt_symm_of_mem_maximalAtlas hc (htarget x)).comp x
      (contMDiff_subtype_val (U := V)).contMDiffAt
    apply h.congr_of_eventuallyEq
    filter_upwards with y
    exact hinverse y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodDiffeomorph

theorem finiteCapNeighborhoodDiffeomorph_apply (p : finiteCapNeighborhoodOpens hL hδ f hf hdisj b) :
    finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b p =
      finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b p := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodDiffeomorph_apply

theorem finiteCapNeighborhoodDiffeomorph_symm_apply
    (x : finiteCapRadialBall (L := L) (precision := precision) b) :
    let : ChartedSpace SmoothE3 NeighborhoodQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    (finiteCapNeighborhoodDiffeomorph I hdim hL hδ f hf hdisj hs b).symm x =
      (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b).symm x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapNeighborhoodDiffeomorph_symm_apply
end DifferentialGeometry.Topology.ThreeManifold.Surgery
