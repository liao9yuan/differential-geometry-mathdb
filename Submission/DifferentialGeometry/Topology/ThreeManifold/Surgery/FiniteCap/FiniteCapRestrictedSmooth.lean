import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapRestrictedNeighborhood
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
private abbrev PatchE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.PatchE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.PatchE3 target :: scope.openDecls } }
private abbrev PatchIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.PatchIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.PatchIC target :: scope.openDecls } }

def finiteCapRestrictedBall (L r : ℝ) : _root_.TopologicalSpace.Opens PatchE3 :=
  ⟨{x | ‖x‖ < L + r}, isOpen_lt continuous_norm continuous_const⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedBall ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedBall

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph PatchIC I ∞ (f i))
local notation "PatchQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCapRestrictedDiffeomorph (b : ι × Bool) (r : ℝ)
    (hfit : r ≤ cuttingCollarWidth (precision b.1)) :
    let : ChartedSpace PatchE3 PatchQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    Diffeomorph (𝓡 3) (𝓡 3) (finiteCapRestrictedNeighborhood hL hδ f hf hdisj b r)
      (finiteCapRestrictedBall L r) ∞ := by
  let : ChartedSpace PatchE3 PatchQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : IsManifold (𝓡 3) ∞ PatchQ := finiteCapQuotient_isManifold hdim hL hδ f hf hdisj hs
  let U := finiteCapRestrictedNeighborhood hL hδ f hf hdisj b r
  let V := finiteCapRestrictedBall L r
  let c := finiteCapOpenChart hL hδ f hf hdisj b
  have hc : c ∈ _root_.IsManifold.maximalAtlas (𝓡 3) ∞ PatchQ :=
    StructureGroupoid.subset_maximalAtlas _ (show c ∈ @ChartedSpace.atlas PatchE3 _ PatchQ _
      (finiteCapChartedSpace I hdim hL hδ f hf hdisj) from Or.inr ⟨b, rfl⟩)
  have hx (x : V) : x.val ∈ c.target := by
    rw [finiteCapOpenChart_target]
    exact (show ‖x.val‖ < L + r from x.property).trans_le (add_le_add le_rfl hfit)
  let F : U → V := fun p => ⟨c p.val, p.property.2⟩
  let G : V → U := fun x => ⟨c.symm x.val, c.map_target (hx x), by
    change ‖c (c.symm x.val)‖ < L + r
    rw [c.right_inv (hx x)]
    exact x.property⟩
  refine
    { toEquiv :=
        { toFun := F
          invFun := G
          left_inv := fun p => Subtype.ext (c.left_inv p.property.1)
          right_inv := fun x => Subtype.ext (c.right_inv (hx x)) }
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff V F).mp
    intro p
    exact (contMDiffAt_of_mem_maximalAtlas hc p.property.1).comp p
      (contMDiff_subtype_val (U := U)).contMDiffAt
  · apply (ContMDiff.subtypeVal_comp_iff U G).mp
    intro x
    exact (contMDiffAt_symm_of_mem_maximalAtlas hc (hx x)).comp x
      (contMDiff_subtype_val (U := V)).contMDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph

theorem finiteCapRestrictedDiffeomorph_apply (b : ι × Bool) (r : ℝ)
    (hfit : r ≤ cuttingCollarWidth (precision b.1))
    (p : finiteCapRestrictedNeighborhood hL hδ f hf hdisj b r) :
    (finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit p).val =
      finiteCapOpenChart hL hδ f hf hdisj b p.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph_apply

theorem finiteCapRestrictedDiffeomorph_symm_apply (b : ι × Bool) (r : ℝ)
    (hfit : r ≤ cuttingCollarWidth (precision b.1)) (x : finiteCapRestrictedBall L r) :
    let : ChartedSpace PatchE3 PatchQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ((finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit).symm x).val =
      (finiteCapOpenChart hL hδ f hf hdisj b).symm x.val := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph_symm_apply

theorem finiteCapRestrictedDiffeomorph_symm_cap (b : ι × Bool) (r : ℝ) (hr : 0 < r)
    (hfit : r ≤ cuttingCollarWidth (precision b.1)) (x : {v : PatchE3 // ‖v‖ ≤ L}) :
    let : ChartedSpace PatchE3 PatchQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    ((finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit).symm
      ⟨x.val, x.property.trans_lt (lt_add_of_pos_right L hr)⟩).val =
        finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩ := by
  let : ChartedSpace PatchE3 PatchQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  exact finiteCapOpenChart_symm_cap hL hδ f hf hdisj b x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph_symm_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph_symm_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph_symm_cap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapRestrictedDiffeomorph_symm_cap
end DifferentialGeometry.Topology.ThreeManifold.Surgery
