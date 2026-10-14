import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapLocalInsertion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold.Attachment
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Topology.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev FullE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FullE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.FullE3 target :: scope.openDecls } }
private abbrev FullS2 := Metric.sphere (0 : FullE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FullS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.FullS2 target :: scope.openDecls } }
private abbrev FullIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FullIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.FullIC target :: scope.openDecls } }
private abbrev FullAttachment {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :=
  AdjunctionSpace (radialCapBoundary hL) (retainedBoundary hB)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FullAttachment
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.FullAttachment target :: scope.openDecls } }

theorem preparedFullCapWidth_bounds (c δ : ℝ) (hc : 4 ≤ c) (hδ : 0 < δ) :
    0 < (c * δ)⁻¹ ∧ (c * δ)⁻¹ < cuttingCollarWidth δ := by
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have htwo : 0 < (2 : ℝ) * δ := mul_pos (by norm_num) hδ
  have hlt : 2 * δ < c * δ := mul_lt_mul_of_pos_right (by linarith) hδ
  refine ⟨inv_pos.mpr (mul_pos hcpos hδ), ?_⟩
  have h := (inv_lt_inv₀ (mul_pos hcpos hδ) htwo).mpr hlt
  simpa only [cuttingCollarWidth, mul_inv_rev, div_eq_mul_inv] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.preparedFullCapWidth_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.preparedFullCapWidth_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.preparedFullCapWidth_bounds ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.preparedFullCapWidth_bounds

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L B : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph FullIC I ∞ (f i))
variable (b : ι × Bool) (hfit : B ≤ cuttingCollarWidth (precision b.1)) (hB : 0 < B)
local notation "FullQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "FullPatch" => finiteCapRestrictedNeighborhood hL hδ f hf hdisj b B

def finiteCapFullInsertionDiffeomorph :
    let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    FullPatch ≃ₘ⟮𝓡 3, 𝓡 3⟯ FullAttachment hL hB := by
  let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  exact (finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b B hfit).trans
    (radialCapAttachmentDiffeomorph hL hB).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph

theorem finiteCapFullInsertionDiffeomorph_apply (q : FullPatch) :
    let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b hfit hB q =
      finiteCapInsertionMap I hdim hL hδ f hf hdisj hs b B hfit hB le_rfl q := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph_apply

theorem finiteCapFullInsertionDiffeomorph_symm_cap (x : {v : FullE3 // ‖v‖ ≤ L}) :
    let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    (finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b hfit hB).symm
      (adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) x) =
        ⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩,
          finiteCapInclusion_mem_restrictedNeighborhood hL hδ f hf hdisj b hB x⟩ := by
  let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  let D := finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b hfit hB
  apply D.injective
  exact (D.apply_symm_apply _).trans
    ((finiteCapFullInsertionDiffeomorph_apply I hdim hL hδ f hf hdisj hs b hfit hB _).trans
      (finiteCapInsertionMap_cap I hdim hL hδ f hf hdisj hs b B hfit hB le_rfl hB x)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph_symm_cap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph_symm_cap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph_symm_cap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph_symm_cap

theorem finiteCapFullInsertionDiffeomorph_symm_collar (q : FullS2 × _root_.Set.Ico (0 : ℝ) B) :
    let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    (finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b hfit hB).symm
      (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB) q) =
        ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
          (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
            (q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans_le hfit⟩)),
          (finiteCapRestrictedNeighborhood_collar_iff hL hδ f hf hdisj b B _).mpr q.2.property.2⟩ := by
  let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  let D := finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b hfit hB
  apply D.injective
  exact (D.apply_symm_apply _).trans
    ((finiteCapFullInsertionDiffeomorph_apply I hdim hL hδ f hf hdisj hs b hfit hB _).trans
      (finiteCapInsertionMap_collar I hdim hL hδ f hf hdisj hs b B hfit hB le_rfl
        (q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans_le hfit⟩) q.2.property.2)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph_symm_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph_symm_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph_symm_collar ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapFullInsertionDiffeomorph_symm_collar
end DifferentialGeometry.Topology.ThreeManifold.Surgery
