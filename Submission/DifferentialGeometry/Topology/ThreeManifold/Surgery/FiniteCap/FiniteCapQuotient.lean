import Submission.DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionInjectivity
import Submission.DifferentialGeometry.Topology.Manifold.Attachment.RadialCap
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingSphereAttachment

import Mathlib.Topology.Compactness.SigmaCompact

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
private abbrev Cap (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.Cap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.Cap target :: scope.openDecls } }

abbrev IndexedCaps (ι : Type*) (L : ℝ) := Σ _b : ι × Bool, Cap L

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.IndexedCaps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.IndexedCaps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.IndexedCaps ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.IndexedCaps

def indexedCapBoundary {ι : Type*} {L : ℝ} (hL : 0 < L) : CuttingSpheres ι → IndexedCaps ι L :=
  fun p => ⟨p.1, radialCapBoundary hL p.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.indexedCapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.indexedCapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.indexedCapBoundary ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.indexedCapBoundary

theorem injective_indexedCapBoundary {ι : Type*} {L : ℝ} (hL : 0 < L) :
    Injective (indexedCapBoundary (ι := ι) hL) := by
  rintro ⟨i, y⟩ ⟨j, z⟩ he
  have hij : i = j := congrArg Sigma.fst he
  subst j
  have hs : radialCapBoundary hL y = radialCapBoundary hL z := eq_of_heq (Sigma.mk.inj he).2
  have hv := congrArg (fun x : Cap L => L⁻¹ • x.val) hs
  change L⁻¹ • (L • y.val) = L⁻¹ • (L • z.val) at hv
  simp only [smul_smul, inv_mul_cancel₀ hL.ne', one_smul] at hv
  exact congrArg (Sigma.mk i) (Subtype.ext hv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_indexedCapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_indexedCapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_indexedCapBoundary ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_indexedCapBoundary

theorem norm_indexedCapBoundary {ι : Type*} {L : ℝ} (hL : 0 < L) (p : CuttingSpheres ι) :
    ‖(indexedCapBoundary hL p).2.val‖ = L := by
  change ‖L • p.2.val‖ = L
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  have hp : ‖p.2.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using p.2.property
  rw [hp, mul_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.norm_indexedCapBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.norm_indexedCapBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.norm_indexedCapBoundary ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.norm_indexedCapBoundary

variable {ι M : Type*} {precision : ι → ℝ} {L : ℝ}

abbrev FiniteCapQuotient (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :=
  AdjunctionSpace (indexedCapBoundary hL) (cuttingSphereAttachment hδ f hf hdisj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCapQuotient

def finiteCapInclusion (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    IndexedCaps ι L → FiniteCapQuotient hL hδ f hf hdisj :=
  adjunctionCell (indexedCapBoundary hL) (cuttingSphereAttachment hδ f hf hdisj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion

def finiteCoreInclusion (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    cutCore f → FiniteCapQuotient hL hδ f hf hdisj :=
  adjunctionLower (i := indexedCapBoundary hL) (cuttingSphereAttachment hδ f hf hdisj)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCoreInclusion

theorem finiteCapQuotient_coherence (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) (p : CuttingSpheres ι) :
    finiteCapInclusion hL hδ f hf hdisj (indexedCapBoundary hL p) =
      finiteCoreInclusion hL hδ f hf hdisj (cuttingSphereAttachment hδ f hf hdisj p) :=
  adjunction_coherence _ _ p

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_coherence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_coherence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_coherence ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_coherence

theorem injective_finiteCoreInclusion (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    Injective (finiteCoreInclusion hL hδ f hf hdisj) :=
  adjunctionLower_injective _ _ (injective_indexedCapBoundary hL)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteCoreInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteCoreInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteCoreInclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteCoreInclusion

theorem injective_finiteCapInclusion (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    Injective (finiteCapInclusion hL hδ f hf hdisj) := by
  apply adjunctionCell_injective _ _ (injective_indexedCapBoundary hL)
  intro p q he
  exact injective_cuttingSphereMap hδ f hf hdisj (congrArg Subtype.val he)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteCapInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteCapInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteCapInclusion ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.injective_finiteCapInclusion

theorem finiteCapQuotient_cover (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    range (finiteCapInclusion hL hδ f hf hdisj) ∪ _root_.Set.range (finiteCoreInclusion hL hδ f hf hdisj) = univ :=
  adjunction_inclusions_cover _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_cover ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_cover

theorem finiteCapQuotient_inter (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    _root_.Set.range (finiteCapInclusion hL hδ f hf hdisj) ∩ _root_.Set.range (finiteCoreInclusion hL hδ f hf hdisj) =
      range (finiteCapInclusion hL hδ f hf hdisj ∘ indexedCapBoundary hL) :=
  adjunction_inclusions_inter _ _ (injective_indexedCapBoundary hL)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_inter ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_inter

theorem finiteCapQuotient_different_indices (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))))
    (b c : ι × Bool) (hbc : b ≠ c) (x y : Cap L) :
    finiteCapInclusion hL hδ f hf hdisj ⟨b, x⟩ ≠ finiteCapInclusion hL hδ f hf hdisj ⟨c, y⟩ := by
  intro he
  exact hbc (congrArg Sigma.fst (injective_finiteCapInclusion hL hδ f hf hdisj he))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_different_indices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_different_indices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_different_indices ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_different_indices

theorem finiteCapInclusion_not_mem_core_of_norm_lt (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, _root_.Function.Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))))
    (b : ι × Bool) (x : Cap L) (hx : ‖x.val‖ < L) :
    finiteCapInclusion hL hδ f hf hdisj ⟨b, x⟩ ∉ _root_.Set.range (finiteCoreInclusion hL hδ f hf hdisj) := by
  rintro ⟨y, hy⟩
  obtain ⟨a, ha, _⟩ := (adjunctionCell_eq_lower_iff _ _
    (injective_indexedCapBoundary hL) ⟨b, x⟩ y).mp hy.symm
  have he := congrArg (fun p : IndexedCaps ι L => ‖p.2.val‖) ha
  rw [norm_indexedCapBoundary hL a] at he
  exact (ne_of_lt hx) he.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion_not_mem_core_of_norm_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion_not_mem_core_of_norm_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion_not_mem_core_of_norm_lt ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapInclusion_not_mem_core_of_norm_lt

variable [TopologicalSpace M]

theorem finiteCapQuotient_compactSpace [CompactSpace M] [Finite ι]
    (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    CompactSpace (FiniteCapQuotient hL hδ f (fun i => (hf i).injective) hdisj) := by
  let : CompactSpace (cutCore f) := isCompact_iff_compactSpace.mp (isCompact_cutCore f hf)
  have hcap : IsCompact {x : E3 | ‖x‖ ≤ L} := by
    simpa only [Metric.closedBall, dist_zero_right] using _root_.ProperSpace.isCompact_closedBall (0 : E3) L
  let : CompactSpace (Cap L) := isCompact_iff_compactSpace.mp hcap
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_compactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_compactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_compactSpace ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_compactSpace

theorem finiteCapQuotient_sigmaCompactSpace [SigmaCompactSpace M] [Countable ι]
    (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    SigmaCompactSpace (FiniteCapQuotient hL hδ f (fun i => (hf i).injective) hdisj) := by
  let : SigmaCompactSpace (cutCore f) := (isClosed_cutCore f hf).sigmaCompactSpace
  have hcap : IsCompact {x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ L} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      _root_.ProperSpace.isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) L
  let : CompactSpace {x : EuclideanSpace ℝ (Fin 3) // ‖x‖ ≤ L} :=
    isCompact_iff_compactSpace.mp hcap
  apply isSigmaCompact_univ_iff.mp
  have h := isSigmaCompact_range (continuous_adjunctionMk (indexedCapBoundary hL)
    (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj))
  rwa [Set.range_eq_univ.mpr (isQuotientMap_adjunctionMk _ _).surjective] at h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_sigmaCompactSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_sigmaCompactSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_sigmaCompactSpace ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.finiteCapQuotient_sigmaCompactSpace

end DifferentialGeometry.Topology.ThreeManifold.Surgery
