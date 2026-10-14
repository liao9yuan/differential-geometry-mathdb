import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingLocalDiffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CoreAmbientCoordinates
import Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.SphericalCutCore
import Mathlib.Geometry.Manifold.Instances.Icc

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Topology.Manifold
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev TubeE3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeE3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeE3 target :: scope.openDecls } }
private abbrev TubeE2 := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeE2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeE2 target :: scope.openDecls } }
private abbrev TubeS2 := Metric.sphere (0 : TubeE3) 1

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeS2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeS2 target :: scope.openDecls } }
private abbrev TubeIR := (𝓡 2).prod (𝓡∂ 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeIR
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeIR target :: scope.openDecls } }
private abbrev TubeIC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeIC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.TubeIC target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealTubeE3HAddOfNat : Fact (Module.finrank ℝ TubeE3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealTubeE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealTubeE3HAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactLtRealNegOfNat_differentialGeometry : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactLtRealNegOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactLtRealNegOfNat_differentialGeometry target :: scope.openDecls } }
variable {M : Type*} [TopologicalSpace M] {δ : ℝ}

private def originalTubularDomainMap (hδ : 0 < δ) (hδ1 : δ < 1) :
    TubeS2 × _root_.Set.Icc (-2 : ℝ) 2 → bufferedCylinder δ := fun q =>
  ⟨(q.1, q.2.val), by
    have hi : 1 < δ⁻¹ := (one_lt_inv₀ hδ).mpr hδ1
    change -δ⁻¹ - 1 < q.2.val ∧ q.2.val < δ⁻¹ + 1
    constructor <;> linarith [q.2.property.1, q.2.property.2]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularDomainMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularDomainMap target :: scope.openDecls } }

def originalTubularMap (hδ : 0 < δ) (hδ1 : δ < 1) (f : bufferedCylinder δ → M) :
    TubeS2 × _root_.Set.Icc (-2 : ℝ) 2 → M := f ∘ originalTubularDomainMap hδ hδ1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap

omit [TopologicalSpace M] in
theorem range_originalTubularMap_subset (hδ : 0 < δ) (hδ1 : δ < 1) (f : bufferedCylinder δ → M) :
    range (originalTubularMap hδ hδ1 f) ⊆ _root_.Set.range f := _root_.Set.range_comp_subset_range (originalTubularDomainMap hδ hδ1) f

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_originalTubularMap_subset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.range_originalTubularMap_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.range_originalTubularMap_subset ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.range_originalTubularMap_subset

omit [TopologicalSpace M] in
theorem originalTubularMap_central_image (hδ : 0 < δ) (hδ1 : δ < 1) (f : bufferedCylinder δ → M) :
    originalTubularMap hδ hδ1 f '' {q : TubeS2 × _root_.Set.Icc (-2 : ℝ) 2 | q.2.val ∈ _root_.Set.Ioo (-1 : ℝ) 1} = removedSlab f := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨originalTubularDomainMap hδ hδ1 q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    let r : TubeS2 × _root_.Set.Icc (-2 : ℝ) 2 := (q.val.1, ⟨q.val.2, by
      change -1 < q.val.2 ∧ q.val.2 < 1 at hq
      constructor <;> linarith [hq.1, hq.2]⟩)
    refine ⟨r, hq, ?_⟩
    exact congrArg f (Subtype.ext rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap_central_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap_central_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap_central_image ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap_central_image

section Smooth
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [ChartedSpace H M] [IsManifold I ∞ M]

theorem originalTubularMap_isSmoothEmbedding (hdim : Module.finrank ℝ E = 3)
    (hδ : 0 < δ) (hδ1 : δ < 1) (f : bufferedCylinder δ → M)
    (hf : _root_.Topology.IsOpenEmbedding f) (hs : IsLocalDiffeomorph TubeIC I ∞ f) :
    IsSmoothEmbedding TubeIR I ∞ (originalTubularMap hδ hδ1 f) := by
  let : Nonempty H := ⟨I.toHomeomorph.symm 0⟩
  let j := originalTubularDomainMap hδ hδ1
  have hj : _root_.Manifold.IsSmoothEmbedding TubeIR TubeIC ∞ j :=
    isSmoothEmbedding_intoOpen TubeIR TubeIC (bufferedCylinder δ) j
      ((IsSmoothEmbedding.id : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 2) ∞ (id : TubeS2 → TubeS2)).prodMap
        (isSmoothEmbedding_subtypeVal_Icc (x := (-2 : ℝ)) (y := 2)))
  let ψ := coreAmbientNormalizingHomeomorph I hdim 0 1 (by norm_num)
  let B : (ModelProd TubeE2 ℝ) ≃ₘ⟮TubeIC, I⟯ H :=
    { toEquiv := ψ.toEquiv
      contMDiff_toFun := coreAmbientNormalizingHomeomorph_contMDiff I hdim 0 1 (by norm_num)
      contMDiff_invFun := coreAmbientNormalizingHomeomorph_symm_contMDiff I hdim 0 1 (by norm_num) }
  let A := (coreAmbientLinearEquiv hdim).symm
  have hA (y : ModelProd TubeE2 ℝ) : I (B y) = A (TubeIC y) := by
    change I (ψ y) = (coreAmbientLinearEquiv hdim).symm (y.1, y.2)
    have h := coreAmbientNormalizingHomeomorph_extend I hdim 0 1 (by norm_num) y
    simpa only [zero_add, one_mul] using h
  exact isSmoothEmbedding_openLocalDiffeomorph_comp TubeIR TubeIC I j hj f hf hs B A hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap_isSmoothEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap_isSmoothEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap_isSmoothEmbedding ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap_isSmoothEmbedding
end Smooth

variable {ι : Type*} {precision : ι → ℝ}
omit [TopologicalSpace M] in
theorem originalTubularMap_pairwise_disjoint (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hdisj : Pairwise (fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))) :
    Pairwise (fun i j => Disjoint (_root_.Set.range (originalTubularMap (hδ i) (hδ1 i) (f i)))
      (_root_.Set.range (originalTubularMap (hδ j) (hδ1 j) (f j)))) := by
  intro i j hij
  exact (hdisj hij).mono (range_originalTubularMap_subset (hδ i) (hδ1 i) (f i))
    (range_originalTubularMap_subset (hδ j) (hδ1 j) (f j))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap_pairwise_disjoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap_pairwise_disjoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap_pairwise_disjoint ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.originalTubularMap_pairwise_disjoint

omit [TopologicalSpace M] in
theorem cutCore_eq_originalTubularComplement (hδ : ∀ i, 0 < precision i) (hδ1 : ∀ i, precision i < 1)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) :
    cutCore f = (⋃ i, originalTubularMap (hδ i) (hδ1 i) (f i) ''
      {q : TubeS2 × _root_.Set.Icc (-2 : ℝ) 2 | q.2.val ∈ _root_.Set.Ioo (-1 : ℝ) 1})ᶜ := by
  simp only [originalTubularMap_central_image]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_eq_originalTubularComplement then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_eq_originalTubularComplement"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_eq_originalTubularComplement ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_eq_originalTubularComplement
end DifferentialGeometry.Topology.ThreeManifold.Surgery
