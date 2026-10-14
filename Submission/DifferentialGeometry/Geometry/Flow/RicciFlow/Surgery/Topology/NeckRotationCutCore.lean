import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedTubeSystem
import Submission.DifferentialGeometry.Geometry.Neck.ScalarRetainedCore
import Submission.DifferentialGeometry.Geometry.Neck.BufferedRotation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedNeckDatum

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.TopologicalSpace _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

private theorem componentMap_setCongr_injective {M : Type*} [TopologicalSpace M]
    {S T : Set M} (h : S = T) :
    Injective (Homeomorph.setCongr h).continuous.connectedComponentsMap := by
  cases h
  intro c d he
  have hid (c : ConnectedComponents S) :
      (Homeomorph.setCongr rfl : S ≃ₜ S).continuous.connectedComponentsMap c = c := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl
  rw [hid, hid] at he
  exact he

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.componentMap_setCongr_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.componentMap_setCongr_injective target :: scope.openDecls } }

variable {M : Type*} [TopologicalSpace M] {ι : Type*} {δ : ι → ℝ}
  {f f' : ∀ i, bufferedCylinder (δ i) → M}

section CuttingSphere
variable [Finite ι] [T2Space M] [LocallyPathConnectedSpace M]
  (hδ : ∀ i, 0 < δ i)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hf' : ∀ i, _root_.Topology.IsOpenEmbedding (f' i))
  (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
  (hdisj' : Pairwise fun i j => Disjoint (range (f' i)) (range (f' j)))
  (e : ι → (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2 ≃
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2))
  (hmap : ∀ i z, f' i z = f i ⟨(e i z.val.1, z.val.2), z.property⟩)

theorem cuttingSphereComponent_map_of_sphere_reparametrization (b : ι × Bool) :
    (Homeomorph.setCongr (cutCore_eq_of_sphere_reparametrization e hmap)).continuous.connectedComponentsMap
      (cuttingSphereComponent hδ f' hf' hdisj' b) = cuttingSphereComponent hδ f hf hdisj b := by
  change ConnectedComponents.mk ((Homeomorph.setCongr (cutCore_eq_of_sphere_reparametrization e hmap))
    (cuttingSphereAttachment hδ f' (fun i => (hf' i).injective) hdisj' ⟨b, spherePoint⟩)) = _
  have he : (Homeomorph.setCongr (cutCore_eq_of_sphere_reparametrization e hmap))
      (cuttingSphereAttachment hδ f' (fun i => (hf' i).injective) hdisj' ⟨b, spherePoint⟩) =
      cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, e b.1 spherePoint⟩ := by
    apply Subtype.ext
    exact hmap b.1 _
  rw [he]
  exact cuttingSphere_component_eq hδ f hf hdisj b (e b.1 spherePoint)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_map_of_sphere_reparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_map_of_sphere_reparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_map_of_sphere_reparametrization ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_map_of_sphere_reparametrization

end CuttingSphere

section Scalar
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H M] [IsManifold I ∞ M]

theorem scalarSublevelComponents_preimage_of_cutCore_eq
    (U : _root_.TopologicalSpace.Opens M) (g : SmoothRiemannianMetric I U) (K : ℝ)
    (hcore : cutCore f' = cutCore f) :
    scalarSublevelComponents U g f' K =
      (Homeomorph.setCongr hcore).continuous.connectedComponentsMap ⁻¹'
        scalarSublevelComponents U g f K := by
  ext c
  constructor
  · rintro ⟨x, hx, hmem, he⟩
    refine ⟨x, hx, hcore ▸ hmem, ?_⟩
    rw [← he]
    rfl
  · rintro ⟨x, hx, hmem, he⟩
    refine ⟨x, hx, hcore.symm ▸ hmem, ?_⟩
    apply componentMap_setCongr_injective hcore
    exact he

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.scalarSublevelComponents_preimage_of_cutCore_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.scalarSublevelComponents_preimage_of_cutCore_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.scalarSublevelComponents_preimage_of_cutCore_eq ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.scalarSublevelComponents_preimage_of_cutCore_eq

theorem retainedCore_image_of_cutCore_eq
    (U : _root_.TopologicalSpace.Opens M) (g : SmoothRiemannianMetric I U) (K : ℝ)
    (hcore : cutCore f' = cutCore f) :
    (Subtype.val : cutCore f' → M) '' retainedCore f' (scalarSublevelComponents U g f' K) =
      (Subtype.val : cutCore f → M) '' retainedCore f (scalarSublevelComponents U g f K) := by
  rw [scalarSublevelComponents_preimage_of_cutCore_eq U g K hcore]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Homeomorph.setCongr hcore p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(Homeomorph.setCongr hcore).symm p, ?_, rfl⟩
    change ConnectedComponents.mk ((Homeomorph.setCongr hcore) ((Homeomorph.setCongr hcore).symm p)) ∈ scalarSublevelComponents U g f K
    rw [Homeomorph.apply_symm_apply]
    exact hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_image_of_cutCore_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_image_of_cutCore_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_image_of_cutCore_eq ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_image_of_cutCore_eq

theorem cuttingSphereComponent_mem_scalarSublevelComponents_iff_sphere_reparametrization
    [Finite ι] [T2Space M] [LocallyPathConnectedSpace M]
    (U : _root_.TopologicalSpace.Opens M) (g : SmoothRiemannianMetric I U) (K : ℝ)
    (hδ : ∀ i, 0 < δ i)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hf' : ∀ i, _root_.Topology.IsOpenEmbedding (f' i))
    (hdisj : Pairwise fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j)))
    (hdisj' : Pairwise fun i j => Disjoint (_root_.Set.range (f' i)) (_root_.Set.range (f' j)))
    (e : ι → (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2 ≃
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Sphere 2))
    (hmap : ∀ i z, f' i z = f i ⟨(e i z.val.1, z.val.2), z.property⟩)
    (b : ι × Bool) :
    cuttingSphereComponent hδ f' hf' hdisj' b ∈ scalarSublevelComponents U g f' K ↔
      cuttingSphereComponent hδ f hf hdisj b ∈ scalarSublevelComponents U g f K := by
  rw [scalarSublevelComponents_preimage_of_cutCore_eq U g K
    (cutCore_eq_of_sphere_reparametrization e hmap)]
  change _ ∈ scalarSublevelComponents U g f K ↔ _
  rw [cuttingSphereComponent_map_of_sphere_reparametrization hδ hf hf' hdisj hdisj' e hmap b]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_mem_scalarSublevelComponents_iff_sphere_reparametrization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_mem_scalarSublevelComponents_iff_sphere_reparametrization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_mem_scalarSublevelComponents_iff_sphere_reparametrization ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_mem_scalarSublevelComponents_iff_sphere_reparametrization

end Scalar
section Rotation
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.E3 target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.ThreeManifold.Surgery.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

variable (f : ∀ i, bufferedCylinder (δ i) → M) (e : ι → E3 ≃ₗᵢ[ℝ] E3)

omit [TopologicalSpace M] in
theorem cutCore_comp_bufferedCylinderRotation :
    cutCore (fun i => f i ∘ bufferedCylinderRotation (δ i) (e i)) = cutCore f := by
  apply cutCore_eq_of_sphere_reparametrization (fun i => (DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (e i)).toEquiv)
  intro i z
  apply congrArg (f i)
  apply Subtype.ext
  exact bufferedCylinderRotation_apply (δ i) (e i) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_comp_bufferedCylinderRotation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_comp_bufferedCylinderRotation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_comp_bufferedCylinderRotation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cutCore_comp_bufferedCylinderRotation

theorem isOpenEmbedding_comp_bufferedCylinderRotation
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i)) (i : ι) :
    _root_.Topology.IsOpenEmbedding (f i ∘ bufferedCylinderRotation (δ i) (e i)) :=
  (hf i).comp (bufferedCylinderRotation (δ i) (e i)).toHomeomorph.isOpenEmbedding

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpenEmbedding_comp_bufferedCylinderRotation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpenEmbedding_comp_bufferedCylinderRotation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpenEmbedding_comp_bufferedCylinderRotation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.isOpenEmbedding_comp_bufferedCylinderRotation

omit [TopologicalSpace M] in
theorem pairwise_disjoint_range_comp_bufferedCylinderRotation
    (hdisj : Pairwise fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))) :
    Pairwise fun i j => Disjoint (_root_.Set.range (f i ∘ bufferedCylinderRotation (δ i) (e i)))
      (_root_.Set.range (f j ∘ bufferedCylinderRotation (δ j) (e j))) := by
  intro i j hij
  exact (hdisj hij).mono (_root_.Set.range_comp_subset_range _ _) (_root_.Set.range_comp_subset_range _ _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_range_comp_bufferedCylinderRotation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_range_comp_bufferedCylinderRotation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_range_comp_bufferedCylinderRotation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.pairwise_disjoint_range_comp_bufferedCylinderRotation

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H M] [IsManifold I ∞ M]

theorem retainedCore_image_comp_bufferedCylinderRotation
    (U : _root_.TopologicalSpace.Opens M) (g : SmoothRiemannianMetric I U) (K : ℝ) :
    (Subtype.val : cutCore (fun i => f i ∘ bufferedCylinderRotation (δ i) (e i)) → M) ''
      retainedCore (fun i => f i ∘ bufferedCylinderRotation (δ i) (e i))
        (scalarSublevelComponents U g (fun i => f i ∘ bufferedCylinderRotation (δ i) (e i)) K) =
      (Subtype.val : cutCore f → M) '' retainedCore f (scalarSublevelComponents U g f K) :=
  retainedCore_image_of_cutCore_eq U g K (cutCore_comp_bufferedCylinderRotation f e)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_image_comp_bufferedCylinderRotation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_image_comp_bufferedCylinderRotation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_image_comp_bufferedCylinderRotation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.retainedCore_image_comp_bufferedCylinderRotation

theorem cuttingSphereComponent_mem_comp_bufferedCylinderRotation
    [Finite ι] [T2Space M] [LocallyPathConnectedSpace M]
    (U : _root_.TopologicalSpace.Opens M) (g : SmoothRiemannianMetric I U) (K : ℝ) (hδ : ∀ i, 0 < δ i)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise fun i j => Disjoint (_root_.Set.range (f i)) (_root_.Set.range (f j))) (b : ι × Bool) :
    cuttingSphereComponent hδ (fun i => f i ∘ bufferedCylinderRotation (δ i) (e i))
      (isOpenEmbedding_comp_bufferedCylinderRotation f e hf)
      (pairwise_disjoint_range_comp_bufferedCylinderRotation f e hdisj) b ∈
      scalarSublevelComponents U g (fun i => f i ∘ bufferedCylinderRotation (δ i) (e i)) K ↔
    cuttingSphereComponent hδ f hf hdisj b ∈ scalarSublevelComponents U g f K := by
  apply cuttingSphereComponent_mem_scalarSublevelComponents_iff_sphere_reparametrization U g K hδ hf
    (isOpenEmbedding_comp_bufferedCylinderRotation f e hf)
    hdisj (pairwise_disjoint_range_comp_bufferedCylinderRotation f e hdisj)
    (fun i => (DifferentialGeometry.Geometry.sphereDiffeo (n := 2) (e i)).toEquiv) _ b
  intro i z
  apply congrArg (f i)
  apply Subtype.ext
  exact bufferedCylinderRotation_apply (δ i) (e i) z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_mem_comp_bufferedCylinderRotation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_mem_comp_bufferedCylinderRotation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_mem_comp_bufferedCylinderRotation ``Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery.cuttingSphereComponent_mem_comp_bufferedCylinderRotation

end Rotation
end DifferentialGeometry.Topology.ThreeManifold.Surgery

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Topology.ThreeManifold.Surgery
universe u
private instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceOfNat target :: scope.openDecls } }
private instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] {ι : Type*}
  (U : Opens M) (g : SmoothRiemannianMetric ThreeModel U)
  {δ : ι → ℝ} {k : ι → ℕ} (N : ∀ i, NormalizedNeck g (δ i) (k i))
  (e : ι → ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
  (he : ∀ i, sphereDiffeo (n := 2) (e i) spherePoint = (N i).sphereMark)
  (side : ι → Bool)

theorem rotatedDatum_retainedCore_image (K : ℝ) :
    (Subtype.val : cutCore (fun i => neckAmbientMap U ((N i).rotatedDatum (e i) (he i) (side i))) → M) ''
      retainedCore (fun i => neckAmbientMap U ((N i).rotatedDatum (e i) (he i) (side i)))
        (scalarSublevelComponents U g (fun i => neckAmbientMap U ((N i).rotatedDatum (e i) (he i) (side i))) K) =
    (Subtype.val : cutCore (fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val) → M) ''
      retainedCore (fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val) (scalarSublevelComponents U g (fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val) K) := by
  have hf : (fun i => neckAmbientMap U ((N i).rotatedDatum (e i) (he i) (side i))) =
      (fun i => (fun q : bufferedCylinder (δ i) => ((N i).chart q).val) ∘ bufferedCylinderRotation (δ i) (e i)) := rfl
  rw [hf]
  exact retainedCore_image_comp_bufferedCylinderRotation (fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val) e U g K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rotatedDatum_retainedCore_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rotatedDatum_retainedCore_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rotatedDatum_retainedCore_image ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rotatedDatum_retainedCore_image

theorem rotatedDatum_cuttingSphereComponent_mem [Finite ι] (K : ℝ)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding ((fun q : bufferedCylinder (δ i) => ((N i).chart q).val)))
    (hdisj : Pairwise fun i j => Disjoint (_root_.Set.range ((fun q : bufferedCylinder (δ i) => ((N i).chart q).val))) (_root_.Set.range ((fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val) j)))
    (b : ι × Bool) :
    let f := (fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val)
    let f' := fun i => neckAmbientMap U ((N i).rotatedDatum (e i) (he i) (side i))
    let hf' := isOpenEmbedding_comp_bufferedCylinderRotation f e hf
    let hdisj' := pairwise_disjoint_range_comp_bufferedCylinderRotation f e hdisj
    cuttingSphereComponent (fun i => (N i).delta_pos) f' hf' hdisj' b ∈ scalarSublevelComponents U g f' K ↔
      cuttingSphereComponent (fun i => (N i).delta_pos) f hf hdisj b ∈ scalarSublevelComponents U g f K := by
  let : LocallyPathConnectedSpace M :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners ThreeModel
  exact cuttingSphereComponent_mem_comp_bufferedCylinderRotation (fun i => fun q : bufferedCylinder (δ i) => ((N i).chart q).val) e U g K
    (fun i => (N i).delta_pos) hf hdisj b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rotatedDatum_cuttingSphereComponent_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rotatedDatum_cuttingSphereComponent_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rotatedDatum_cuttingSphereComponent_mem ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.rotatedDatum_cuttingSphereComponent_mem

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
