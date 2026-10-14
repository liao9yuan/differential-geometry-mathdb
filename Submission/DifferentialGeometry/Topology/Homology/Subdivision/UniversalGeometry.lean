import Submission.DifferentialGeometry.Topology.Homology.Subdivision.Singular

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.Simplicial

universe u

namespace DifferentialGeometry.Homology


def simplexCoordinateEmbedding (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ⟶ TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.down.val⟩,
    continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.simplexCoordinateEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.simplexCoordinateEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.simplexCoordinateEmbedding ``Submission.DifferentialGeometry.Homology.simplexCoordinateEmbedding

private def coordinateRegion (n : ℕ) : Set (ULift.{u} (Fin (n + 1) → ℝ)) :=
  ULift.down ⁻¹' stdSimplex ℝ (Fin (n + 1))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.coordinateRegion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.coordinateRegion target :: scope.openDecls } }

private theorem convex_coordinateRegion (n : ℕ) : Convex ℝ (coordinateRegion.{u} n) := by
  intro x hx y hy a b ha hb hab
  exact (convex_stdSimplex ℝ (Fin (n + 1))) hx hy ha hb hab

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.convex_coordinateRegion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.convex_coordinateRegion target :: scope.openDecls } }

private def coordinateRegionHomeo (n : ℕ) :
    SimplexCategory.toTop.{u}.obj ⦋n⦌ ≃ₜ coordinateRegion.{u} n where
  toFun x := ⟨⟨x.down.val⟩, x.down.property⟩
  invFun x := ⟨⟨x.val.down, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_uliftUp.comp (continuous_subtype_val.comp continuous_uliftDown)).subtype_mk _
  continuous_invFun :=
    continuous_uliftUp.comp ((continuous_uliftDown.comp continuous_subtype_val).subtype_mk _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.coordinateRegionHomeo
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.coordinateRegionHomeo target :: scope.openDecls } }

variable {k : Type u} [Ring k] (R : ModuleCat.{u} k)

private def coordinateChainIso (n : ℕ) :=
  ((SSet.chainComplexFunctor (ModuleCat.{u} k)).obj R).mapIso
    (TopCat.toSSet.mapIso (TopCat.isoOfHomeo (coordinateRegionHomeo n)) ≪≫
      singularSubspaceIso (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ))) (coordinateRegion n))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.coordinateChainIso
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.coordinateChainIso target :: scope.openDecls } }

private theorem coordinateChainIso_inclusion (n : ℕ) :
    (coordinateChainIso R n).hom ≫
      SSet.chainComplexMap
        (smallSingularSimplices (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))
          (fun _ : Unit ↦ coordinateRegion n)).ι R =
      SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R := by
  change ((SSet.chainComplexFunctor _).obj R).map _ ≫
      ((SSet.chainComplexFunctor _).obj R).map _ =
    ((SSet.chainComplexFunctor _).obj R).map _
  rw [← Functor.map_comp]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.coordinateChainIso_inclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.coordinateChainIso_inclusion target :: scope.openDecls } }

private theorem coordinateChainIso_inv_inclusion (n : ℕ) :
    (coordinateChainIso R n).inv ≫
        SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R =
      SSet.chainComplexMap
        (smallSingularSimplices (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))
          (fun _ : Unit ↦ coordinateRegion n)).ι R := by
  rw [← coordinateChainIso_inclusion R n, Iso.inv_hom_id_assoc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Homology.coordinateChainIso_inv_inclusion
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Homology.coordinateChainIso_inv_inclusion target :: scope.openDecls } }


theorem mono_simplexCoordinateEmbedding_chainMap_f (n d : ℕ) :
    Mono ((SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R).f d) := by
  have h := HomologicalComplex.congr_hom (coordinateChainIso_inclusion R n) d
  simp only [HomologicalComplex.comp_f] at h
  rw [← h]
  have : _root_.CategoryTheory.Mono ((SSet.chainComplexMap
      (smallSingularSimplices (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))
        (fun _ : Unit ↦ coordinateRegion n)).ι R).f d) :=
    mono_smallChainMap_f _ _ R d
  infer_instance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.mono_simplexCoordinateEmbedding_chainMap_f then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.mono_simplexCoordinateEmbedding_chainMap_f"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.mono_simplexCoordinateEmbedding_chainMap_f ``Submission.DifferentialGeometry.Homology.mono_simplexCoordinateEmbedding_chainMap_f


theorem simplexSubdivision_coordinateEmbedding (n : ℕ) :
    simplexSubdivision R n ≫
        SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R =
      SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R ≫
        affineSubdivision R := by
  change ((coordinateChainIso R n).hom ≫
      smallAffineSubdivision (convex_coordinateRegion n) R ≫ (coordinateChainIso R n).inv) ≫
        SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R = _
  simp only [Category.assoc]
  rw [coordinateChainIso_inv_inclusion]
  rw [smallAffineSubdivision_inclusion]
  rw [← Category.assoc ((coordinateChainIso R n).hom), coordinateChainIso_inclusion]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.simplexSubdivision_coordinateEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.simplexSubdivision_coordinateEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.simplexSubdivision_coordinateEmbedding ``Submission.DifferentialGeometry.Homology.simplexSubdivision_coordinateEmbedding


theorem affineSimplex_coordinateVertices (n : ℕ) (x : stdSimplex ℝ (Fin (n + 1))) :
    affineSimplex (fun i ↦ (ULift.up (stdSimplex.vertex (S := ℝ) i).val :
      ULift.{u} (Fin (n + 1) → ℝ))) x = ULift.up x.val := by
  apply ULift.ext
  change (ULift.moduleEquiv : ULift.{u} (Fin (n + 1) → ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
      (∑ i, x i • ULift.up (stdSimplex.vertex (S := ℝ) i).val) = x.val
  rw [map_sum]
  simp only [map_smul, ULift.moduleEquiv_apply]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.affineSimplex_coordinateVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.affineSimplex_coordinateVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.affineSimplex_coordinateVertices ``Submission.DifferentialGeometry.Homology.affineSimplex_coordinateVertices


theorem singularSimplexMap_coordinateVertices (n : ℕ) :
    singularSimplexMap (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))
        (affineSingularSimplex (fun i ↦ ULift.up (stdSimplex.vertex (S := ℝ) i).val)) =
      simplexCoordinateEmbedding n := by
  apply TopCat.ext
  intro x
  exact affineSimplex_coordinateVertices n x.down

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSimplexMap_coordinateVertices then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSimplexMap_coordinateVertices"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSimplexMap_coordinateVertices ``Submission.DifferentialGeometry.Homology.singularSimplexMap_coordinateVertices


theorem barycentricSimplexChain_coordinateEmbedding (n : ℕ) :
    barycentricSimplexChain R n ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R).f n =
      (TopCat.toSSet.obj (TopCat.of (ULift.{u} (Fin (n + 1) → ℝ)))).ιChainComplex
        (affineSingularSimplex (fun i ↦ ULift.up (stdSimplex.vertex (S := ℝ) i).val)) ≫
          affineSubdivisionMap R n := by
  have h := HomologicalComplex.congr_hom (simplexSubdivision_coordinateEmbedding R n) n
  simp only [HomologicalComplex.comp_f, affineSubdivision_f] at h
  rw [barycentricSimplexChain, Category.assoc, h, ← Category.assoc]
  rw [← singularSimplexMap_coordinateVertices, fundamentalSimplexChain_pushforward]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.barycentricSimplexChain_coordinateEmbedding then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.barycentricSimplexChain_coordinateEmbedding"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.barycentricSimplexChain_coordinateEmbedding ``Submission.DifferentialGeometry.Homology.barycentricSimplexChain_coordinateEmbedding

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def vertexCoordinateMap {n : ℕ} (v : Fin (n + 1) → E) :
    ULift.{u} (Fin (n + 1) → ℝ) →L[ℝ] E where
  toFun x := ∑ i, x.down i • v i
  map_add' x y := by
    change (∑ i, (x.down i + y.down i) • v i) = _
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ i, (a * x.down i) • v i) = a • ∑ i, x.down i • v i
    simp only [Finset.smul_sum, _root_.SemigroupAction.mul_smul]
  cont := continuous_finsetSum _ (fun i _ ↦
    ((continuous_apply i).comp continuous_uliftDown).smul continuous_const)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.vertexCoordinateMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.vertexCoordinateMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.vertexCoordinateMap ``Submission.DifferentialGeometry.Homology.vertexCoordinateMap


@[simp]
theorem vertexCoordinateMap_vertex {n : ℕ} (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    vertexCoordinateMap v (ULift.up (stdSimplex.vertex (S := ℝ) i).val) = v i := by
  simp [vertexCoordinateMap, Pi.single_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.vertexCoordinateMap_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.vertexCoordinateMap_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.vertexCoordinateMap_vertex ``Submission.DifferentialGeometry.Homology.vertexCoordinateMap_vertex


theorem simplexCoordinateEmbedding_vertexCoordinateMap {n : ℕ} (v : Fin (n + 1) → E) :
    simplexCoordinateEmbedding n ≫ TopCat.ofHom (⟨vertexCoordinateMap v,
        (vertexCoordinateMap v).continuous⟩ : C(ULift.{u} (Fin (n + 1) → ℝ), E)) =
      singularSimplexMap (TopCat.of E) (affineSingularSimplex v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.simplexCoordinateEmbedding_vertexCoordinateMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.simplexCoordinateEmbedding_vertexCoordinateMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.simplexCoordinateEmbedding_vertexCoordinateMap ``Submission.DifferentialGeometry.Homology.simplexCoordinateEmbedding_vertexCoordinateMap


theorem singularSubdivisionMap_affine {n : ℕ} (v : Fin (n + 1) → E) :
    (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (affineSingularSimplex v) ≫
        singularSubdivisionMap R (TopCat.of E) n =
      (TopCat.toSSet.obj (TopCat.of E)).ιChainComplex (affineSingularSimplex v) ≫
        affineSubdivisionMap R n := by
  let F := SSet.chainComplexMap (TopCat.toSSet.map
    (TopCat.ofHom (⟨vertexCoordinateMap v, (vertexCoordinateMap v).continuous⟩ :
      C(ULift.{u} (Fin (n + 1) → ℝ), E)))) R
  have hF : SSet.chainComplexMap (TopCat.toSSet.map (simplexCoordinateEmbedding n)) R ≫ F =
      SSet.chainComplexMap (TopCat.toSSet.map
        (singularSimplexMap (TopCat.of E) (affineSingularSimplex v))) R := by
    change ((SSet.chainComplexFunctor _).obj R).map _ ≫
        ((SSet.chainComplexFunctor _).obj R).map _ =
      ((SSet.chainComplexFunctor _).obj R).map _
    rw [← Functor.map_comp, ← TopCat.toSSet.map_comp,
      simplexCoordinateEmbedding_vertexCoordinateMap]
  have hf := HomologicalComplex.congr_hom hF n
  simp only [HomologicalComplex.comp_f] at hf
  rw [ι_singularSubdivisionMap, ← hf, ← Category.assoc,
    barycentricSimplexChain_coordinateEmbedding, Category.assoc]
  have hn : affineSubdivisionMap R n ≫ F.f n = F.f n ≫ affineSubdivisionMap R n :=
    affineSubdivisionMap_naturality_linear (vertexCoordinateMap v) R n
  rw [hn, ← Category.assoc]
  change (_ ≫ (SSet.chainComplexMap _ R).f n) ≫ _ = _
  rw [SSet.ι_chainComplexMap_f, map_affineSingularSimplex_linear]
  have hv : vertexCoordinateMap v ∘
      (fun i ↦ ULift.up (stdSimplex.vertex (S := ℝ) i).val) = v := by
    funext i
    exact vertexCoordinateMap_vertex v i
  rw [hv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Homology.singularSubdivisionMap_affine then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Homology.singularSubdivisionMap_affine"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Homology.singularSubdivisionMap_affine ``Submission.DifferentialGeometry.Homology.singularSubdivisionMap_affine

end DifferentialGeometry.Homology
