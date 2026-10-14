import Submission.DifferentialGeometry.Topology.Homology.PathCones
import Submission.DifferentialGeometry.Topology.Homology.SimplexBoundaryChain
import Submission.DifferentialGeometry.Topology.Homology.CycleClassMaps
import Submission.DifferentialGeometry.Topology.Homology.UniversalCoefficientsOneLinearEquiv
import Submission.DifferentialGeometry.Topology.Homology.SphereHurewicz
import Submission.DifferentialGeometry.Topology.Homology.SphereGenerator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap _root_.Module
open scoped _root_.Simplicial _root_.Topology

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def integralSingularTwoCycleProjection (x : X) :
    (integralSingularChains X).X 2 →ₗ[ℤ] integralSingularCycles 1 X :=
  (LinearMap.id - (integralSingularConeOne x).comp
    ((integralSingularChains X).d 2 1).hom).codRestrict (integralSingularCycles 1 X) fun z => by
      change (integralSingularChains X).d 2 1
        (z - integralSingularConeOne x ((integralSingularChains X).d 2 1 z)) = 0
      rw [map_sub, integralSingularConeOne_bounds, sub_self]
      have h := congrArg (fun f => f z) ((integralSingularChains X).d_comp_d 2 1 0)
      exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTwoCycleProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTwoCycleProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTwoCycleProjection ``Submission.DifferentialGeometry.Topology.integralSingularTwoCycleProjection

theorem integralSingularTwoCycleProjection_val (x : X) (z : (integralSingularChains X).X 2) :
    (integralSingularTwoCycleProjection x z).val =
      z - integralSingularConeOne x ((integralSingularChains X).d 2 1 z) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTwoCycleProjection_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTwoCycleProjection_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTwoCycleProjection_val ``Submission.DifferentialGeometry.Topology.integralSingularTwoCycleProjection_val

@[simp] theorem integralSingularTwoCycleProjection_cycle (x : X) (z : integralSingularCycles 1 X) :
    integralSingularTwoCycleProjection x z.val = z := by
  apply Subtype.ext
  rw [integralSingularTwoCycleProjection_val]
  have hz : (integralSingularChains X).d 2 1 z.val = 0 := z.property
  rw [hz, map_zero, sub_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularTwoCycleProjection_cycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularTwoCycleProjection_cycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularTwoCycleProjection_cycle ``Submission.DifferentialGeometry.Topology.integralSingularTwoCycleProjection_cycle

theorem span_integralSingularTwoCycleProjection (x : X) :
    Submodule.span ℤ (Set.range (fun σ : integralSingularSimplex 2 X =>
      integralSingularCycleClass 1 X
        (integralSingularTwoCycleProjection x (integralSimplexChain 2 σ)))) = ⊤ := by
  let f := (integralSingularCycleClassLinearMap 1 X).comp (integralSingularTwoCycleProjection x)
  have hspan : Submodule.span ℤ (Set.range (integralSingularChainBasis 2 X)) ≤
      Submodule.comap f (Submodule.span ℤ (Set.range (fun σ : integralSingularSimplex 2 X =>
        integralSingularCycleClass 1 X
          (integralSingularTwoCycleProjection x (integralSimplexChain 2 σ))))) := by
    rw [Submodule.span_le]
    rintro z ⟨σ, rfl⟩
    exact Submodule.subset_span ⟨σ, by
      simp only [f, LinearMap.comp_apply, integralSingularChainBasis_apply,
        integralSingularCycleClassLinearMap_apply]⟩
  apply top_unique
  intro y _
  obtain ⟨z, rfl⟩ := integralSingularCycleClass_surjective 1 X y
  have hz : f z.val ∈ Submodule.span ℤ (Set.range (fun σ : integralSingularSimplex 2 X =>
      integralSingularCycleClass 1 X
        (integralSingularTwoCycleProjection x (integralSimplexChain 2 σ)))) := by
    apply hspan
    rw [Basis.span_eq]
    exact Submodule.mem_top
  simpa only [f, LinearMap.comp_apply, integralSingularTwoCycleProjection_cycle,
    integralSingularCycleClassLinearMap_apply] using hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.span_integralSingularTwoCycleProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.span_integralSingularTwoCycleProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.span_integralSingularTwoCycleProjection ``Submission.DifferentialGeometry.Topology.span_integralSingularTwoCycleProjection

def integralSingularConeFaces (x : X) (σ : integralSingularSimplex 2 X) :
    Fin 4 → integralSingularSimplex 2 X :=
  Fin.cons σ fun i => integralSingularConeTriangle x
    ((TopCat.toSSet.obj (TopCat.of X)).δ i σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeFaces then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeFaces"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeFaces ``Submission.DifferentialGeometry.Topology.integralSingularConeFaces

theorem integralSingularConeFaces_compatible (x : X) (σ : integralSingularSimplex 2 X)
    (i : Fin 4) (j : Fin 3) :
    (TopCat.toSSet.obj (TopCat.of X)).δ j (integralSingularConeFaces x σ i) =
      (TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
        (integralSingularConeFaces x σ (i.succAbove j)) := by
  have h0 : (TopCat.toSSet.obj (TopCat.of X)).δ 0
      ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 0
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ (show (0 : Fin 2) ≤ 0 by decide))
  have h1 : (TopCat.toSSet.obj (TopCat.of X)).δ 0
      ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 1
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ (show (0 : Fin 2) ≤ 1 by decide))
  have h2 : (TopCat.toSSet.obj (TopCat.of X)).δ 1
      ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 1
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) :=
    congrArg (fun f => f σ) ((TopCat.toSSet.obj (TopCat.of X)).δ_comp_δ (show (1 : Fin 2) ≤ 1 by decide))
  fin_cases i <;> fin_cases j
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 σ = (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    simp only [integralSingularConeTriangle_face_zero]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 σ = (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    simp only [integralSingularConeTriangle_face_zero]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 σ = (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    simp only [integralSingularConeTriangle_face_zero]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 0 σ
    simp only [integralSingularConeTriangle_face_zero]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    simp only [integralSingularConeTriangle_face_one]
    rw [h0]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    simp only [integralSingularConeTriangle_face_one,
      integralSingularConeTriangle_face_two]
    rw [h1]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 σ
    simp only [integralSingularConeTriangle_face_zero]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    simp only [integralSingularConeTriangle_face_one]
    rw [h0]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ))
    simp only [integralSingularConeTriangle_face_two]
    rw [h2]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 0 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 σ
    simp only [integralSingularConeTriangle_face_zero]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 1 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ))
    simp only [integralSingularConeTriangle_face_one,
      integralSingularConeTriangle_face_two]
    rw [h1]
  · change (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ)) = (TopCat.toSSet.obj (TopCat.of X)).δ 2 (integralSingularConeTriangle x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ))
    simp only [integralSingularConeTriangle_face_two]
    rw [h2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeFaces_compatible then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeFaces_compatible"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeFaces_compatible ``Submission.DifferentialGeometry.Topology.integralSingularConeFaces_compatible

private theorem integralSingularTwoCycleProjection_simplex (x : X) (σ : integralSingularSimplex 2 X) :
    (integralSingularTwoCycleProjection x (integralSimplexChain 2 σ)).val =
      integralSimplexChain 2 (integralSingularConeFaces x σ 0) -
      integralSimplexChain 2 (integralSingularConeFaces x σ 1) +
      integralSimplexChain 2 (integralSingularConeFaces x σ 2) -
      integralSimplexChain 2 (integralSingularConeFaces x σ 3) := by
  rw [integralSingularTwoCycleProjection_val, integralSimplexChain_boundary_two, map_add,
    map_sub, integralSingularConeOne_simplex, integralSingularConeOne_simplex,
    integralSingularConeOne_simplex]
  dsimp [integralSingularConeFaces, Fin.cons]
  abel

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularTwoCycleProjection_simplex
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularTwoCycleProjection_simplex target :: scope.openDecls } }

private def integralSingularConeBoundaryMap (x : X) (σ : integralSingularSimplex 2 X) :
    C(DifferentialGeometry.Simplex.boundary (Fin 4), X) :=
  DifferentialGeometry.Simplex.boundaryDesc
    (fun i => integralSingularSimplexEquiv 2 X (integralSingularConeFaces x σ i)) fun i j p => by
      have h := congrArg (fun s => integralSingularSimplexEquiv 1 X s p)
        (integralSingularConeFaces_compatible x σ i j)
      change (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ j (integralSingularConeFaces x σ i)) p =
        (TopCat.of X).toSSetObjEquiv _
          ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
            (integralSingularConeFaces x σ (i.succAbove j))) p at h
      rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply] at h
      exact h

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularConeBoundaryMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularConeBoundaryMap target :: scope.openDecls } }

def integralSingularConeSphereMap (x : X) (σ : integralSingularSimplex 2 X) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, X) :=
  (integralSingularConeBoundaryMap x σ).comp
    ⟨(DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin 3) ℝ).symm).symm,
      (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin 3) ℝ).symm).symm.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeSphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeSphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeSphereMap ``Submission.DifferentialGeometry.Topology.integralSingularConeSphereMap

theorem integralSingularConeSphereMap_simplexBoundarySphereChain
    (x : X) (σ : integralSingularSimplex 2 X) :
    (integralSingularChainMap
      ((integralSingularConeSphereMap x σ).comp ⟨ULift.down, continuous_uliftDown⟩)).f 2
      (simplexBoundarySphereChain.{u} 1) =
        (integralSingularTwoCycleProjection x (integralSimplexChain 2 σ)).val := by
  have h := integralSingularChainMap_boundarySphereDesc_simplexBoundarySphereChain 1
    (fun i => integralSingularSimplexEquiv 2 X (integralSingularConeFaces x σ i))
    (show ∀ (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)),
      integralSingularSimplexEquiv 2 X (integralSingularConeFaces x σ i)
          (stdSimplex.map j.succAbove p) =
        integralSingularSimplexEquiv 2 X
          (integralSingularConeFaces x σ (i.succAbove j))
          (stdSimplex.map (j.predAbove i).succAbove p) from by
      intro i j p
      have he := congrArg (fun s => integralSingularSimplexEquiv 1 X s p)
        (integralSingularConeFaces_compatible x σ i j)
      change (TopCat.of X).toSSetObjEquiv _
        ((TopCat.toSSet.obj (TopCat.of X)).δ j (integralSingularConeFaces x σ i)) p =
        (TopCat.of X).toSSetObjEquiv _
          ((TopCat.toSSet.obj (TopCat.of X)).δ (j.predAbove i)
            (integralSingularConeFaces x σ (i.succAbove j))) p at he
      rw [TopCat.toSSetObjEquiv_δ_apply, TopCat.toSSetObjEquiv_δ_apply] at he
      exact he)
  change (integralSingularChainMap
      ((integralSingularConeSphereMap x σ).comp ⟨ULift.down, continuous_uliftDown⟩)).f 2
      (simplexBoundarySphereChain 1) = _ at h
  rw [h, integralSingularTwoCycleProjection_simplex]
  change (∑ i : Fin 4, (-1 : ℤ) ^ i.val • integralSimplexChain 2
    (integralSingularConeFaces x σ i)) = _
  rw [Fin.sum_univ_four]
  norm_num
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeSphereMap_simplexBoundarySphereChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeSphereMap_simplexBoundarySphereChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeSphereMap_simplexBoundarySphereChain ``Submission.DifferentialGeometry.Topology.integralSingularConeSphereMap_simplexBoundarySphereChain

theorem integralSingularConeSphereMap_simplexBoundarySphereClass
    (x : X) (σ : integralSingularSimplex 2 X) :
    freeSphereHomologyImage 1 (simplexBoundarySphereClass.{u} 1)
      (ZerothHomotopy.mk (integralSingularConeSphereMap x σ)) =
        integralSingularCycleClass 1 X
          (integralSingularTwoCycleProjection x (integralSimplexChain 2 σ)) := by
  rw [freeSphereHomologyImage_mk, simplexBoundarySphereClass,
    integralSingularCycleClass_map]
  congr 1
  apply Subtype.ext
  rw [integralSingularCycleMap_val]
  exact integralSingularConeSphereMap_simplexBoundarySphereChain x σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeSphereMap_simplexBoundarySphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeSphereMap_simplexBoundarySphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeSphereMap_simplexBoundarySphereClass ``Submission.DifferentialGeometry.Topology.integralSingularConeSphereMap_simplexBoundarySphereClass

theorem span_range_freeSphereHomologyImage_two
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Submodule.span ℤ (Set.range (freeSphereHomologyImage (X := X) 1 c)) = ⊤ := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨k, hk⟩ := (isSphereHomologyGenerator_iff_forall_exists_zsmul 1 c).mp hc
    (simplexBoundarySphereClass.{u} 1)
  apply top_unique
  rw [← span_integralSingularTwoCycleProjection x]
  apply Submodule.span_le.mpr
  rintro y ⟨σ, rfl⟩
  change integralSingularCycleClass 1 X
      (integralSingularTwoCycleProjection x (integralSimplexChain 2 σ)) ∈ _
  rw [← integralSingularConeSphereMap_simplexBoundarySphereClass, hk,
    freeSphereHomologyImage_zsmul]
  have hm : freeSphereHomologyImage (X := X) 1 c
      (ZerothHomotopy.mk (integralSingularConeSphereMap x σ)) ∈
      Submodule.span ℤ (Set.range (freeSphereHomologyImage (X := X) 1 c)) :=
    Submodule.subset_span ⟨ZerothHomotopy.mk (integralSingularConeSphereMap x σ), rfl⟩
  exact zsmul_mem hm k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.span_range_freeSphereHomologyImage_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.span_range_freeSphereHomologyImage_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.span_range_freeSphereHomologyImage_two ``Submission.DifferentialGeometry.Topology.span_range_freeSphereHomologyImage_two

theorem span_range_sphereHurewicz_two (x : X)
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1))
    (hc : IsSphereHomologyGenerator 1 c) :
    Submodule.span ℤ (Set.range (sphereHurewicz 1 x c)) = ⊤ := by
  rw [sphereHurewicz,
    (homotopyGroupToFreeSphere_surjective 1 x).range_comp (freeSphereHomologyImage 1 c)]
  exact span_range_freeSphereHomologyImage_two c hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.span_range_sphereHurewicz_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.span_range_sphereHurewicz_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.span_range_sphereHurewicz_two ``Submission.DifferentialGeometry.Topology.span_range_sphereHurewicz_two

theorem integralSingularHomology_two_subsingleton_of_subsingleton_homotopyGroup
    (x : X) [Subsingleton (HomotopyGroup (Fin 2) X x)] :
    Subsingleton (integralSingularHomology 2 X) := by
  have hspan := span_range_sphereHurewicz_two x (integralLiftedSphereGenerator.{u} 1)
    (integralLiftedSphereGenerator_isGenerator 1)
  have hzero : Submodule.span ℤ
      (Set.range (sphereHurewicz 1 x (integralLiftedSphereGenerator.{u} 1))) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro y ⟨a, rfl⟩
    rw [Subsingleton.elim a 1, sphereHurewicz_one]
  have ht : (⊤ : Submodule ℤ (integralSingularHomology 2 X)) = ⊥ := hspan.symm.trans hzero
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have h : a ∈ (⊤ : Submodule ℤ (integralSingularHomology 2 X)) := Submodule.mem_top
    rwa [ht, Submodule.mem_bot] at h
  have hb : b = 0 := by
    have h : b ∈ (⊤ : Submodule ℤ (integralSingularHomology 2 X)) := Submodule.mem_top
    rwa [ht, Submodule.mem_bot] at h
  exact ha.trans hb.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomology_two_subsingleton_of_subsingleton_homotopyGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomology_two_subsingleton_of_subsingleton_homotopyGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomology_two_subsingleton_of_subsingleton_homotopyGroup ``Submission.DifferentialGeometry.Topology.integralSingularHomology_two_subsingleton_of_subsingleton_homotopyGroup

end DifferentialGeometry.Topology
