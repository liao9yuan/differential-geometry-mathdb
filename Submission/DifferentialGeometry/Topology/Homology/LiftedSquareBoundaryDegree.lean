import Submission.DifferentialGeometry.Topology.Homology.Relative.Basic
import Submission.DifferentialGeometry.Topology.Homology.SquareBoundaryDegree
import Submission.DifferentialGeometry.Topology.Homotopy.CubeCompactification

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial _root_.Topology

noncomputable section

universe u

namespace DifferentialGeometry.Topology

abbrev liftedSquare : Type u := ULift.{u} Square

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquare then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquare"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquare ``Submission.DifferentialGeometry.Topology.liftedSquare

def liftedSquareBoundary : Set (liftedSquare.{u}) := {x | x.down ∈ Cube.boundary (Fin 2)}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareBoundary ``Submission.DifferentialGeometry.Topology.liftedSquareBoundary

def liftedSquareUp : C(Square, liftedSquare.{u}) := ⟨ULift.up, continuous_uliftUp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareUp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareUp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareUp ``Submission.DifferentialGeometry.Topology.liftedSquareUp

def liftedSquareDown : C(liftedSquare.{u}, Square) := ⟨ULift.down, continuous_uliftDown⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareDown then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareDown"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareDown ``Submission.DifferentialGeometry.Topology.liftedSquareDown

def liftedSquareCollapse : C(liftedSquare.{u}, liftedHomotopySphere.{u} 1) :=
  ⟨fun x => squareSphereCollapse x.down,
    squareSphereCollapse.continuous.comp continuous_uliftDown⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareCollapse then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareCollapse"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareCollapse ``Submission.DifferentialGeometry.Topology.liftedSquareCollapse

theorem liftedSquareCollapse_apply (x : liftedSquare.{u}) :
    liftedSquareCollapse x = squareSphereCollapse x.down := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareCollapse_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareCollapse_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareCollapse_apply ``Submission.DifferentialGeometry.Topology.liftedSquareCollapse_apply

theorem liftedSquareDown_comp_up :
    liftedSquareDown.comp liftedSquareUp = ContinuousMap.id Square := by
  ext t
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareDown_comp_up then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareDown_comp_up"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareDown_comp_up ``Submission.DifferentialGeometry.Topology.liftedSquareDown_comp_up

theorem liftedSquareCollapse_comp_up :
    liftedSquareCollapse.comp liftedSquareUp = squareSphereCollapse := by
  ext t
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareCollapse_comp_up then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareCollapse_comp_up"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareCollapse_comp_up ``Submission.DifferentialGeometry.Topology.liftedSquareCollapse_comp_up

theorem liftedSquareCollapse_mapsTo :
    _root_.Set.MapsTo liftedSquareCollapse liftedSquareBoundary
      ({ULift.up (cubeSphereBasepoint 1)} : Set (liftedHomotopySphere.{u} 1)) :=
  fun x hx => squareSphereCollapse_boundary x.down hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareCollapse_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareCollapse_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareCollapse_mapsTo ``Submission.DifferentialGeometry.Topology.liftedSquareCollapse_mapsTo

def liftedSquareInclusion :
    C((Cube.boundary (Fin 2) : Set Square), (liftedSquareBoundary.{u} : Set (liftedSquare.{u}))) :=
  ⟨fun t => ⟨ULift.up t.val, t.property⟩, by
    apply Continuous.subtype_mk
    exact continuous_uliftUp.comp continuous_subtype_val⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareInclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareInclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareInclusion ``Submission.DifferentialGeometry.Topology.liftedSquareInclusion

theorem liftedSquareInclusion_inclusion :
    (singularSubspaceInclusion liftedSquareBoundary).comp liftedSquareInclusion =
      liftedSquareUp.comp (singularSubspaceInclusion (Cube.boundary (Fin 2))) := by
  ext t
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareInclusion_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareInclusion_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareInclusion_inclusion ``Submission.DifferentialGeometry.Topology.liftedSquareInclusion_inclusion

def liftedSquareFundamentalChain : (integralSingularChains (liftedSquare.{u})).X 2 :=
  singularChainImageGen 2 liftedSquareUp squareFundamentalChain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareFundamentalChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareFundamentalChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareFundamentalChain ``Submission.DifferentialGeometry.Topology.liftedSquareFundamentalChain

def liftedSquareBoundaryLoopChain :
    (integralSingularChains (liftedSquareBoundary.{u} : Set (liftedSquare.{u}))).X 1 :=
  singularChainImageGen 1 liftedSquareInclusion squareBoundaryLoopChain

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain ``Submission.DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain

theorem liftedSquareBoundaryLoopChain_inclusion :
    (integralSingularChainMap (singularSubspaceInclusion liftedSquareBoundary)).f 1
        liftedSquareBoundaryLoopChain =
      (integralSingularChains (liftedSquare.{u})).d 2 1 liftedSquareFundamentalChain := by
  have h1 : (singularChainImageGen 1 (singularSubspaceInclusion liftedSquareBoundary))
      ((singularChainImageGen 1 liftedSquareInclusion) squareBoundaryLoopChain) =
      (singularChainImageGen 1 ((singularSubspaceInclusion liftedSquareBoundary).comp
        liftedSquareInclusion)) squareBoundaryLoopChain := by
    simpa only [LinearMap.comp_apply] using
      (LinearMap.congr_fun (singularChainImageGen_comp 1 liftedSquareInclusion
        (singularSubspaceInclusion liftedSquareBoundary)) squareBoundaryLoopChain).symm
  have h2 : (singularChainImageGen 1 (liftedSquareUp.comp
        (singularSubspaceInclusion (Cube.boundary (Fin 2))))) squareBoundaryLoopChain =
      (singularChainImageGen 1 liftedSquareUp) ((singularChainImageGen 1
        (singularSubspaceInclusion (Cube.boundary (Fin 2)))) squareBoundaryLoopChain) := by
    simpa only [LinearMap.comp_apply] using
      LinearMap.congr_fun (singularChainImageGen_comp 1
        (singularSubspaceInclusion (Cube.boundary (Fin 2))) liftedSquareUp) squareBoundaryLoopChain
  rw [liftedSquareBoundaryLoopChain, liftedSquareFundamentalChain,
    integralSingularChainMap_apply_eq_singularChainImageGen, h1, liftedSquareInclusion_inclusion,
    h2, ← integralSingularChainMap_apply_eq_singularChainImageGen 1
      (singularSubspaceInclusion (Cube.boundary (Fin 2))) squareBoundaryLoopChain,
    squareBoundaryLoopChain_inclusion,
    ← singularChainImageGen_d_eq 1 liftedSquareUp squareFundamentalChain]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain_inclusion ``Submission.DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain_inclusion

theorem liftedSquareBoundaryLoopChain_boundary :
    (integralSingularChains (liftedSquareBoundary.{u} : Set (liftedSquare.{u}))).d 1 0
        liftedSquareBoundaryLoopChain = 0 := by
  have hdd : (integralSingularChains (liftedSquare.{u})).d 1 0
      ((integralSingularChains (liftedSquare.{u})).d 2 1 liftedSquareFundamentalChain) = 0 := by
    have h := congrArg (fun k : (integralSingularChains (liftedSquare.{u})).X 2 ⟶
      (integralSingularChains (liftedSquare.{u})).X 0 => k liftedSquareFundamentalChain)
      ((integralSingularChains (liftedSquare.{u})).d_comp_d 2 1 0)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  apply integralSingularChainInclusion_injective 0 liftedSquareBoundary
  rw [← integralSingularChainMap_d 0 (singularSubspaceInclusion liftedSquareBoundary)
    liftedSquareBoundaryLoopChain, liftedSquareBoundaryLoopChain_inclusion, hdd]
  exact (map_zero (ConcreteCategory.hom
    ((integralSingularChainMap (singularSubspaceInclusion liftedSquareBoundary)).f 0))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain_boundary ``Submission.DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain_boundary


def liftedSquareFundamentalRelativeChain :
    integralSingularCoefficients ⟶
      (integralRelativeChains (liftedSquareBoundary.{u} : Set (liftedSquare.{u}))).X 2 :=
  integralChainHom 2 liftedSquareFundamentalChain ≫
    (integralRelativeProjection liftedSquareBoundary).f 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareFundamentalRelativeChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareFundamentalRelativeChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareFundamentalRelativeChain ``Submission.DifferentialGeometry.Topology.liftedSquareFundamentalRelativeChain

theorem liftedSquareBoundaryLoopChain_inclusion_chainHom :
    integralChainHom 1 liftedSquareBoundaryLoopChain ≫
        (integralSingularChainMap (singularSubspaceInclusion liftedSquareBoundary)).f 1 =
      integralChainHom 2 liftedSquareFundamentalChain ≫
        (integralSingularChains (liftedSquare.{u})).d 2 1 := by
  rw [integralChainHom_comp_map, liftedSquareBoundaryLoopChain_inclusion, integralChainHom_d]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain_inclusion_chainHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain_inclusion_chainHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain_inclusion_chainHom ``Submission.DifferentialGeometry.Topology.liftedSquareBoundaryLoopChain_inclusion_chainHom

theorem liftedSquareFundamentalRelativeChain_boundary :
    liftedSquareFundamentalRelativeChain ≫
      (integralRelativeChains (liftedSquareBoundary.{u} : Set (liftedSquare.{u}))).d 2 1 = 0 :=
  integralRelativeChain_projection_boundary 0 liftedSquareBoundary
    (integralChainHom 2 liftedSquareFundamentalChain)
    (integralChainHom 1 liftedSquareBoundaryLoopChain)
    liftedSquareBoundaryLoopChain_inclusion_chainHom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareFundamentalRelativeChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareFundamentalRelativeChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareFundamentalRelativeChain_boundary ``Submission.DifferentialGeometry.Topology.liftedSquareFundamentalRelativeChain_boundary

def liftedSquareRelativeFundamentalClass :
    integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})) :=
  integralRelativeClassOf 1 liftedSquareBoundary liftedSquareFundamentalRelativeChain
    liftedSquareFundamentalRelativeChain_boundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareRelativeFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareRelativeFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareRelativeFundamentalClass ``Submission.DifferentialGeometry.Topology.liftedSquareRelativeFundamentalClass

def liftedSquareBoundaryLoopClass :
    integralSingularHomology 1 (liftedSquareBoundary.{u} : Set (liftedSquare.{u})) :=
  integralHomologyClass 0 liftedSquareBoundaryLoopChain liftedSquareBoundaryLoopChain_boundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareBoundaryLoopClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareBoundaryLoopClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareBoundaryLoopClass ``Submission.DifferentialGeometry.Topology.liftedSquareBoundaryLoopClass

theorem integralRelativeConnecting_liftedSquareRelativeFundamentalClass :
    integralRelativeConnecting 1 liftedSquareBoundary liftedSquareRelativeFundamentalClass =
      liftedSquareBoundaryLoopClass :=
  integralRelativeConnecting_liftCycles_apply 0 liftedSquareBoundary
    (integralChainHom 2 liftedSquareFundamentalChain) liftedSquareFundamentalRelativeChain_boundary
    (integralChainHom 1 liftedSquareBoundaryLoopChain)
    (by rw [integralChainHom_d 0 liftedSquareBoundaryLoopChain,
      liftedSquareBoundaryLoopChain_boundary, integralChainHom_zero])
    liftedSquareBoundaryLoopChain_inclusion_chainHom

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquareRelativeFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquareRelativeFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquareRelativeFundamentalClass ``Submission.DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquareRelativeFundamentalClass

theorem liftedSquare_contractibleSpace :
    ContractibleSpace (liftedSquare.{u}) :=
  letI := square_contractible
  (Homeomorph.ulift : liftedSquare.{u} ≃ₜ Square).contractibleSpace

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquare_contractibleSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquare_contractibleSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquare_contractibleSpace ``Submission.DifferentialGeometry.Topology.liftedSquare_contractibleSpace

theorem integralRelativeConnecting_liftedSquare_surjective :
    Function.Surjective (integralRelativeConnecting 1
      (liftedSquareBoundary.{u} : Set (liftedSquare.{u}))) := by
  have h : Subsingleton (integralSingularHomology 1 (liftedSquare.{u})) :=
    letI : ContractibleSpace (liftedSquare.{u}) := liftedSquare_contractibleSpace
    integralSingularHomology_subsingleton_of_contractible 1 (by omega) (liftedSquare.{u})
  exact integralRelativeConnecting_surjective_of_subsingleton 1 liftedSquareBoundary h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquare_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquare_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquare_surjective ``Submission.DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquare_surjective

theorem integralRelativeConnecting_liftedSquare_injective :
    Function.Injective (integralRelativeConnecting 1
      (liftedSquareBoundary.{u} : Set (liftedSquare.{u}))) := by
  have h : Subsingleton (integralSingularHomology 2 (liftedSquare.{u})) :=
    letI : ContractibleSpace (liftedSquare.{u}) := liftedSquare_contractibleSpace
    integralSingularHomology_subsingleton_of_contractible 2 (by omega) (liftedSquare.{u})
  exact integralRelativeConnecting_injective_of_subsingleton 1 liftedSquareBoundary h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquare_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquare_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquare_injective ``Submission.DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquare_injective

theorem integralRelativeConnecting_liftedSquare_bijective :
    Function.Bijective (integralRelativeConnecting 1
      (liftedSquareBoundary.{u} : Set (liftedSquare.{u}))) :=
  ⟨integralRelativeConnecting_liftedSquare_injective,
    integralRelativeConnecting_liftedSquare_surjective⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquare_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquare_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquare_bijective ``Submission.DifferentialGeometry.Topology.integralRelativeConnecting_liftedSquare_bijective

theorem exists_linearMap_liftedSquareBoundaryLoopClass_iff_exists_linearMap_liftedSquareRelative :
    (∃ φ : integralSingularHomology 1
        (liftedSquareBoundary.{u} : Set (liftedSquare.{u})) →ₗ[ℤ] ℤ,
        φ liftedSquareBoundaryLoopClass = 1) ↔
      (∃ ψ : integralRelativeHomology 2
        (liftedSquareBoundary.{u} : Set (liftedSquare.{u})) →ₗ[ℤ] ℤ,
        ψ liftedSquareRelativeFundamentalClass = 1) := by
  refine ⟨fun ⟨φ, hφ⟩ =>
      ⟨φ.comp (integralRelativeConnecting 1 liftedSquareBoundary), ?_⟩,
    fun ⟨ψ, hψ⟩ => ?_⟩
  · rw [LinearMap.comp_apply, integralRelativeConnecting_liftedSquareRelativeFundamentalClass, hφ]
  · refine ⟨ψ.comp (LinearEquiv.ofBijective
      (integralRelativeConnecting 1 liftedSquareBoundary)
      integralRelativeConnecting_liftedSquare_bijective).symm.toLinearMap, ?_⟩
    have hsymm : (LinearEquiv.ofBijective
        (integralRelativeConnecting 1 liftedSquareBoundary)
        integralRelativeConnecting_liftedSquare_bijective).symm liftedSquareBoundaryLoopClass =
        liftedSquareRelativeFundamentalClass := by
      rw [← integralRelativeConnecting_liftedSquareRelativeFundamentalClass]
      exact LinearEquiv.symm_apply_apply _ _
    exact (congrArg ψ hsymm).trans hψ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_linearMap_liftedSquareBoundaryLoopClass_iff_exists_linearMap_liftedSquareRelative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_linearMap_liftedSquareBoundaryLoopClass_iff_exists_linearMap_liftedSquareRelative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_linearMap_liftedSquareBoundaryLoopClass_iff_exists_linearMap_liftedSquareRelative ``Submission.DifferentialGeometry.Topology.exists_linearMap_liftedSquareBoundaryLoopClass_iff_exists_linearMap_liftedSquareRelative


abbrev liftedSphereBasepoint : Set (liftedHomotopySphere.{u} 1) :=
  {ULift.up (cubeSphereBasepoint 1)}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSphereBasepoint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSphereBasepoint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSphereBasepoint ``Submission.DifferentialGeometry.Topology.liftedSphereBasepoint

theorem liftedSquareCollapse_fundamentalChain :
    (integralSingularChainMap liftedSquareCollapse).f 2 liftedSquareFundamentalChain =
      squareSphereFundamentalChain := by
  rw [liftedSquareFundamentalChain, squareSphereFundamentalChain,
    integralSingularChainMap_apply_eq_singularChainImageGen, ← liftedSquareCollapse_comp_up,
    LinearMap.congr_fun (singularChainImageGen_comp 2 liftedSquareUp liftedSquareCollapse)
      squareFundamentalChain, LinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareCollapse_fundamentalChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareCollapse_fundamentalChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareCollapse_fundamentalChain ``Submission.DifferentialGeometry.Topology.liftedSquareCollapse_fundamentalChain

theorem integralRelativeHomologyMap_liftedSquareCollapse_liftedSquareRelativeFundamentalClass :
    integralRelativeHomologyMap 2 liftedSquareCollapse liftedSquareCollapse_mapsTo
        liftedSquareRelativeFundamentalClass =
      integralAbsoluteToRelative 2 (liftedSphereBasepoint.{u}) squareSphereFundamentalClass := by
  have hchain : (liftedSquareFundamentalRelativeChain ≫
      (integralRelativeChainMap liftedSquareCollapse liftedSquareCollapse_mapsTo).f 2) =
      integralChainHom 2 squareSphereFundamentalChain ≫
        (integralRelativeProjection (liftedSphereBasepoint.{u})).f 2 := by
    rw [liftedSquareFundamentalRelativeChain, Category.assoc,
      integralRelativeProjection_chainMap_component, ← Category.assoc, integralChainHom_comp_map,
      liftedSquareCollapse_fundamentalChain]
  have himg : (integralChainHom 2 squareSphereFundamentalChain ≫
      (integralRelativeProjection (liftedSphereBasepoint.{u})).f 2) ≫
      (integralRelativeChains (liftedSphereBasepoint.{u})).d 2 1 = 0 := by
    rw [← hchain, Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc,
      liftedSquareFundamentalRelativeChain_boundary, Limits.zero_comp]
  have key : integralRelativeHomologyMap 2 liftedSquareCollapse liftedSquareCollapse_mapsTo
      liftedSquareRelativeFundamentalClass =
      integralRelativeClassOf 1 (liftedSphereBasepoint.{u})
        (integralChainHom 2 squareSphereFundamentalChain ≫
          (integralRelativeProjection (liftedSphereBasepoint.{u})).f 2) himg :=
    (integralRelativeHomologyMap_liftCycles_apply 1 liftedSquareCollapse liftedSquareCollapse_mapsTo
        liftedSquareFundamentalRelativeChain liftedSquareFundamentalRelativeChain_boundary
        (by rw [hchain]; exact himg)).trans
      (integralRelativeClassOf_congr 1 (liftedSphereBasepoint.{u}) hchain)
  rw [key]
  exact (integralAbsoluteToRelative_homologyClass 1 (liftedSphereBasepoint.{u})
    squareSphereFundamentalChain squareSphereFundamentalChain_boundary himg).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedSquareCollapse_liftedSquareRelativeFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedSquareCollapse_liftedSquareRelativeFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedSquareCollapse_liftedSquareRelativeFundamentalClass ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_liftedSquareCollapse_liftedSquareRelativeFundamentalClass

theorem liftedSquareBoundaryLoopClass_ne_zero_of_exists_linearMap_eq_one
    (h : ∃ φ : integralSingularHomology 1 (liftedSquareBoundary.{u} : Set (liftedSquare.{u}))
      →ₗ[ℤ] ℤ, φ (liftedSquareBoundaryLoopClass.{u}) = 1) :
    liftedSquareBoundaryLoopClass.{u} ≠ 0 := by
  rintro hzero
  obtain ⟨φ, hφ⟩ := h
  refine (zero_ne_one (α := ℤ)).symm ?_
  exact hφ.symm.trans ((congrArg φ hzero).trans (map_zero φ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareBoundaryLoopClass_ne_zero_of_exists_linearMap_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareBoundaryLoopClass_ne_zero_of_exists_linearMap_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareBoundaryLoopClass_ne_zero_of_exists_linearMap_eq_one ``Submission.DifferentialGeometry.Topology.liftedSquareBoundaryLoopClass_ne_zero_of_exists_linearMap_eq_one

theorem liftedSquareRelativeFundamentalClass_ne_zero_of_exists_linearMap_eq_one
    (h : ∃ ψ : integralRelativeHomology 2 (liftedSquareBoundary.{u} : Set (liftedSquare.{u}))
      →ₗ[ℤ] ℤ, ψ (liftedSquareRelativeFundamentalClass.{u}) = 1) :
    liftedSquareRelativeFundamentalClass.{u} ≠ 0 := by
  rintro hzero
  obtain ⟨ψ, hψ⟩ := h
  refine (zero_ne_one (α := ℤ)).symm ?_
  exact hψ.symm.trans ((congrArg ψ hzero).trans (map_zero ψ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareRelativeFundamentalClass_ne_zero_of_exists_linearMap_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareRelativeFundamentalClass_ne_zero_of_exists_linearMap_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareRelativeFundamentalClass_ne_zero_of_exists_linearMap_eq_one ``Submission.DifferentialGeometry.Topology.liftedSquareRelativeFundamentalClass_ne_zero_of_exists_linearMap_eq_one

theorem squareAffineMap_vertex (n : ℕ) (v : Fin (n + 1) → Square) (j : Fin (n + 1)) :
    squareAffineMap n v (stdSimplex.vertex j) = v j := by
  funext i
  apply Subtype.ext
  rw [squareAffineMap_apply_coe]
  change ∑ k, (Pi.single j (1 : ℝ) : Fin (n + 1) → ℝ) k * (v k i : ℝ) = (v j i : ℝ)
  simp [Pi.single_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareAffineMap_vertex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareAffineMap_vertex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareAffineMap_vertex ``Submission.DifferentialGeometry.Topology.squareAffineMap_vertex

theorem squareAffineSimplex_eq_iff (n : ℕ) (v v' : Fin (n + 1) → Square) :
    squareAffineSimplex n v = squareAffineSimplex n v' ↔ v = v' := by
  constructor
  · intro h
    have h' : squareAffineMap n v = squareAffineMap n v' := by
      rw [← squareAffineSimplex_val, ← squareAffineSimplex_val, h]
    funext j
    rw [← squareAffineMap_vertex n v j, ← squareAffineMap_vertex n v' j, h']
  · intro h
    rw [h]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareAffineSimplex_eq_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareAffineSimplex_eq_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareAffineSimplex_eq_iff ``Submission.DifferentialGeometry.Topology.squareAffineSimplex_eq_iff

theorem squareEast_ne_squareNorth : squareEast ≠ squareNorth := by
  intro h
  have h0 := congrFun h 0
  simp [squareEast, squareNorth, squarePoint] at h0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareEast_ne_squareNorth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareEast_ne_squareNorth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareEast_ne_squareNorth ``Submission.DifferentialGeometry.Topology.squareEast_ne_squareNorth

theorem squareFundamentalChain_ne_zero : squareFundamentalChain ≠ 0 := by
  intro hzero
  have hrepr := congrArg (integralSingularChainRepr 2 Square) hzero
  rw [map_zero] at hrepr
  rw [squareFundamentalChain, map_sub, squareTriangleChain, squareTriangleChain,
    integralSingularChainRepr_simplex, integralSingularChainRepr_simplex] at hrepr
  have hne : squareAffineSimplex 2
        (![squareOrigin, squareEast, squareNorthEast] : Fin 3 → Square) ≠
      squareAffineSimplex 2
        (![squareOrigin, squareNorth, squareNorthEast] : Fin 3 → Square) := by
    intro h
    have hv := (squareAffineSimplex_eq_iff 2 _ _).mp h
    have h1 := congrFun hv 1
    exact squareEast_ne_squareNorth h1
  have hval := congrArg (fun f : integralSingularSimplex 2 Square →₀ ℤ =>
    f (squareAffineSimplex 2
      (![squareOrigin, squareEast, squareNorthEast] : Fin 3 → Square))) hrepr
  simp only [Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne,
    Finsupp.zero_apply, sub_zero] at hval
  exact one_ne_zero hval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareFundamentalChain_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareFundamentalChain_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareFundamentalChain_ne_zero ``Submission.DifferentialGeometry.Topology.squareFundamentalChain_ne_zero



theorem liftedSquareFundamentalChain_ne_zero : liftedSquareFundamentalChain.{u} ≠ 0 := by
  intro hzero
  have hzero' : (singularChainImageGen 2 (liftedSquareUp.{u}) squareFundamentalChain) = 0 :=
    hzero
  have hdown : (singularChainImageGen 2 (liftedSquareDown.{u}))
      (singularChainImageGen 2 (liftedSquareUp.{u}) squareFundamentalChain) = 0 := by
    rw [hzero', map_zero]
  have hcomp := LinearMap.congr_fun (singularChainImageGen_comp 2 (liftedSquareUp.{u})
    (liftedSquareDown.{u})) squareFundamentalChain
  rw [LinearMap.comp_apply] at hcomp
  rw [← hcomp, liftedSquareDown_comp_up, singularChainImageGen_eq_chainMap,
    integralSingularChainMap_id] at hdown
  exact squareFundamentalChain_ne_zero
    (by simpa only [HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_coe, id_eq] using hdown)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSquareFundamentalChain_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSquareFundamentalChain_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSquareFundamentalChain_ne_zero ``Submission.DifferentialGeometry.Topology.liftedSquareFundamentalChain_ne_zero

theorem isUnit_of_liftedSquareBoundaryLoopClass_eq_zsmul
    (h : ∃ φ : integralSingularHomology 1
      (liftedSquareBoundary.{u} : Set (liftedSquare.{u})) →ₗ[ℤ] ℤ,
      φ liftedSquareBoundaryLoopClass = 1)
    {k : ℤ} {z : integralSingularHomology 1
      (liftedSquareBoundary.{u} : Set (liftedSquare.{u}))}
    (hz : liftedSquareBoundaryLoopClass = k • z) : IsUnit k :=
  isUnit_of_exists_linearMap_eq_one liftedSquareBoundaryLoopClass h hz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isUnit_of_liftedSquareBoundaryLoopClass_eq_zsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isUnit_of_liftedSquareBoundaryLoopClass_eq_zsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isUnit_of_liftedSquareBoundaryLoopClass_eq_zsmul ``Submission.DifferentialGeometry.Topology.isUnit_of_liftedSquareBoundaryLoopClass_eq_zsmul

end DifferentialGeometry.Topology
