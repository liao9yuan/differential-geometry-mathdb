import Submission.DifferentialGeometry.Topology.Homology.Relative.Basic
import Submission.DifferentialGeometry.Topology.Homology.HurewiczTwoMultiplication
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Set _root_.Module
open scoped _root_.Simplicial _root_.Topology

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X] {Y : Type u} [TopologicalSpace Y]

def integralRelativeProjection (A : Set X) :
    integralSingularChains X ⟶ integralRelativeChains A :=
  cokernel.π (integralSingularChainMap (singularSubspaceInclusion A))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeProjection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeProjection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeProjection ``Submission.DifferentialGeometry.Topology.integralRelativeProjection

theorem integralRelativeProjection_condition (A : Set X) :
    integralSingularChainMap (singularSubspaceInclusion A) ≫ integralRelativeProjection A = 0 :=
  cokernel.condition _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeProjection_condition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeProjection_condition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeProjection_condition ``Submission.DifferentialGeometry.Topology.integralRelativeProjection_condition

def integralRelativeClassOf (n : ℕ) (A : Set X)
    (z : integralSingularCoefficients ⟶ (integralRelativeChains A).X (n + 1))
    (hz : z ≫ (integralRelativeChains A).d (n + 1) n = 0) :
    integralRelativeHomology (n + 1) A :=
  (((integralRelativeChains A).liftCycles z n ((ComplexShape.down ℕ).next_eq' (by rfl)) hz) ≫
    (integralRelativeChains A).homologyπ (n + 1)) (ULift.up 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeClassOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeClassOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeClassOf ``Submission.DifferentialGeometry.Topology.integralRelativeClassOf

theorem integralRelativeClassOf_congr (n : ℕ) (A : Set X)
    {z z' : integralSingularCoefficients ⟶ (integralRelativeChains A).X (n + 1)}
    {hz : z ≫ (integralRelativeChains A).d (n + 1) n = 0}
    {hz' : z' ≫ (integralRelativeChains A).d (n + 1) n = 0} (h : z = z') :
    integralRelativeClassOf n A z hz = integralRelativeClassOf n A z' hz' := by
  unfold integralRelativeClassOf
  cases h
  rw [Subsingleton.elim hz hz']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeClassOf_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeClassOf_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeClassOf_congr ``Submission.DifferentialGeometry.Topology.integralRelativeClassOf_congr

theorem integralRelativeConnecting_surjective_of_subsingleton (n : ℕ) (A : Set X)
    (h : Subsingleton (integralSingularHomology n X)) :
    Function.Surjective (integralRelativeConnecting n A) := by
  have hex := LinearMap.exact_iff.mp (integralRelative_exact_subspace n A)
  have hzero : integralSingularHomologyMap n (singularSubspaceInclusion A) = 0 :=
    LinearMap.ext fun x => Subsingleton.elim _ (0 : integralSingularHomology n X)
  rw [hzero, LinearMap.ker_zero] at hex
  exact LinearMap.range_eq_top.mp hex.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnecting_surjective_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnecting_surjective_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnecting_surjective_of_subsingleton ``Submission.DifferentialGeometry.Topology.integralRelativeConnecting_surjective_of_subsingleton

theorem integralRelativeConnecting_injective_of_subsingleton (n : ℕ) (A : Set X)
    (h : Subsingleton (integralSingularHomology (n + 1) X)) :
    Function.Injective (integralRelativeConnecting n A) := by
  have hex := LinearMap.exact_iff.mp (integralRelative_exact_relative n A)
  have hzero : integralAbsoluteToRelative (n + 1) A = 0 :=
    LinearMap.ext fun x => by
      simpa using congrArg (integralAbsoluteToRelative (n + 1) A) (Subsingleton.elim x 0)
  rw [hzero, LinearMap.range_zero] at hex
  exact LinearMap.ker_eq_bot.mp hex

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnecting_injective_of_subsingleton then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnecting_injective_of_subsingleton"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnecting_injective_of_subsingleton ``Submission.DifferentialGeometry.Topology.integralRelativeConnecting_injective_of_subsingleton

theorem integralAbsoluteToRelative_homologyClassOf (n : ℕ) (A : Set X)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 1))
    (hz : z ≫ (integralSingularChains X).d (n + 1) n = 0)
    (h : (z ≫ (integralRelativeProjection A).f (n + 1)) ≫
      (integralRelativeChains A).d (n + 1) n = 0) :
    integralAbsoluteToRelative (n + 1) A (integralHomologyClassOf n z hz) =
      integralRelativeClassOf n A (z ≫ (integralRelativeProjection A).f (n + 1)) h :=
  chainComplex_homologyMap_liftCycles_apply (integralRelativeProjection A) n z hz h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelative_homologyClassOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelative_homologyClassOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelative_homologyClassOf ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_homologyClassOf

theorem integralRelativeHomologyMap_liftCycles_apply (n : ℕ) (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B)
    (z : integralSingularCoefficients ⟶ (integralRelativeChains A).X (n + 1))
    (hz : z ≫ (integralRelativeChains A).d (n + 1) n = 0)
    (h : (z ≫ (integralRelativeChainMap f hf).f (n + 1)) ≫
      (integralRelativeChains B).d (n + 1) n = 0) :
    integralRelativeHomologyMap (n + 1) f hf (integralRelativeClassOf n A z hz) =
      integralRelativeClassOf n B (z ≫ (integralRelativeChainMap f hf).f (n + 1)) h :=
  chainComplex_homologyMap_liftCycles_apply (integralRelativeChainMap f hf) n z hz h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeHomologyMap_liftCycles_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeHomologyMap_liftCycles_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeHomologyMap_liftCycles_apply ``Submission.DifferentialGeometry.Topology.integralRelativeHomologyMap_liftCycles_apply

theorem integralRelativeConnecting_square_surjective :
    Function.Surjective (integralRelativeConnecting 1 (Cube.boundary (Fin 2))) :=
  integralRelativeConnecting_surjective_of_subsingleton 1 (Cube.boundary (Fin 2))
    (@integralSingularHomology_subsingleton_of_contractible 1 (by omega) Square _
      square_contractible)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnecting_square_surjective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnecting_square_surjective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnecting_square_surjective ``Submission.DifferentialGeometry.Topology.integralRelativeConnecting_square_surjective

theorem integralRelativeConnecting_square_injective :
    Function.Injective (integralRelativeConnecting 1 (Cube.boundary (Fin 2))) :=
  integralRelativeConnecting_injective_of_subsingleton 1 (Cube.boundary (Fin 2))
    (@integralSingularHomology_subsingleton_of_contractible 2 (by omega) Square _
      square_contractible)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnecting_square_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnecting_square_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnecting_square_injective ``Submission.DifferentialGeometry.Topology.integralRelativeConnecting_square_injective

theorem integralRelativeConnecting_square_bijective :
    Function.Bijective (integralRelativeConnecting 1 (Cube.boundary (Fin 2))) :=
  ⟨integralRelativeConnecting_square_injective, integralRelativeConnecting_square_surjective⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnecting_square_bijective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnecting_square_bijective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnecting_square_bijective ``Submission.DifferentialGeometry.Topology.integralRelativeConnecting_square_bijective

theorem integralRelativeChain_projection_boundary (n : ℕ) (A : Set X)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 2))
    (a : integralSingularCoefficients ⟶ (integralSingularChains A).X (n + 1))
    (ha : a ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 1) =
      z ≫ (integralSingularChains X).d (n + 2) (n + 1)) :
    (z ≫ (integralRelativeProjection A).f (n + 2)) ≫
      (integralRelativeChains A).d (n + 2) (n + 1) = 0 := by
  have hcond : (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 1) ≫
      (integralRelativeProjection A).f (n + 1) = 0 := by
    have h : ((integralSingularChainMap (singularSubspaceInclusion A) ≫
        integralRelativeProjection A).f (n + 1)) = 0 := by
      rw [integralRelativeProjection_condition, HomologicalComplex.zero_f]
    rwa [HomologicalComplex.comp_f] at h
  rw [Category.assoc, HomologicalComplex.Hom.comm, ← Category.assoc, ← ha, Category.assoc,
    hcond, Limits.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeChain_projection_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeChain_projection_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeChain_projection_boundary ``Submission.DifferentialGeometry.Topology.integralRelativeChain_projection_boundary

theorem squareSegmentChain_east_northEast_mem :
    squareSegmentChain squareEast squareNorthEast ∈
      integralSingularChainsIn 1 (Cube.boundary (Fin 2)) := by
  rw [squareSegmentChain]
  refine Submodule.subset_span ⟨squareAffineSimplex 1 ![squareEast, squareNorthEast], ?_, rfl⟩
  rintro x ⟨t, rfl⟩
  rw [squareAffineSimplex_coe]
  exact squareAffineMap_boundary_east_northEast t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareSegmentChain_east_northEast_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareSegmentChain_east_northEast_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareSegmentChain_east_northEast_mem ``Submission.DifferentialGeometry.Topology.squareSegmentChain_east_northEast_mem

theorem squareSegmentChain_origin_east_mem :
    squareSegmentChain squareOrigin squareEast ∈
      integralSingularChainsIn 1 (Cube.boundary (Fin 2)) := by
  rw [squareSegmentChain]
  refine Submodule.subset_span ⟨squareAffineSimplex 1 ![squareOrigin, squareEast], ?_, rfl⟩
  rintro x ⟨t, rfl⟩
  rw [squareAffineSimplex_coe]
  exact squareAffineMap_boundary_origin_east t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareSegmentChain_origin_east_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareSegmentChain_origin_east_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareSegmentChain_origin_east_mem ``Submission.DifferentialGeometry.Topology.squareSegmentChain_origin_east_mem

theorem squareSegmentChain_north_northEast_mem :
    squareSegmentChain squareNorth squareNorthEast ∈
      integralSingularChainsIn 1 (Cube.boundary (Fin 2)) := by
  rw [squareSegmentChain]
  refine Submodule.subset_span ⟨squareAffineSimplex 1 ![squareNorth, squareNorthEast], ?_, rfl⟩
  rintro x ⟨t, rfl⟩
  rw [squareAffineSimplex_coe]
  exact squareAffineMap_boundary_north_northEast t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareSegmentChain_north_northEast_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareSegmentChain_north_northEast_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareSegmentChain_north_northEast_mem ``Submission.DifferentialGeometry.Topology.squareSegmentChain_north_northEast_mem

theorem squareSegmentChain_origin_north_mem :
    squareSegmentChain squareOrigin squareNorth ∈
      integralSingularChainsIn 1 (Cube.boundary (Fin 2)) := by
  rw [squareSegmentChain]
  refine Submodule.subset_span ⟨squareAffineSimplex 1 ![squareOrigin, squareNorth], ?_, rfl⟩
  rintro x ⟨t, rfl⟩
  rw [squareAffineSimplex_coe]
  exact squareAffineMap_boundary_origin_north t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareSegmentChain_origin_north_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareSegmentChain_origin_north_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareSegmentChain_origin_north_mem ``Submission.DifferentialGeometry.Topology.squareSegmentChain_origin_north_mem

theorem squareFundamentalChain_boundary :
    (integralSingularChains Square).d 2 1 squareFundamentalChain =
      squareSegmentChain squareEast squareNorthEast + squareSegmentChain squareOrigin squareEast -
        squareSegmentChain squareNorth squareNorthEast -
          squareSegmentChain squareOrigin squareNorth := by
  rw [squareFundamentalChain, map_sub, squareTriangleChain_boundary, squareTriangleChain_boundary]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareFundamentalChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareFundamentalChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareFundamentalChain_boundary ``Submission.DifferentialGeometry.Topology.squareFundamentalChain_boundary

theorem squareFundamentalChain_boundary_mem :
    (integralSingularChains Square).d 2 1 squareFundamentalChain ∈
      integralSingularChainsIn 1 (Cube.boundary (Fin 2)) := by
  rw [squareFundamentalChain_boundary]
  exact sub_mem (sub_mem (_root_.AddMemClass.add_mem squareSegmentChain_east_northEast_mem
    squareSegmentChain_origin_east_mem) squareSegmentChain_north_northEast_mem)
    squareSegmentChain_origin_north_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareFundamentalChain_boundary_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareFundamentalChain_boundary_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareFundamentalChain_boundary_mem ``Submission.DifferentialGeometry.Topology.squareFundamentalChain_boundary_mem

def squareBoundaryLoopChain : (integralSingularChains (Cube.boundary (Fin 2))).X 1 :=
  integralSingularChainRestriction 1 (Cube.boundary (Fin 2))
    ⟨(integralSingularChains Square).d 2 1 squareFundamentalChain,
      squareFundamentalChain_boundary_mem⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareBoundaryLoopChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareBoundaryLoopChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareBoundaryLoopChain ``Submission.DifferentialGeometry.Topology.squareBoundaryLoopChain

theorem squareBoundaryLoopChain_inclusion :
    (integralSingularChainMap (singularSubspaceInclusion (Cube.boundary (Fin 2)))).f 1
        squareBoundaryLoopChain =
      (integralSingularChains Square).d 2 1 squareFundamentalChain :=
  integralSingularChainRestriction_inclusion 1 (Cube.boundary (Fin 2))
    ⟨(integralSingularChains Square).d 2 1 squareFundamentalChain,
      squareFundamentalChain_boundary_mem⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareBoundaryLoopChain_inclusion then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareBoundaryLoopChain_inclusion"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareBoundaryLoopChain_inclusion ``Submission.DifferentialGeometry.Topology.squareBoundaryLoopChain_inclusion

theorem squareBoundaryLoopChain_boundary :
    (integralSingularChains (Cube.boundary (Fin 2))).d 1 0 squareBoundaryLoopChain = 0 := by
  have hrest := integralSingularChainRestriction_boundary (X := Square)
    (A := Cube.boundary (Fin 2)) 0
    ⟨(integralSingularChains Square).d 2 1 squareFundamentalChain,
      squareFundamentalChain_boundary_mem⟩
  have hdd : (integralSingularChains Square).d 1 0
      ((integralSingularChains Square).d 2 1 squareFundamentalChain) = 0 := by
    have h := congrArg (fun f : (integralSingularChains Square).X 2 ⟶
      (integralSingularChains Square).X 0 => f squareFundamentalChain)
      ((integralSingularChains Square).d_comp_d 2 1 0)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  unfold squareBoundaryLoopChain
  refine hrest.symm.trans ?_
  have helem : (⟨(integralSingularChains Square).d 1 0
      ((integralSingularChains Square).d 2 1 squareFundamentalChain),
      integralSingularChainsIn_boundary 0 (Cube.boundary (Fin 2))
        squareFundamentalChain_boundary_mem⟩ :
      integralSingularChainsIn 0 (Cube.boundary (Fin 2))) = 0 :=
    Subtype.ext hdd
  rw [helem, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareBoundaryLoopChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareBoundaryLoopChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareBoundaryLoopChain_boundary ``Submission.DifferentialGeometry.Topology.squareBoundaryLoopChain_boundary

def squareBoundaryLoopClass : integralSingularHomology 1 (Cube.boundary (Fin 2)) :=
  integralHomologyClass 0 squareBoundaryLoopChain squareBoundaryLoopChain_boundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareBoundaryLoopClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareBoundaryLoopClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareBoundaryLoopClass ``Submission.DifferentialGeometry.Topology.squareBoundaryLoopClass

def squareFundamentalRelativeChain :
    integralSingularCoefficients ⟶ (integralRelativeChains (Cube.boundary (Fin 2))).X 2 :=
  integralChainHom 2 squareFundamentalChain ≫
    (integralRelativeProjection (Cube.boundary (Fin 2))).f 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareFundamentalRelativeChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareFundamentalRelativeChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareFundamentalRelativeChain ``Submission.DifferentialGeometry.Topology.squareFundamentalRelativeChain

theorem squareBoundaryLoopChain_inclusion_boundary :
    integralChainHom 1 squareBoundaryLoopChain ≫
        (integralSingularChainMap (singularSubspaceInclusion
          (Cube.boundary (Fin 2)))).f 1 =
      integralChainHom 2 squareFundamentalChain ≫ (integralSingularChains Square).d 2 1 := by
  rw [integralChainHom_comp_map, squareBoundaryLoopChain_inclusion, integralChainHom_d]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareBoundaryLoopChain_inclusion_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareBoundaryLoopChain_inclusion_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareBoundaryLoopChain_inclusion_boundary ``Submission.DifferentialGeometry.Topology.squareBoundaryLoopChain_inclusion_boundary

theorem squareFundamentalRelativeChain_boundary :
    squareFundamentalRelativeChain ≫
      (integralRelativeChains (Cube.boundary (Fin 2))).d 2 1 = 0 :=
  integralRelativeChain_projection_boundary 0 (Cube.boundary (Fin 2))
    (integralChainHom 2 squareFundamentalChain) (integralChainHom 1 squareBoundaryLoopChain)
    squareBoundaryLoopChain_inclusion_boundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareFundamentalRelativeChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareFundamentalRelativeChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareFundamentalRelativeChain_boundary ``Submission.DifferentialGeometry.Topology.squareFundamentalRelativeChain_boundary

def squareRelativeFundamentalClass :
    integralRelativeHomology 2 (Cube.boundary (Fin 2)) :=
  integralRelativeClassOf 1 (Cube.boundary (Fin 2)) squareFundamentalRelativeChain
    squareFundamentalRelativeChain_boundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareRelativeFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareRelativeFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareRelativeFundamentalClass ``Submission.DifferentialGeometry.Topology.squareRelativeFundamentalClass

theorem integralRelativeConnecting_squareRelativeFundamentalClass :
    integralRelativeConnecting 1 (Cube.boundary (Fin 2)) squareRelativeFundamentalClass =
      squareBoundaryLoopClass :=
  integralRelativeConnecting_liftCycles_apply 0 (Cube.boundary (Fin 2))
    (integralChainHom 2 squareFundamentalChain) squareFundamentalRelativeChain_boundary
    (integralChainHom 1 squareBoundaryLoopChain)
    (by rw [integralChainHom_d 0 squareBoundaryLoopChain, squareBoundaryLoopChain_boundary,
      integralChainHom_zero])
    squareBoundaryLoopChain_inclusion_boundary

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeConnecting_squareRelativeFundamentalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeConnecting_squareRelativeFundamentalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeConnecting_squareRelativeFundamentalClass ``Submission.DifferentialGeometry.Topology.integralRelativeConnecting_squareRelativeFundamentalClass

theorem integralRelativeProjection_chainMap (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) :
    integralRelativeProjection A ≫ integralRelativeChainMap f hf =
      integralSingularChainMap f ≫ integralRelativeProjection B :=
  integralRelativeChainMap_π f hf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeProjection_chainMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeProjection_chainMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeProjection_chainMap ``Submission.DifferentialGeometry.Topology.integralRelativeProjection_chainMap

theorem integralRelativeProjection_chainMap_component (n : ℕ) (f : C(X, Y))
    {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
    (integralRelativeProjection A).f n ≫ (integralRelativeChainMap f hf).f n =
      (integralSingularChainMap f).f n ≫ (integralRelativeProjection B).f n := by
  have h := congrArg (fun k : integralSingularChains X ⟶ integralRelativeChains B => k.f n)
    (integralRelativeProjection_chainMap f hf)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralRelativeProjection_chainMap_component then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralRelativeProjection_chainMap_component"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralRelativeProjection_chainMap_component ``Submission.DifferentialGeometry.Topology.integralRelativeProjection_chainMap_component

theorem integralAbsoluteToRelative_homologyClass (n : ℕ) (A : Set X)
    (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0)
    (h : (integralChainHom (n + 1) c ≫ (integralRelativeProjection A).f (n + 1)) ≫
      (integralRelativeChains A).d (n + 1) n = 0) :
    integralAbsoluteToRelative (n + 1) A (integralHomologyClass n c hc) =
      integralRelativeClassOf n A (integralChainHom (n + 1) c ≫
        (integralRelativeProjection A).f (n + 1)) h :=
  integralAbsoluteToRelative_homologyClassOf n A (integralChainHom (n + 1) c)
    (by rw [integralChainHom_d, hc, integralChainHom_zero]) h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralAbsoluteToRelative_homologyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralAbsoluteToRelative_homologyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralAbsoluteToRelative_homologyClass ``Submission.DifferentialGeometry.Topology.integralAbsoluteToRelative_homologyClass

theorem exists_linearMap_squareBoundaryLoopClass_iff_exists_linearMap_squareRelative :
    (∃ φ : integralSingularHomology 1 (Cube.boundary (Fin 2)) →ₗ[ℤ] ℤ,
        φ squareBoundaryLoopClass = 1) ↔
      (∃ ψ : integralRelativeHomology 2 (Cube.boundary (Fin 2)) →ₗ[ℤ] ℤ,
        ψ squareRelativeFundamentalClass = 1) := by
  refine ⟨fun ⟨φ, hφ⟩ =>
      ⟨φ.comp (integralRelativeConnecting 1 (Cube.boundary (Fin 2))), ?_⟩,
    fun ⟨ψ, hψ⟩ => ?_⟩
  · rw [LinearMap.comp_apply, integralRelativeConnecting_squareRelativeFundamentalClass, hφ]
  · refine ⟨ψ.comp (LinearEquiv.ofBijective
      (integralRelativeConnecting 1 (Cube.boundary (Fin 2)))
      integralRelativeConnecting_square_bijective).symm.toLinearMap, ?_⟩
    have hsymm : (LinearEquiv.ofBijective
        (integralRelativeConnecting 1 (Cube.boundary (Fin 2)))
        integralRelativeConnecting_square_bijective).symm squareBoundaryLoopClass =
        squareRelativeFundamentalClass := by
      rw [← integralRelativeConnecting_squareRelativeFundamentalClass]
      exact LinearEquiv.symm_apply_apply _ _
    exact (congrArg ψ hsymm).trans hψ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_linearMap_squareBoundaryLoopClass_iff_exists_linearMap_squareRelative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_linearMap_squareBoundaryLoopClass_iff_exists_linearMap_squareRelative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_linearMap_squareBoundaryLoopClass_iff_exists_linearMap_squareRelative ``Submission.DifferentialGeometry.Topology.exists_linearMap_squareBoundaryLoopClass_iff_exists_linearMap_squareRelative

theorem isUnit_of_exists_linearMap_eq_one {M : Type u} [AddCommGroup M] [Module ℤ M]
    (x : M) (h : ∃ φ : M →ₗ[ℤ] ℤ, φ x = 1) {k : ℤ} {y : M} (hy : x = k • y) :
    IsUnit k := by
  obtain ⟨φ, hφ⟩ := h
  have h2 : k * φ y = 1 := by
    have h3 : φ (k • y) = 1 := by
      rw [← hy]
      exact hφ
    rwa [map_zsmul, smul_eq_mul] at h3
  exact Int.isUnit_iff.mpr (Int.eq_one_or_neg_one_of_mul_eq_one h2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isUnit_of_exists_linearMap_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isUnit_of_exists_linearMap_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isUnit_of_exists_linearMap_eq_one ``Submission.DifferentialGeometry.Topology.isUnit_of_exists_linearMap_eq_one

theorem squareBoundaryLoopClass_ne_zero_of_exists_linearMap_eq_one
    (h : ∃ φ : integralSingularHomology 1 (Cube.boundary (Fin 2)) →ₗ[ℤ] ℤ,
      φ squareBoundaryLoopClass = 1) : squareBoundaryLoopClass ≠ 0 := by
  intro hzero
  obtain ⟨φ, hφ⟩ := h
  rw [hzero, map_zero] at hφ
  exact zero_ne_one hφ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareBoundaryLoopClass_ne_zero_of_exists_linearMap_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareBoundaryLoopClass_ne_zero_of_exists_linearMap_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareBoundaryLoopClass_ne_zero_of_exists_linearMap_eq_one ``Submission.DifferentialGeometry.Topology.squareBoundaryLoopClass_ne_zero_of_exists_linearMap_eq_one

theorem squareSphereCollapse_mapsTo :
    Set.MapsTo squareSphereCollapse (Cube.boundary (Fin 2))
      ({ULift.up (cubeSphereBasepoint 1)} : Set (liftedHomotopySphere.{u} 1)) :=
  fun t ht => squareSphereCollapse_boundary t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareSphereCollapse_mapsTo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareSphereCollapse_mapsTo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareSphereCollapse_mapsTo ``Submission.DifferentialGeometry.Topology.squareSphereCollapse_mapsTo

end DifferentialGeometry.Topology
