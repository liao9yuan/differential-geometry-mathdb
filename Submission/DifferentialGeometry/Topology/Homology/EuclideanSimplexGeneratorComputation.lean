import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.FundamentalClassMinimalHypotheses
import Submission.DifferentialGeometry.Topology.Homology.HurewiczTwoMultiplication

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Metric _root_.Submission.Metric _root_.Set _root_.Module
open scoped _root_.Topology _root_.Simplicial

namespace DifferentialGeometry.Topology

universe u

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

def liftedTetrahedronFace (i : Fin 4) : C(stdSimplex ℝ (Fin 3), stdSimplex ℝ (Fin 4)) :=
  ⟨stdSimplex.map (SimplexCategory.δ i).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ i).toOrderHom⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedTetrahedronFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedTetrahedronFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedTetrahedronFace ``Submission.DifferentialGeometry.Topology.liftedTetrahedronFace

theorem liftedTetrahedronFace_zero (i : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
    (liftedTetrahedronFace i q).val i = 0 := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (q : Fin 3 → ℝ) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact False.elim (Fin.succAbove_ne i j (Finset.mem_filter.mp hj).2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedTetrahedronFace_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedTetrahedronFace_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedTetrahedronFace_zero ``Submission.DifferentialGeometry.Topology.liftedTetrahedronFace_zero

def liftedTetrahedronSimplex : C(stdSimplex ℝ (Fin 4), liftedSphereSpace.{u} 1) where
  toFun q := (ULift.up (positiveTetrahedron q) : liftedSphereSpace.{u} 1)
  continuous_toFun :=
    (Homeomorph.ulift (X := ThreeSpace) :
        liftedSphereSpace.{u} 1 ≃ₜ ThreeSpace).symm.continuous.comp
      positiveTetrahedron.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedTetrahedronSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedTetrahedronSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedTetrahedronSimplex ``Submission.DifferentialGeometry.Topology.liftedTetrahedronSimplex

theorem liftedTetrahedronSimplex_face_ne_zero (i : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
    liftedTetrahedronSimplex (liftedTetrahedronFace i q) ≠ (0 : liftedSphereSpace.{u} 1) := by
  intro hh
  exact positiveTetrahedron_face_ne_zero (liftedTetrahedronFace i q) i
    (liftedTetrahedronFace_zero i q) (ULift.up_inj.mp hh)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedTetrahedronSimplex_face_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedTetrahedronSimplex_face_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedTetrahedronSimplex_face_ne_zero ``Submission.DifferentialGeometry.Topology.liftedTetrahedronSimplex_face_ne_zero

def euclideanStandardSimplexBoundaryChain :
    integralSingularCoefficients ⟶
      (integralSingularChains ({(0 : liftedSphereSpace.{u} 1)}ᶜ :
        Set (liftedSphereSpace.{u} 1))).X 2 :=
  puncturedSimplexBoundary (0 : liftedSphereSpace.{u} 1) liftedTetrahedronSimplex
    liftedTetrahedronSimplex_face_ne_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanStandardSimplexBoundaryChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanStandardSimplexBoundaryChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanStandardSimplexBoundaryChain ``Submission.DifferentialGeometry.Topology.euclideanStandardSimplexBoundaryChain

theorem euclideanStandardSimplexBoundaryChain_boundary :
    euclideanStandardSimplexBoundaryChain ≫
      (integralSingularChains ({(0 : liftedSphereSpace.{u} 1)}ᶜ :
        Set (liftedSphereSpace.{u} 1))).d 2 1 = 0 :=
  puncturedSimplexBoundary_boundary (0 : liftedSphereSpace.{u} 1) liftedTetrahedronSimplex
    liftedTetrahedronSimplex_face_ne_zero

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanStandardSimplexBoundaryChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanStandardSimplexBoundaryChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanStandardSimplexBoundaryChain_boundary ``Submission.DifferentialGeometry.Topology.euclideanStandardSimplexBoundaryChain_boundary

theorem euclideanStandardSimplexBoundaryClass_eq_classOf :
    integralHomologyClassOf 1 euclideanStandardSimplexBoundaryChain
        euclideanStandardSimplexBoundaryChain_boundary =
      euclideanStandardSimplexBoundaryClass.{u} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanStandardSimplexBoundaryClass_eq_classOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanStandardSimplexBoundaryClass_eq_classOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanStandardSimplexBoundaryClass_eq_classOf ``Submission.DifferentialGeometry.Topology.euclideanStandardSimplexBoundaryClass_eq_classOf

theorem euclideanStandardSimplexClass_eq_simplexLocalClass :
    simplexLocalClass (0 : liftedSphereSpace.{u} 1) liftedTetrahedronSimplex
        liftedTetrahedronSimplex_face_ne_zero =
      euclideanStandardSimplexClass.{u} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanStandardSimplexClass_eq_simplexLocalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanStandardSimplexClass_eq_simplexLocalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanStandardSimplexClass_eq_simplexLocalClass ``Submission.DifferentialGeometry.Topology.euclideanStandardSimplexClass_eq_simplexLocalClass

def liftedSimplexBoundarySphereMap :
    C(({(0 : liftedSphereSpace.{u} 1)}ᶜ : Set (liftedSphereSpace.{u} 1)),
      liftedHomotopySphere.{u} 1) :=
  (liftedSphereHomeomorph.{u} 1).toHomotopyEquiv.invFun.comp
    (puncturedSpaceSphereHomotopyEquiv (liftedSphereSpace.{u} 1)).toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSimplexBoundarySphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSimplexBoundarySphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSimplexBoundarySphereMap ``Submission.DifferentialGeometry.Topology.liftedSimplexBoundarySphereMap

def simplexBoundaryLiftedChain :
    integralSingularCoefficients ⟶
      (integralSingularChains (liftedHomotopySphere.{u} 1)).X 2 :=
  euclideanStandardSimplexBoundaryChain ≫
    (integralSingularChainMap liftedSimplexBoundarySphereMap).f 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexBoundaryLiftedChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexBoundaryLiftedChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexBoundaryLiftedChain ``Submission.DifferentialGeometry.Topology.simplexBoundaryLiftedChain

theorem simplexBoundaryLiftedChain_boundary :
    simplexBoundaryLiftedChain ≫
      (integralSingularChains (liftedHomotopySphere.{u} 1)).d 2 1 = 0 := by
  rw [simplexBoundaryLiftedChain, Category.assoc,
    (integralSingularChainMap liftedSimplexBoundarySphereMap).comm 2 1, ← Category.assoc,
    euclideanStandardSimplexBoundaryChain_boundary, Limits.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexBoundaryLiftedChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexBoundaryLiftedChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexBoundaryLiftedChain_boundary ``Submission.DifferentialGeometry.Topology.simplexBoundaryLiftedChain_boundary

theorem euclideanStandardSimplexBoundarySphereClass_eq_map :
    euclideanStandardSimplexBoundarySphereClass.{u} =
      integralSingularHomologyMap 2 liftedSimplexBoundarySphereMap
        euclideanStandardSimplexBoundaryClass.{u} := by
  unfold euclideanStandardSimplexBoundarySphereClass
  rw [show integralSingularHomologyMap 2 liftedSimplexBoundarySphereMap =
      (integralSingularHomologyMap 2
        (liftedSphereHomeomorph.{u} 1).toHomotopyEquiv.invFun).comp
      (integralSingularHomologyMap 2
        (puncturedSpaceSphereHomotopyEquiv (liftedSphereSpace.{u} 1)).toFun)
      from integralSingularHomologyMap_comp 2
        (puncturedSpaceSphereHomotopyEquiv (liftedSphereSpace.{u} 1)).toFun
        (liftedSphereHomeomorph.{u} 1).toHomotopyEquiv.invFun]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_eq_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_eq_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_eq_map ``Submission.DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_eq_map

theorem euclideanStandardSimplexBoundarySphereClass_eq_classOf :
    integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      euclideanStandardSimplexBoundarySphereClass.{u} := by
  rw [euclideanStandardSimplexBoundarySphereClass_eq_map,
    ← euclideanStandardSimplexBoundaryClass_eq_classOf,
    integralSingularHomologyMap_integralHomologyClassOf]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_eq_classOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_eq_classOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_eq_classOf ``Submission.DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_eq_classOf

theorem integralChainHom_squareSphereFundamentalChain_boundary :
    integralChainHom 2 squareSphereFundamentalChain ≫
      (integralSingularChains (liftedHomotopySphere.{u} 1)).d 2 1 = 0 := by
  rw [integralChainHom_d 1 squareSphereFundamentalChain, squareSphereFundamentalChain_boundary,
    integralChainHom_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralChainHom_squareSphereFundamentalChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralChainHom_squareSphereFundamentalChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralChainHom_squareSphereFundamentalChain_boundary ``Submission.DifferentialGeometry.Topology.integralChainHom_squareSphereFundamentalChain_boundary

theorem squareSphereFundamentalClass_eq_classOf :
    integralHomologyClassOf 1 (integralChainHom 2 squareSphereFundamentalChain)
        integralChainHom_squareSphereFundamentalChain_boundary =
      squareSphereFundamentalClass.{u} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.squareSphereFundamentalClass_eq_classOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.squareSphereFundamentalClass_eq_classOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.squareSphereFundamentalClass_eq_classOf ``Submission.DifferentialGeometry.Topology.squareSphereFundamentalClass_eq_classOf

def SimplexBoundarySphereAlignment : Prop :=
  integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      squareSphereFundamentalClass.{u} ∨
    integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      -squareSphereFundamentalClass.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexBoundarySphereAlignment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexBoundarySphereAlignment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexBoundarySphereAlignment ``Submission.DifferentialGeometry.Topology.SimplexBoundarySphereAlignment

def SimplexBoundarySphereFilling : Prop :=
  ∃ z : integralSingularCoefficients ⟶
      (integralSingularChains (liftedHomotopySphere.{u} 1)).X 3,
    (z ≫ (integralSingularChains (liftedHomotopySphere.{u} 1)).d 3 2 =
        simplexBoundaryLiftedChain - integralChainHom 2 squareSphereFundamentalChain) ∨
      (z ≫ (integralSingularChains (liftedHomotopySphere.{u} 1)).d 3 2 =
        integralChainHom 2 squareSphereFundamentalChain - simplexBoundaryLiftedChain)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexBoundarySphereFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexBoundarySphereFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexBoundarySphereFilling ``Submission.DifferentialGeometry.Topology.SimplexBoundarySphereFilling

theorem simplexBoundarySphereAlignment_of_filling (h : SimplexBoundarySphereFilling.{u}) :
    SimplexBoundarySphereAlignment.{u} := by
  obtain ⟨z, hz | hz⟩ := h
  · left
    refine (integralHomologyClassOf_eq_of_sub_eq 1 simplexBoundaryLiftedChain
      (integralChainHom 2 squareSphereFundamentalChain) simplexBoundaryLiftedChain_boundary
      integralChainHom_squareSphereFundamentalChain_boundary z hz.symm).trans ?_
    exact squareSphereFundamentalClass_eq_classOf.symm
  · left
    exact (integralHomologyClassOf_eq_of_sub_eq 1
      (integralChainHom 2 squareSphereFundamentalChain) simplexBoundaryLiftedChain
      integralChainHom_squareSphereFundamentalChain_boundary simplexBoundaryLiftedChain_boundary
      z hz.symm).symm.trans squareSphereFundamentalClass_eq_classOf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexBoundarySphereAlignment_of_filling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexBoundarySphereAlignment_of_filling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexBoundarySphereAlignment_of_filling ``Submission.DifferentialGeometry.Topology.simplexBoundarySphereAlignment_of_filling

theorem isSphereHomologyGenerator_neg (n : ℕ)
    {c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)}
    (h : IsSphereHomologyGenerator n c) : IsSphereHomologyGenerator n (-c) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.trans (LinearEquiv.neg ℤ), ?_⟩
  simp [LinearEquiv.trans_apply, he]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_neg ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_neg

theorem isSphereHomologyGenerator_of_simplexBoundarySphereAlignment
    (halign : SimplexBoundarySphereAlignment.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    IsSphereHomologyGenerator.{u} 1 euclideanStandardSimplexBoundarySphereClass.{u} := by
  rw [← euclideanStandardSimplexBoundarySphereClass_eq_classOf]
  rcases halign with h | h
  · rwa [h]
  · rw [h]
    exact isSphereHomologyGenerator_neg 1 hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_of_simplexBoundarySphereAlignment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_of_simplexBoundarySphereAlignment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_of_simplexBoundarySphereAlignment ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_of_simplexBoundarySphereAlignment

theorem euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereAlignment
    (halign : SimplexBoundarySphereAlignment.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    euclideanStandardSimplexClassGenerator.{u} :=
  euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator.mpr
    (isSphereHomologyGenerator_of_simplexBoundarySphereAlignment halign hg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereAlignment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereAlignment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereAlignment ``Submission.DifferentialGeometry.Topology.euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereAlignment

theorem euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereFilling
    (h : SimplexBoundarySphereFilling.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    euclideanStandardSimplexClassGenerator.{u} :=
  euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereAlignment
    (simplexBoundarySphereAlignment_of_filling h) hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereFilling ``Submission.DifferentialGeometry.Topology.euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereFilling

theorem simplexBoundarySphereAlignment_of_euclideanStandardSimplexClassGenerator
    (h : euclideanStandardSimplexClassGenerator.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    SimplexBoundarySphereAlignment.{u} := by
  have hc := euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator.mp h
  rw [← euclideanStandardSimplexBoundarySphereClass_eq_classOf] at hc
  rcases IsSphereHomologyGenerator.eq_or_eq_neg 1 hc hg with h' | h'
  · exact Or.inl h'
  · exact Or.inr h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.simplexBoundarySphereAlignment_of_euclideanStandardSimplexClassGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.simplexBoundarySphereAlignment_of_euclideanStandardSimplexClassGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.simplexBoundarySphereAlignment_of_euclideanStandardSimplexClassGenerator ``Submission.DifferentialGeometry.Topology.simplexBoundarySphereAlignment_of_euclideanStandardSimplexClassGenerator

theorem euclideanStandardSimplexClassGenerator_iff_simplexBoundarySphereAlignment
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    euclideanStandardSimplexClassGenerator.{u} ↔ SimplexBoundarySphereAlignment.{u} :=
  ⟨fun h => simplexBoundarySphereAlignment_of_euclideanStandardSimplexClassGenerator h hg,
    fun h => euclideanStandardSimplexClassGenerator_of_simplexBoundarySphereAlignment h hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanStandardSimplexClassGenerator_iff_simplexBoundarySphereAlignment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanStandardSimplexClassGenerator_iff_simplexBoundarySphereAlignment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanStandardSimplexClassGenerator_iff_simplexBoundarySphereAlignment ``Submission.DifferentialGeometry.Topology.euclideanStandardSimplexClassGenerator_iff_simplexBoundarySphereAlignment

theorem euclideanStandardSimplexBoundarySphereClass_ne_zero_of_simplexBoundarySphereFilling
    (h : SimplexBoundarySphereFilling.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    euclideanStandardSimplexBoundarySphereClass.{u} ≠ 0 :=
  IsSphereHomologyGenerator.ne_zero 1
    (isSphereHomologyGenerator_of_simplexBoundarySphereAlignment
      (simplexBoundarySphereAlignment_of_filling h) hg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_ne_zero_of_simplexBoundarySphereFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_ne_zero_of_simplexBoundarySphereFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_ne_zero_of_simplexBoundarySphereFilling ``Submission.DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_ne_zero_of_simplexBoundarySphereFilling

theorem euclideanStandardSimplexBoundarySphereClass_eq_zero_iff_of_simplexBoundarySphereFilling
    (h : SimplexBoundarySphereFilling.{u}) :
    euclideanStandardSimplexBoundarySphereClass.{u} = 0 ↔
      squareSphereFundamentalClass.{u} = 0 := by
  have halign := simplexBoundarySphereAlignment_of_filling h
  rw [← euclideanStandardSimplexBoundarySphereClass_eq_classOf]
  rcases halign with h' | h'
  · rw [h']
  · rw [h', neg_eq_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_eq_zero_iff_of_simplexBoundarySphereFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_eq_zero_iff_of_simplexBoundarySphereFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_eq_zero_iff_of_simplexBoundarySphereFilling ``Submission.DifferentialGeometry.Topology.euclideanStandardSimplexBoundarySphereClass_eq_zero_iff_of_simplexBoundarySphereFilling

theorem not_simplexBoundarySphereAlignment_two_zsmul
    (halign : SimplexBoundarySphereAlignment.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    ¬ (integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
          (2 : ℤ) • squareSphereFundamentalClass.{u} ∨
        integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
          -((2 : ℤ) • squareSphereFundamentalClass.{u})) := by
  obtain ⟨e, he⟩ := hg
  have h2 : e ((2 : ℤ) • squareSphereFundamentalClass.{u}) = 2 := by
    have h : e.toLinearMap ((2 : ℤ) • squareSphereFundamentalClass.{u}) =
        2 • e.toLinearMap squareSphereFundamentalClass.{u} :=
      map_zsmul e.toLinearMap (2 : ℤ) squareSphereFundamentalClass.{u}
    have hone : e.toLinearMap squareSphereFundamentalClass.{u} = 1 := he
    rw [hone] at h
    simpa using h
  have hc : e (integralHomologyClassOf 1 simplexBoundaryLiftedChain
        simplexBoundaryLiftedChain_boundary) = 1 ∨
      e (integralHomologyClassOf 1 simplexBoundaryLiftedChain
        simplexBoundaryLiftedChain_boundary) = -1 := by
    rcases halign with h | h
    · left
      rw [h, he]
    · right
      rw [h, map_neg, he]
  rintro (h | h)
  · rw [h, h2] at hc
    omega
  · rw [h, map_neg, h2] at hc
    omega

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.not_simplexBoundarySphereAlignment_two_zsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.not_simplexBoundarySphereAlignment_two_zsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.not_simplexBoundarySphereAlignment_two_zsmul ``Submission.DifferentialGeometry.Topology.not_simplexBoundarySphereAlignment_two_zsmul

end DifferentialGeometry.Topology
