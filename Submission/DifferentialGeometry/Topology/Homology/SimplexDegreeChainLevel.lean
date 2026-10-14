import Submission.DifferentialGeometry.Topology.Homology.Relative.Basic
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChartSimplexBlend
import Submission.DifferentialGeometry.Topology.Homology.EuclideanLocalTop
import Submission.DifferentialGeometry.Topology.Homology.HurewiczTwoMultiplication
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyClasses
import Submission.DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology _root_.ContinuousMap _root_.Metric _root_.Set _root_.Module
open scoped _root_.Simplicial _root_.Topology

namespace DifferentialGeometry.Topology

namespace SimplexDegree

universe u

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

def orientedSimplexFace (i : Fin 4) :
    C(stdSimplex ℝ (Fin 3), stdSimplex ℝ (Fin 4)) :=
  ⟨stdSimplex.map (SimplexCategory.δ i).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ i).toOrderHom⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.orientedSimplexFace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.orientedSimplexFace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.orientedSimplexFace ``Submission.DifferentialGeometry.Topology.SimplexDegree.orientedSimplexFace

private theorem orientedSimplexFace_zero (i : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
    (orientedSimplexFace i q).val i = 0 := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (q : Fin 3 → ℝ) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact False.elim (Fin.succAbove_ne i j (Finset.mem_filter.mp hj).2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.orientedSimplexFace_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.orientedSimplexFace_zero target :: scope.openDecls } }

def integralSimplexChain {X : Type u} [TopologicalSpace X] (n : ℕ)
    (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    integralSingularCoefficients ⟶ (integralSingularChains X).X n :=
  (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).symm σ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralSimplexChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralSimplexChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralSimplexChain ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralSimplexChain

private def puncturedFace {X : Type u} [TopologicalSpace X] (p : X)
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p)
    (i : Fin 4) : C(stdSimplex ℝ (Fin 3), ({p}ᶜ : Set X)) :=
  ⟨fun q => ⟨σ (orientedSimplexFace i q), hσ i q⟩,
    (σ.continuous.comp (orientedSimplexFace i).continuous).subtype_mk _⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedFace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.puncturedFace target :: scope.openDecls } }

private theorem puncturedFace_chain {X : Type u} [TopologicalSpace X] (p : X)
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p)
    (i : Fin 4) :
    integralSimplexChain 2 (puncturedFace p σ hσ i) ≫
      (integralSingularChainMap (singularSubspaceInclusion ({(p : X)}ᶜ : Set X))).f 2 =
        integralSimplexChain 2 (σ.comp (orientedSimplexFace i)) :=
  SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of ({p}ᶜ : Set X)))
    (TopCat.toSSet.obj (TopCat.of X))
    (TopCat.toSSet.map (TopCat.ofHom (singularSubspaceInclusion ({(p : X)}ᶜ : Set X))))
    integralSingularCoefficients
    ((TopCat.toSSetObjEquiv (TopCat.of ({p}ᶜ : Set X)) (.op ⦋2⦌)).symm
      (puncturedFace p σ hσ i))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedFace_chain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.puncturedFace_chain target :: scope.openDecls } }

private theorem simplexChain_boundary {X : Type u} [TopologicalSpace X]
    (σ : C(stdSimplex ℝ (Fin 4), X)) :
    integralSimplexChain 3 σ ≫ (integralSingularChains X).d 3 2 =
      ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
        integralSimplexChain 2 (σ.comp (orientedSimplexFace i)) :=
  (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d (R := integralSingularCoefficients)
    ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋3⦌)).symm σ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexChain_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.simplexChain_boundary target :: scope.openDecls } }

private theorem relativeChain_boundary {X : Type u} [TopologicalSpace X] (p : X)
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p) :
    (integralSimplexChain 3 σ ≫ (cokernel.π (integralSingularChainMap
      (singularSubspaceInclusion ({(p : X)}ᶜ : Set X)))).f 3) ≫
      (integralRelativeChains ({(p : X)}ᶜ : Set X)).d 3 2 = 0 := by
  let quotientMap := cokernel.π (integralSingularChainMap
    (singularSubspaceInclusion ({(p : X)}ᶜ : Set X)))
  have hπ : (integralSingularChainMap (singularSubspaceInclusion ({(p : X)}ᶜ : Set X))).f 2 ≫
      quotientMap.f 2 = 0 :=
    congrArg (fun f => f.f 2) (cokernel.condition
      (integralSingularChainMap (singularSubspaceInclusion ({(p : X)}ᶜ : Set X))))
  have hf (i : Fin 4) :
      integralSimplexChain 2 (σ.comp (orientedSimplexFace i)) ≫ quotientMap.f 2 = 0 := by
    rw [← puncturedFace_chain p σ hσ i, Category.assoc, hπ, Limits.comp_zero]
  change (integralSimplexChain 3 σ ≫ quotientMap.f 3) ≫ (_root_.CategoryTheory.Limits.cokernel (integralSingularChainMap
    (singularSubspaceInclusion ({(p : X)}ᶜ : Set X)))).d 3 2 = 0
  rw [Category.assoc, quotientMap.comm 3 2, ← Category.assoc, simplexChain_boundary]
  simp only [Preadditive.sum_comp, Linear.smul_comp, hf, smul_zero, Finset.sum_const_zero]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.SimplexDegree.relativeChain_boundary
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.SimplexDegree.relativeChain_boundary target :: scope.openDecls } }

def simplexLocalClass {X : Type u} [TopologicalSpace X] (p : X)
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p) :
    integralLocalHomology 3 p :=
  ((integralRelativeChains ({(p : X)}ᶜ : Set X)).liftCycles
      (integralSimplexChain 3 σ ≫ (cokernel.π (integralSingularChainMap
        (singularSubspaceInclusion ({(p : X)}ᶜ : Set X)))).f 3) 2
      ((ComplexShape.down ℕ).next_eq' (by rfl))
      (relativeChain_boundary p σ hσ) ≫
    (integralRelativeChains ({(p : X)}ᶜ : Set X)).homologyπ 3) (ULift.up 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.simplexLocalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.simplexLocalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.simplexLocalClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexLocalClass

def standardTetrahedronSimplex :
    C(stdSimplex ℝ (Fin 4), liftedSphereSpace.{u} 1) where
  toFun q := (ULift.up (positiveTetrahedron q) : liftedSphereSpace.{u} 1)
  continuous_toFun :=
    (Homeomorph.ulift (X := ThreeSpace) :
        liftedSphereSpace.{u} 1 ≃ₜ ThreeSpace).symm.continuous.comp
      positiveTetrahedron.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.standardTetrahedronSimplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.standardTetrahedronSimplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.standardTetrahedronSimplex ``Submission.DifferentialGeometry.Topology.SimplexDegree.standardTetrahedronSimplex

theorem standardTetrahedronSimplex_face_ne_zero (i : Fin 4)
    (q : stdSimplex ℝ (Fin 3)) :
    standardTetrahedronSimplex (orientedSimplexFace i q) ≠
      (0 : liftedSphereSpace.{u} 1) := by
  intro hh
  exact positiveTetrahedron_face_ne_zero (orientedSimplexFace i q) i
    (orientedSimplexFace_zero i q) (ULift.up_inj.mp hh)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.standardTetrahedronSimplex_face_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.standardTetrahedronSimplex_face_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.standardTetrahedronSimplex_face_ne_zero ``Submission.DifferentialGeometry.Topology.SimplexDegree.standardTetrahedronSimplex_face_ne_zero

def euclideanStandardSimplexClass :
    integralLocalHomology 3 (0 : liftedSphereSpace.{u} 1) :=
  simplexLocalClass (0 : liftedSphereSpace.{u} 1) standardTetrahedronSimplex
    (fun i q => standardTetrahedronSimplex_face_ne_zero i q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass

def puncturedSimplexBoundary {X : Type u} [TopologicalSpace X] (p : X)
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p) :
    integralSingularCoefficients ⟶ (integralSingularChains ({(p : X)}ᶜ : Set X)).X 2 :=
  ∑ i : Fin 4, (-1 : ℤ) ^ i.val • integralSimplexChain 2 (puncturedFace p σ hσ i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedSimplexBoundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedSimplexBoundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedSimplexBoundary ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedSimplexBoundary

theorem puncturedSimplexBoundary_chain {X : Type u} [TopologicalSpace X] (p : X)
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p) :
    puncturedSimplexBoundary p σ hσ ≫
        (integralSingularChainMap (singularSubspaceInclusion ({(p : X)}ᶜ : Set X))).f 2 =
      integralSimplexChain 3 σ ≫ (integralSingularChains X).d 3 2 := by
  rw [puncturedSimplexBoundary, Preadditive.sum_comp]
  rw [Finset.sum_congr rfl (fun i _ => by
    rw [Linear.smul_comp, puncturedFace_chain p σ hσ i])]
  rw [← simplexChain_boundary σ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedSimplexBoundary_chain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedSimplexBoundary_chain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedSimplexBoundary_chain ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedSimplexBoundary_chain

theorem puncturedSimplexBoundary_boundary {X : Type u} [TopologicalSpace X] (p : X)
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p) :
    puncturedSimplexBoundary p σ hσ ≫
      (integralSingularChains ({(p : X)}ᶜ : Set X)).d 2 1 = 0 := by
  rw [← _root_.CategoryTheory.cancel_mono
    ((integralSingularChainMap (singularSubspaceInclusion ({(p : X)}ᶜ : Set X))).f 1)]
  rw [Limits.zero_comp, Category.assoc,
    ← (integralSingularChainMap (singularSubspaceInclusion ({(p : X)}ᶜ : Set X))).comm 2 1,
    ← Category.assoc, puncturedSimplexBoundary_chain p σ hσ, Category.assoc,
    HomologicalComplex.d_comp_d, Limits.comp_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.puncturedSimplexBoundary_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.puncturedSimplexBoundary_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.puncturedSimplexBoundary_boundary ``Submission.DifferentialGeometry.Topology.SimplexDegree.puncturedSimplexBoundary_boundary

theorem integralRelativeConnecting_simplexLocalClass {X : Type u} [TopologicalSpace X] (p : X)
    (σ : C(stdSimplex ℝ (Fin 4), X))
    (hσ : ∀ (i : Fin 4) (q : stdSimplex ℝ (Fin 3)), σ (orientedSimplexFace i q) ≠ p) :
    integralRelativeConnecting 2 ({(p : X)}ᶜ : Set X) (simplexLocalClass p σ hσ) =
      (((integralSingularChains ({(p : X)}ᶜ : Set X)).liftCycles
        (puncturedSimplexBoundary p σ hσ) 1 ((ComplexShape.down ℕ).next_eq' (by rfl))
        (puncturedSimplexBoundary_boundary p σ hσ)) ≫
        (integralSingularChains ({(p : X)}ᶜ : Set X)).homologyπ 2) (ULift.up 1) :=
  integralRelativeConnecting_liftCycles_apply 1 ({(p : X)}ᶜ : Set X)
    (integralSimplexChain 3 σ) (relativeChain_boundary p σ hσ)
    (puncturedSimplexBoundary p σ hσ) (puncturedSimplexBoundary_boundary p σ hσ)
    (puncturedSimplexBoundary_chain p σ hσ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralRelativeConnecting_simplexLocalClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralRelativeConnecting_simplexLocalClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralRelativeConnecting_simplexLocalClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralRelativeConnecting_simplexLocalClass

def euclideanStandardSimplexBoundaryClass :
    integralSingularHomology 2 ({(0 : liftedSphereSpace.{u} 1)}ᶜ :
      Set (liftedSphereSpace.{u} 1)) :=
  (((integralSingularChains ({(0 : liftedSphereSpace.{u} 1)}ᶜ :
      Set (liftedSphereSpace.{u} 1))).liftCycles
      (puncturedSimplexBoundary (0 : liftedSphereSpace.{u} 1) standardTetrahedronSimplex
        (fun i q => standardTetrahedronSimplex_face_ne_zero i q))
      1 ((ComplexShape.down ℕ).next_eq' (by rfl)) (puncturedSimplexBoundary_boundary _ _ _)) ≫
    (integralSingularChains ({(0 : liftedSphereSpace.{u} 1)}ᶜ :
      Set (liftedSphereSpace.{u} 1))).homologyπ 2) (ULift.up 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryClass

theorem integralRelativeConnecting_euclideanStandardSimplexClass :
    integralRelativeConnecting 2 ({(0 : liftedSphereSpace.{u} 1)}ᶜ)
        euclideanStandardSimplexClass =
      euclideanStandardSimplexBoundaryClass :=
  integralRelativeConnecting_simplexLocalClass 0 standardTetrahedronSimplex
    (fun i q => standardTetrahedronSimplex_face_ne_zero i q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralRelativeConnecting_euclideanStandardSimplexClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralRelativeConnecting_euclideanStandardSimplexClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralRelativeConnecting_euclideanStandardSimplexClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralRelativeConnecting_euclideanStandardSimplexClass

theorem isUnit_apply_iff_bijective_zsmul {A : Type*} [AddCommGroup A] [Module ℤ A]
    (e : A ≃ₗ[ℤ] ℤ) (c : A) :
    IsUnit (e c) ↔ Function.Bijective (fun z : ℤ => z • c) := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := h
    have hfun : (fun z : ℤ => z • c) = fun z : ℤ => e.symm ((z : ℤ) * (u : ℤ)) := by
      funext z
      apply e.injective
      rw [map_zsmul, hu, smul_eq_mul, LinearEquiv.apply_symm_apply]
    rw [hfun]
    constructor
    · intro a b hab
      have h2 : (a : ℤ) * (u : ℤ) = (b : ℤ) * (u : ℤ) := e.symm.injective hab
      exact mul_right_cancel₀ (Units.ne_zero u) h2
    · intro w
      refine ⟨e w * ((u⁻¹ : ℤˣ) : ℤ), ?_⟩
      change e.symm ((e w * ((u⁻¹ : ℤˣ) : ℤ)) * (u : ℤ)) = w
      rw [mul_assoc, Units.inv_mul, mul_one, e.symm_apply_apply]
  · intro h
    obtain ⟨k, hk⟩ := h.surjective (e.symm 1)
    have hk' : k * e c = 1 := by
      have h := congrArg e hk
      rw [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul] at h
      exact h
    exact isUnit_iff_exists_inv.mpr ⟨k, by rw [mul_comm]; exact hk'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.isUnit_apply_iff_bijective_zsmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.isUnit_apply_iff_bijective_zsmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.isUnit_apply_iff_bijective_zsmul ``Submission.DifferentialGeometry.Topology.SimplexDegree.isUnit_apply_iff_bijective_zsmul

theorem bijective_zsmul_iff_of_linearEquiv {A B : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] (f : A ≃ₗ[ℤ] B) (c : A) :
    Function.Bijective (fun z : ℤ => z • f c) ↔
      Function.Bijective (fun z : ℤ => z • c) := by
  have hfun : (fun z : ℤ => z • f c) = ⇑f ∘ fun z : ℤ => z • c := by
    funext z
    rw [Function.comp_apply, map_zsmul]
  rw [hfun]
  exact Equiv.comp_bijective (fun z : ℤ => z • c) f.toEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.bijective_zsmul_iff_of_linearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.bijective_zsmul_iff_of_linearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.bijective_zsmul_iff_of_linearEquiv ``Submission.DifferentialGeometry.Topology.SimplexDegree.bijective_zsmul_iff_of_linearEquiv

theorem euclideanStandardSimplexClass_generator_iff_isUnit_boundaryClass :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) ↔
      IsUnit (integralSphereTopHomologyEquiv 1
        (liftedSphereSpace.{u} 1) (liftedSphereSpace_finrank 1)
        (integralPuncturedSpaceSphereHomologyEquiv
          (liftedSphereSpace.{u} 1) 2
          euclideanStandardSimplexBoundaryClass)) := by
  rw [← isUnit_apply_iff_bijective_zsmul
    (integralEuclideanLocalTopZeroEquiv (liftedSphereSpace.{u} 1) 1
      (liftedSphereSpace_finrank 1)) euclideanStandardSimplexClass]
  have h : integralEuclideanLocalTopZeroEquiv (liftedSphereSpace.{u} 1) 1
      (liftedSphereSpace_finrank 1) euclideanStandardSimplexClass =
      integralSphereTopHomologyEquiv 1 (liftedSphereSpace.{u} 1)
        (liftedSphereSpace_finrank 1)
        (integralPuncturedSpaceSphereHomologyEquiv
          (liftedSphereSpace.{u} 1) 2
          (integralRelativeConnecting 2
            ({(0 : liftedSphereSpace.{u} 1)}ᶜ)
            euclideanStandardSimplexClass)) := by
    unfold integralEuclideanLocalTopZeroEquiv
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
    rfl
  rw [h, integralRelativeConnecting_euclideanStandardSimplexClass]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_isUnit_boundaryClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_isUnit_boundaryClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_isUnit_boundaryClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_isUnit_boundaryClass

def euclideanStandardSimplexBoundaryChain :
    integralSingularCoefficients ⟶
      (integralSingularChains ({(0 : liftedSphereSpace.{u} 1)}ᶜ :
        Set (liftedSphereSpace.{u} 1))).X 2 :=
  puncturedSimplexBoundary (0 : liftedSphereSpace.{u} 1) standardTetrahedronSimplex
    (fun i q => standardTetrahedronSimplex_face_ne_zero i q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryChain ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryChain

theorem euclideanStandardSimplexBoundaryChain_boundary :
    euclideanStandardSimplexBoundaryChain ≫
      (integralSingularChains ({(0 : liftedSphereSpace.{u} 1)}ᶜ :
        Set (liftedSphereSpace.{u} 1))).d 2 1 = 0 :=
  puncturedSimplexBoundary_boundary (0 : liftedSphereSpace.{u} 1) standardTetrahedronSimplex
    (fun i q => standardTetrahedronSimplex_face_ne_zero i q)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryChain_boundary ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryChain_boundary

theorem euclideanStandardSimplexBoundaryClass_eq_classOf :
    integralHomologyClassOf 1 euclideanStandardSimplexBoundaryChain
        euclideanStandardSimplexBoundaryChain_boundary =
      euclideanStandardSimplexBoundaryClass.{u} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryClass_eq_classOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryClass_eq_classOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryClass_eq_classOf ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundaryClass_eq_classOf

def boundarySphereMap :
    C(({(0 : liftedSphereSpace.{u} 1)}ᶜ : Set (liftedSphereSpace.{u} 1)),
      liftedHomotopySphere.{u} 1) :=
  (liftedSphereHomeomorph.{u} 1).toHomotopyEquiv.invFun.comp
    (puncturedSpaceSphereHomotopyEquiv (liftedSphereSpace.{u} 1)).toFun

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.boundarySphereMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.boundarySphereMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.boundarySphereMap ``Submission.DifferentialGeometry.Topology.SimplexDegree.boundarySphereMap

def simplexBoundaryLiftedChain :
    integralSingularCoefficients ⟶
      (integralSingularChains (liftedHomotopySphere.{u} 1)).X 2 :=
  euclideanStandardSimplexBoundaryChain ≫
    (integralSingularChainMap boundarySphereMap).f 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain

theorem simplexBoundaryLiftedChain_boundary :
    simplexBoundaryLiftedChain ≫
      (integralSingularChains (liftedHomotopySphere.{u} 1)).d 2 1 = 0 := by
  rw [simplexBoundaryLiftedChain, Category.assoc,
    (integralSingularChainMap boundarySphereMap).comm 2 1, ← Category.assoc,
    euclideanStandardSimplexBoundaryChain_boundary, Limits.zero_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain_boundary ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain_boundary

def euclideanStandardSimplexBoundarySphereClass :
    integralSingularHomology 2 (liftedHomotopySphere.{u} 1) :=
  (integralSingularHomologyHomotopyEquiv 2
      (liftedSphereHomeomorph.{u} 1).toHomotopyEquiv).symm
    (integralPuncturedSpaceSphereHomologyEquiv
      (liftedSphereSpace.{u} 1) 2 euclideanStandardSimplexBoundaryClass)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundarySphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundarySphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundarySphereClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundarySphereClass

theorem euclideanStandardSimplexBoundarySphereClass_eq_map :
    euclideanStandardSimplexBoundarySphereClass.{u} =
      integralSingularHomologyMap 2 boundarySphereMap
        euclideanStandardSimplexBoundaryClass.{u} := by
  unfold euclideanStandardSimplexBoundarySphereClass
  rw [show integralSingularHomologyMap 2 boundarySphereMap =
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
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundarySphereClass_eq_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundarySphereClass_eq_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundarySphereClass_eq_map ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundarySphereClass_eq_map

theorem euclideanStandardSimplexBoundarySphereClass_eq_classOf :
    integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      euclideanStandardSimplexBoundarySphereClass.{u} := by
  rw [euclideanStandardSimplexBoundarySphereClass_eq_map,
    ← euclideanStandardSimplexBoundaryClass_eq_classOf,
    integralSingularHomologyMap_integralHomologyClassOf]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundarySphereClass_eq_classOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundarySphereClass_eq_classOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundarySphereClass_eq_classOf ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexBoundarySphereClass_eq_classOf

theorem integralChainHom_squareSphereFundamentalChain_boundary :
    integralChainHom 2 squareSphereFundamentalChain ≫
      (integralSingularChains (liftedHomotopySphere.{u} 1)).d 2 1 = 0 := by
  rw [integralChainHom_d 1 squareSphereFundamentalChain, squareSphereFundamentalChain_boundary,
    integralChainHom_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralChainHom_squareSphereFundamentalChain_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralChainHom_squareSphereFundamentalChain_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralChainHom_squareSphereFundamentalChain_boundary ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralChainHom_squareSphereFundamentalChain_boundary

theorem squareSphereFundamentalClass_eq_classOf :
    integralHomologyClassOf 1 (integralChainHom 2 squareSphereFundamentalChain)
        integralChainHom_squareSphereFundamentalChain_boundary =
      squareSphereFundamentalClass.{u} := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.squareSphereFundamentalClass_eq_classOf then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.squareSphereFundamentalClass_eq_classOf"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.squareSphereFundamentalClass_eq_classOf ``Submission.DifferentialGeometry.Topology.SimplexDegree.squareSphereFundamentalClass_eq_classOf

theorem euclideanStandardSimplexClass_generator_iff_puncturedBoundaryClass_generator :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) ↔
      Function.Bijective (fun z : ℤ => z •
        integralPuncturedSpaceSphereHomologyEquiv
          (liftedSphereSpace.{u} 1) 2
          euclideanStandardSimplexBoundaryClass.{u}) :=
  (euclideanStandardSimplexClass_generator_iff_isUnit_boundaryClass).trans
    (isUnit_apply_iff_bijective_zsmul
      (integralSphereTopHomologyEquiv 1
        (liftedSphereSpace.{u} 1) (liftedSphereSpace_finrank 1))
      (integralPuncturedSpaceSphereHomologyEquiv
        (liftedSphereSpace.{u} 1) 2 euclideanStandardSimplexBoundaryClass))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_puncturedBoundaryClass_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_puncturedBoundaryClass_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_puncturedBoundaryClass_generator ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_puncturedBoundaryClass_generator

theorem euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) ↔
      IsSphereHomologyGenerator.{u} 1 euclideanStandardSimplexBoundarySphereClass.{u} := by
  rw [isSphereHomologyGenerator_iff_bijective_zsmul]
  have hdef : euclideanStandardSimplexBoundarySphereClass.{u} =
      (integralSingularHomologyHomotopyEquiv 2
        (liftedSphereHomeomorph.{u} 1).toHomotopyEquiv).symm
        (integralPuncturedSpaceSphereHomologyEquiv
          (liftedSphereSpace.{u} 1) 2
          euclideanStandardSimplexBoundaryClass.{u}) := rfl
  rw [hdef]
  exact (euclideanStandardSimplexClass_generator_iff_puncturedBoundaryClass_generator).trans
    (bijective_zsmul_iff_of_linearEquiv
      (integralSingularHomologyHomotopyEquiv 2
        (liftedSphereHomeomorph.{u} 1).toHomotopyEquiv).symm
      (integralPuncturedSpaceSphereHomologyEquiv
        (liftedSphereSpace.{u} 1) 2
        euclideanStandardSimplexBoundaryClass.{u})).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator

def SimplexBoundarySphereAlignment : Prop :=
  integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      squareSphereFundamentalClass.{u} ∨
    integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      -squareSphereFundamentalClass.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.SimplexBoundarySphereAlignment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.SimplexBoundarySphereAlignment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.SimplexBoundarySphereAlignment ``Submission.DifferentialGeometry.Topology.SimplexDegree.SimplexBoundarySphereAlignment

def SimplexBoundarySphereFilling : Prop :=
  ∃ z : integralSingularCoefficients ⟶
      (integralSingularChains (liftedHomotopySphere.{u} 1)).X 3,
    (z ≫ (integralSingularChains (liftedHomotopySphere.{u} 1)).d 3 2 =
        simplexBoundaryLiftedChain - integralChainHom 2 squareSphereFundamentalChain) ∨
      (z ≫ (integralSingularChains (liftedHomotopySphere.{u} 1)).d 3 2 =
        integralChainHom 2 squareSphereFundamentalChain - simplexBoundaryLiftedChain)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.SimplexBoundarySphereFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.SimplexBoundarySphereFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.SimplexBoundarySphereFilling ``Submission.DifferentialGeometry.Topology.SimplexDegree.SimplexBoundarySphereFilling

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
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereAlignment_of_filling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereAlignment_of_filling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereAlignment_of_filling ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereAlignment_of_filling

theorem isSphereHomologyGenerator_neg (n : ℕ)
    {c : integralSingularHomology (n + 1) (liftedHomotopySphere.{u} n)}
    (h : IsSphereHomologyGenerator n c) : IsSphereHomologyGenerator n (-c) := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.trans (LinearEquiv.neg ℤ), ?_⟩
  simp [LinearEquiv.trans_apply, he]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.isSphereHomologyGenerator_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.isSphereHomologyGenerator_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.isSphereHomologyGenerator_neg ``Submission.DifferentialGeometry.Topology.SimplexDegree.isSphereHomologyGenerator_neg

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
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.isSphereHomologyGenerator_of_simplexBoundarySphereAlignment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.isSphereHomologyGenerator_of_simplexBoundarySphereAlignment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.isSphereHomologyGenerator_of_simplexBoundarySphereAlignment ``Submission.DifferentialGeometry.Topology.SimplexDegree.isSphereHomologyGenerator_of_simplexBoundarySphereAlignment

theorem euclideanStandardSimplexClass_generator_of_simplexBoundarySphereAlignment
    (halign : SimplexBoundarySphereAlignment.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) :=
  euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator.mpr
    (isSphereHomologyGenerator_of_simplexBoundarySphereAlignment halign hg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_of_simplexBoundarySphereAlignment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_of_simplexBoundarySphereAlignment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_of_simplexBoundarySphereAlignment ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_of_simplexBoundarySphereAlignment

theorem euclideanStandardSimplexClass_generator_of_simplexBoundarySphereFilling
    (h : SimplexBoundarySphereFilling.{u})
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) :=
  euclideanStandardSimplexClass_generator_of_simplexBoundarySphereAlignment
    (simplexBoundarySphereAlignment_of_filling h) hg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_of_simplexBoundarySphereFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_of_simplexBoundarySphereFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_of_simplexBoundarySphereFilling ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_of_simplexBoundarySphereFilling

variable {X : Type u} [TopologicalSpace X]

theorem integralChainHom_apply_one (n : ℕ) (c : (integralSingularChains X).X n) :
    integralChainHom n c (ULift.up (1 : ℤ)) = c := by
  change (integralChainHom n c).hom (ULift.up (1 : ℤ)) = c
  rw [integralChainHom_hom, LinearMap.comp_apply]
  exact LinearMap.toSpanSingleton_apply_one ℤ _ c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralChainHom_apply_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralChainHom_apply_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralChainHom_apply_one ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralChainHom_apply_one

theorem integralChainHom_ext {n : ℕ}
    {M : integralSingularCoefficients ⟶ (integralSingularChains X).X n}
    {c : (integralSingularChains X).X n} (h : M (ULift.up (1 : ℤ)) = c) :
    M = integralChainHom n c := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rcases y with ⟨k⟩
  have hk : (ULift.up k : ULift.{u} ℤ) = k • (ULift.up (1 : ℤ) : ULift.{u} ℤ) := by
    ext
    simp
  rw [hk, map_zsmul, map_zsmul, h, integralChainHom_apply_one]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralChainHom_ext then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralChainHom_ext"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralChainHom_ext ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralChainHom_ext

theorem integralChainHom_sub (n : ℕ) (c d : (integralSingularChains X).X n) :
    integralChainHom n (c - d) = integralChainHom n c - integralChainHom n d := by
  apply ModuleCat.hom_ext
  have hsub : LinearMap.toSpanSingleton ℤ ((integralSingularChains X).X n) (c - d) =
      LinearMap.toSpanSingleton ℤ ((integralSingularChains X).X n) c -
        LinearMap.toSpanSingleton ℤ ((integralSingularChains X).X n) d := by
    apply LinearMap.ext
    intro r
    simp only [LinearMap.sub_apply, LinearMap.toSpanSingleton_apply, smul_sub]
  rw [integralChainHom_hom, ModuleCat.hom_sub, integralChainHom_hom, integralChainHom_hom, hsub,
    LinearMap.sub_comp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralChainHom_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralChainHom_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralChainHom_sub ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralChainHom_sub

theorem moduleCatCyclesIso_hom_val (S : _root_.CategoryTheory.ShortComplex (ModuleCat.{u} ℤ)) (z : S.cycles) :
    (S.moduleCatCyclesIso.hom z).val = S.iCycles z := by
  have h := congrArg (fun f : S.cycles ⟶ S.X₂ => f z) (ShortComplex.moduleCatCyclesIso_hom_i S)
  simp only [ModuleCat.comp_apply] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.moduleCatCyclesIso_hom_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.moduleCatCyclesIso_hom_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.moduleCatCyclesIso_hom_val ``Submission.DifferentialGeometry.Topology.SimplexDegree.moduleCatCyclesIso_hom_val

def integralChainLiftCycle (n : ℕ) (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    integralSingularCoefficients ⟶ ((integralSingularChains X).sc (n + 1)).cycles :=
  (integralSingularChains X).liftCycles (integralChainHom (n + 1) c) n
    ((ComplexShape.down ℕ).next_eq' (by rfl))
    (by rw [integralChainHom_d n c, hc, integralChainHom_zero])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralChainLiftCycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralChainLiftCycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralChainLiftCycle ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralChainLiftCycle

theorem integralChainLiftCycle_apply (n : ℕ) (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    (integralSingularChains X).iCycles (n + 1)
      (integralChainLiftCycle n c hc (ULift.up (1 : ℤ))) = c := by
  have h := congrArg (fun f : integralSingularCoefficients ⟶
      (integralSingularChains X).X (n + 1) => f (ULift.up (1 : ℤ)))
    ((integralSingularChains X).liftCycles_i (integralChainHom (n + 1) c) n
      ((ComplexShape.down ℕ).next_eq' (by rfl))
      (by rw [integralChainHom_d n c, hc, integralChainHom_zero]))
  rw [ModuleCat.comp_apply, integralChainHom_apply_one] at h
  rw [integralChainLiftCycle]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralChainLiftCycle_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralChainLiftCycle_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralChainLiftCycle_apply ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralChainLiftCycle_apply

def integralSingularCycleOfChain (n : ℕ) (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    LinearMap.ker (((integralSingularChains X).sc (n + 1)).g.hom) :=
  ((integralSingularChains X).sc (n + 1)).moduleCatCyclesIso.hom
    (integralChainLiftCycle n c hc (ULift.up 1))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralSingularCycleOfChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralSingularCycleOfChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralSingularCycleOfChain ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralSingularCycleOfChain

theorem integralSingularCycleOfChain_val (n : ℕ)
    (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    (integralSingularCycleOfChain n c hc).val = c := by
  have h₁ := moduleCatCyclesIso_hom_val ((integralSingularChains X).sc (n + 1))
    (integralChainLiftCycle n c hc (ULift.up 1))
  rw [integralSingularCycleOfChain, h₁]
  exact integralChainLiftCycle_apply n c hc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralSingularCycleOfChain_val then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralSingularCycleOfChain_val"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralSingularCycleOfChain_val ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralSingularCycleOfChain_val

theorem integralHomologyClassOf_integralChainHom (n : ℕ)
    (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0)
    {hz : integralChainHom (n + 1) c ≫ (integralSingularChains X).d (n + 1) n = 0} :
    integralHomologyClassOf n (integralChainHom (n + 1) c) hz =
      integralHomologyClass n c hc := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralHomologyClassOf_integralChainHom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralHomologyClassOf_integralChainHom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralHomologyClassOf_integralChainHom ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralHomologyClassOf_integralChainHom

theorem integralHomologyClass_eq_moduleHomologyClass (n : ℕ)
    (c : (integralSingularChains X).X (n + 1))
    (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    integralHomologyClass n c hc =
      moduleHomologyClass ((integralSingularChains X).sc (n + 1))
        (integralSingularCycleOfChain n c hc) := by
  have h : moduleHomologyClass ((integralSingularChains X).sc (n + 1))
      (integralSingularCycleOfChain n c hc) =
      ((integralSingularChains X).sc (n + 1)).homologyπ
        (integralChainLiftCycle n c hc (ULift.up (1 : ℤ))) := by
    rw [moduleHomologyClass, integralSingularCycleOfChain]
    change (((integralSingularChains X).sc (n + 1)).homologyπ.hom ∘ₗ
        ((integralSingularChains X).sc (n + 1)).moduleCatCyclesIso.inv.hom)
      (((integralSingularChains X).sc (n + 1)).moduleCatCyclesIso.hom
        (integralChainLiftCycle n c hc (ULift.up (1 : ℤ)))) = _
    rw [LinearMap.comp_apply, Iso.hom_inv_id_apply]
  rw [h, integralHomologyClass, integralHomologyClassOf, integralChainLiftCycle,
    ModuleCat.comp_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralHomologyClass_eq_moduleHomologyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralHomologyClass_eq_moduleHomologyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralHomologyClass_eq_moduleHomologyClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralHomologyClass_eq_moduleHomologyClass

theorem exists_chain_of_integralHomologyClass_eq (n : ℕ)
    (c₁ c₂ : (integralSingularChains X).X (n + 1))
    (h₁ : (integralSingularChains X).d (n + 1) n c₁ = 0)
    (h₂ : (integralSingularChains X).d (n + 1) n c₂ = 0)
    (h : integralHomologyClass n c₁ h₁ = integralHomologyClass n c₂ h₂) :
    ∃ b : (integralSingularChains X).X (n + 2),
      (integralSingularChains X).d (n + 2) (n + 1) b = c₁ - c₂ := by
  have hmod : moduleHomologyClass ((integralSingularChains X).sc (n + 1))
        (integralSingularCycleOfChain n c₁ h₁) =
      moduleHomologyClass ((integralSingularChains X).sc (n + 1))
        (integralSingularCycleOfChain n c₂ h₂) := by
    rw [← integralHomologyClass_eq_moduleHomologyClass n c₁ h₁,
      ← integralHomologyClass_eq_moduleHomologyClass n c₂ h₂]
    exact h
  obtain ⟨b, hb⟩ := (moduleHomologyClass_eq_iff ((integralSingularChains X).sc (n + 1))
    (integralSingularCycleOfChain n c₁ h₁) (integralSingularCycleOfChain n c₂ h₂)).mp hmod
  rw [integralSingularCycleOfChain_val n c₁ h₁,
    integralSingularCycleOfChain_val n c₂ h₂] at hb
  let e := ChainComplex.prev ℕ (n + 1)
  refine ⟨((integralSingularChains X).XIsoOfEq e).hom b, ?_⟩
  have hcomp : (integralSingularChains X).d (n + 2) (n + 1)
      (((integralSingularChains X).XIsoOfEq e).hom b) = c₁ - c₂ := by
    have h₁' := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
      (HomologicalComplex.XIsoOfEq_hom_comp_d (integralSingularChains X) e (n + 1))) b
    simp only [ModuleCat.hom_comp] at h₁'
    exact h₁'.trans hb
  exact hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.exists_chain_of_integralHomologyClass_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.exists_chain_of_integralHomologyClass_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.exists_chain_of_integralHomologyClass_eq ``Submission.DifferentialGeometry.Topology.SimplexDegree.exists_chain_of_integralHomologyClass_eq

theorem simplexBoundaryLiftedChain_apply_boundary :
    (integralSingularChains (liftedHomotopySphere.{u} 1)).d 2 1
      (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ))) = 0 := by
  have h := congrArg (fun f : integralSingularCoefficients ⟶
      (integralSingularChains (liftedHomotopySphere.{u} 1)).X 1 => f (ULift.up (1 : ℤ)))
    simplexBoundaryLiftedChain_boundary.{u}
  rw [ModuleCat.comp_apply] at h
  simpa using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain_apply_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain_apply_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain_apply_boundary ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain_apply_boundary

theorem integralChainHom_simplexBoundaryLiftedChain :
    integralChainHom 2 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ))) =
      simplexBoundaryLiftedChain.{u} :=
  (integralChainHom_ext (M := simplexBoundaryLiftedChain.{u})
    (c := simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ))) rfl).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.integralChainHom_simplexBoundaryLiftedChain then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.integralChainHom_simplexBoundaryLiftedChain"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.integralChainHom_simplexBoundaryLiftedChain ``Submission.DifferentialGeometry.Topology.SimplexDegree.integralChainHom_simplexBoundaryLiftedChain

theorem simplexBoundaryLiftedChain_class_eq_integralHomologyClass :
    integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      integralHomologyClass 1 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ)))
        simplexBoundaryLiftedChain_apply_boundary := by
  have hz : integralChainHom 2 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ))) ≫
      (integralSingularChains (liftedHomotopySphere.{u} 1)).d 2 1 = 0 := by
    rw [integralChainHom_d 1 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ))),
      simplexBoundaryLiftedChain_apply_boundary, integralChainHom_zero]
  exact (integralHomologyClassOf_congr (n := 1)
      (hz := simplexBoundaryLiftedChain_boundary) (hz' := hz)
      integralChainHom_simplexBoundaryLiftedChain.symm).trans
    (integralHomologyClassOf_integralChainHom 1
      (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ)))
      simplexBoundaryLiftedChain_apply_boundary (hz := hz))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain_class_eq_integralHomologyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain_class_eq_integralHomologyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain_class_eq_integralHomologyClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexBoundaryLiftedChain_class_eq_integralHomologyClass

theorem squareSphereFundamentalClass_eq_integralHomologyClass :
    squareSphereFundamentalClass.{u} =
      integralHomologyClass 1 squareSphereFundamentalChain squareSphereFundamentalChain_boundary :=
  squareSphereFundamentalClass_eq_classOf.trans
    (integralHomologyClassOf_integralChainHom 1 squareSphereFundamentalChain
      squareSphereFundamentalChain_boundary (hz :=
        integralChainHom_squareSphereFundamentalChain_boundary))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.squareSphereFundamentalClass_eq_integralHomologyClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.squareSphereFundamentalClass_eq_integralHomologyClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.squareSphereFundamentalClass_eq_integralHomologyClass ``Submission.DifferentialGeometry.Topology.SimplexDegree.squareSphereFundamentalClass_eq_integralHomologyClass

theorem simplexBoundarySphereFilling_iff_exists_filling :
    SimplexBoundarySphereFilling.{u} ↔
      ∃ z : integralSingularCoefficients ⟶
          (integralSingularChains (liftedHomotopySphere.{u} 1)).X 3,
        z ≫ (integralSingularChains (liftedHomotopySphere.{u} 1)).d 3 2 =
          simplexBoundaryLiftedChain - integralChainHom 2 squareSphereFundamentalChain := by
  constructor
  · rintro (⟨z, hz | hz⟩)
    · exact ⟨z, hz⟩
    · exact ⟨-z, by rw [Preadditive.neg_comp, hz, neg_sub]⟩
  · rintro ⟨z, hz⟩
    unfold SimplexBoundarySphereFilling
    exact ⟨z, Or.inl hz⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_iff_exists_filling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_iff_exists_filling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_iff_exists_filling ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_iff_exists_filling

theorem class_eq_of_simplexBoundarySphereFilling (h : SimplexBoundarySphereFilling.{u}) :
    integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      squareSphereFundamentalClass.{u} := by
  obtain ⟨z, hz | hz⟩ := h
  · exact (integralHomologyClassOf_eq_of_sub_eq 1 simplexBoundaryLiftedChain
      (integralChainHom 2 squareSphereFundamentalChain) simplexBoundaryLiftedChain_boundary
      integralChainHom_squareSphereFundamentalChain_boundary z hz.symm).trans
      squareSphereFundamentalClass_eq_classOf.symm
  · exact (integralHomologyClassOf_eq_of_sub_eq 1
      (integralChainHom 2 squareSphereFundamentalChain) simplexBoundaryLiftedChain
      integralChainHom_squareSphereFundamentalChain_boundary simplexBoundaryLiftedChain_boundary
      z hz.symm).symm.trans squareSphereFundamentalClass_eq_classOf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.class_eq_of_simplexBoundarySphereFilling then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.class_eq_of_simplexBoundarySphereFilling"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.class_eq_of_simplexBoundarySphereFilling ``Submission.DifferentialGeometry.Topology.SimplexDegree.class_eq_of_simplexBoundarySphereFilling

theorem simplexBoundarySphereFilling_of_integralHomologyClass_eq
    (h : integralHomologyClass 1 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ)))
        simplexBoundaryLiftedChain_apply_boundary =
      integralHomologyClass 1 squareSphereFundamentalChain squareSphereFundamentalChain_boundary) :
    SimplexBoundarySphereFilling.{u} := by
  obtain ⟨b, hb⟩ := exists_chain_of_integralHomologyClass_eq 1
    (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ))) squareSphereFundamentalChain
    simplexBoundaryLiftedChain_apply_boundary squareSphereFundamentalChain_boundary h
  unfold SimplexBoundarySphereFilling
  exact ⟨integralChainHom 3 b, Or.inl (by
    rw [integralChainHom_d 2 b, hb, integralChainHom_sub,
      integralChainHom_simplexBoundaryLiftedChain])⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_of_integralHomologyClass_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_of_integralHomologyClass_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_of_integralHomologyClass_eq ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_of_integralHomologyClass_eq

theorem simplexBoundarySphereFilling_iff_integralHomologyClass_eq :
    SimplexBoundarySphereFilling.{u} ↔
      integralHomologyClass 1 (simplexBoundaryLiftedChain.{u} (ULift.up (1 : ℤ)))
          simplexBoundaryLiftedChain_apply_boundary =
        integralHomologyClass 1 squareSphereFundamentalChain
          squareSphereFundamentalChain_boundary :=
  ⟨fun h =>
      simplexBoundaryLiftedChain_class_eq_integralHomologyClass.symm.trans
        ((class_eq_of_simplexBoundarySphereFilling h).trans
          squareSphereFundamentalClass_eq_integralHomologyClass),
    simplexBoundarySphereFilling_of_integralHomologyClass_eq⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_iff_integralHomologyClass_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_iff_integralHomologyClass_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_iff_integralHomologyClass_eq ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_iff_integralHomologyClass_eq

theorem simplexBoundarySphereFilling_iff_class_eq :
    SimplexBoundarySphereFilling.{u} ↔
      integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
        squareSphereFundamentalClass.{u} := by
  rw [simplexBoundaryLiftedChain_class_eq_integralHomologyClass,
    squareSphereFundamentalClass_eq_integralHomologyClass]
  exact simplexBoundarySphereFilling_iff_integralHomologyClass_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_iff_class_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_iff_class_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_iff_class_eq ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereFilling_iff_class_eq

theorem not_simplexBoundarySphereFilling_of_class_eq_neg
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u})
    (h : integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
      -squareSphereFundamentalClass.{u}) :
    ¬ SimplexBoundarySphereFilling.{u} := by
  intro hf
  have hneg : squareSphereFundamentalClass.{u} = -squareSphereFundamentalClass.{u} :=
    (class_eq_of_simplexBoundarySphereFilling hf).symm.trans h
  obtain ⟨e, he⟩ := hg
  have hcoe := congrArg e hneg
  rw [map_neg, he] at hcoe
  norm_num at hcoe

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.not_simplexBoundarySphereFilling_of_class_eq_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.not_simplexBoundarySphereFilling_of_class_eq_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.not_simplexBoundarySphereFilling_of_class_eq_neg ``Submission.DifferentialGeometry.Topology.SimplexDegree.not_simplexBoundarySphereFilling_of_class_eq_neg

theorem simplexBoundarySphereAlignment_iff_filling_or_class_eq_neg :
    SimplexBoundarySphereAlignment.{u} ↔
      SimplexBoundarySphereFilling.{u} ∨
        integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
          -squareSphereFundamentalClass.{u} := by
  simp only [SimplexBoundarySphereAlignment, simplexBoundarySphereFilling_iff_class_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereAlignment_iff_filling_or_class_eq_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereAlignment_iff_filling_or_class_eq_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereAlignment_iff_filling_or_class_eq_neg ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereAlignment_iff_filling_or_class_eq_neg

theorem simplexBoundarySphereAlignment_of_euclideanStandardSimplexClass_generator
    (h : Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}))
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    SimplexBoundarySphereAlignment.{u} := by
  have hc := euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator.mp h
  rw [← euclideanStandardSimplexBoundarySphereClass_eq_classOf] at hc
  rcases IsSphereHomologyGenerator.eq_or_eq_neg 1 hc hg with h' | h'
  · exact Or.inl h'
  · exact Or.inr h'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereAlignment_of_euclideanStandardSimplexClass_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereAlignment_of_euclideanStandardSimplexClass_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereAlignment_of_euclideanStandardSimplexClass_generator ``Submission.DifferentialGeometry.Topology.SimplexDegree.simplexBoundarySphereAlignment_of_euclideanStandardSimplexClass_generator

theorem euclideanStandardSimplexClass_generator_iff_simplexBoundarySphereAlignment
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) ↔
      SimplexBoundarySphereAlignment.{u} :=
  ⟨fun h => simplexBoundarySphereAlignment_of_euclideanStandardSimplexClass_generator h hg,
    fun h => euclideanStandardSimplexClass_generator_of_simplexBoundarySphereAlignment h hg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_simplexBoundarySphereAlignment then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_simplexBoundarySphereAlignment"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_simplexBoundarySphereAlignment ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_simplexBoundarySphereAlignment

theorem euclideanStandardSimplexClass_generator_iff_simplexBoundarySphereFilling_or_class_eq_neg
    (hg : IsSphereHomologyGenerator.{u} 1 squareSphereFundamentalClass.{u}) :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) ↔
      SimplexBoundarySphereFilling.{u} ∨
        integralHomologyClassOf 1 simplexBoundaryLiftedChain simplexBoundaryLiftedChain_boundary =
          -squareSphereFundamentalClass.{u} :=
  (euclideanStandardSimplexClass_generator_iff_simplexBoundarySphereAlignment hg).trans
    simplexBoundarySphereAlignment_iff_filling_or_class_eq_neg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_simplexBoundarySphereFilling_or_class_eq_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_simplexBoundarySphereFilling_or_class_eq_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_simplexBoundarySphereFilling_or_class_eq_neg ``Submission.DifferentialGeometry.Topology.SimplexDegree.euclideanStandardSimplexClass_generator_iff_simplexBoundarySphereFilling_or_class_eq_neg

end SimplexDegree

end DifferentialGeometry.Topology
