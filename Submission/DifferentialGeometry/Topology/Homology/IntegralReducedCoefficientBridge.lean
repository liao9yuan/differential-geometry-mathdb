import Submission.DifferentialGeometry.Topology.Homology.Reduced
import Submission.DifferentialGeometry.Topology.Homology.Reduced.Comparison
import Submission.DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral
import Submission.DifferentialGeometry.Topology.Homology.SquareBoundaryDegree
import Submission.DifferentialGeometry.Topology.LocalDegree.SphereDegree
import Submission.DifferentialGeometry.Topology.Homology.SphereGeneratorCriterion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicTopology
open scoped _root_.Topology

namespace DifferentialGeometry.Topology

open _root_.Submission.DifferentialGeometry.Homology

def integralSingularCoefficientsIso : integralSingularCoefficients ≅ ModuleCat.of ℤ ℤ :=
  (ULift.moduleEquiv (M := ℤ)).toModuleIso

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularCoefficientsIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularCoefficientsIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularCoefficientsIso ``Submission.DifferentialGeometry.Topology.integralSingularCoefficientsIso

def integralSingularChainsCoeffIso (X : Type) [TopologicalSpace X] :
    (TopCat.toSSet.obj (TopCat.of X)).chainComplex integralSingularCoefficients ≅
      (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℤ ℤ) :=
  ((SSet.chainComplexFunctor (ModuleCat ℤ)).mapIso integralSingularCoefficientsIso).app
    (TopCat.toSSet.obj (TopCat.of X))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsCoeffIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsCoeffIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsCoeffIso ``Submission.DifferentialGeometry.Topology.integralSingularChainsCoeffIso

theorem integralSingularChainsCoeffIso_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    (integralSingularChainsCoeffIso X).hom ≫
        SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ) =
      SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) integralSingularCoefficients ≫
        (integralSingularChainsCoeffIso Y).hom :=
  (((SSet.chainComplexFunctor (ModuleCat ℤ)).mapIso integralSingularCoefficientsIso).hom.naturality
    (TopCat.toSSet.map (TopCat.ofHom f))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularChainsCoeffIso_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularChainsCoeffIso_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularChainsCoeffIso_naturality ``Submission.DifferentialGeometry.Topology.integralSingularChainsCoeffIso_naturality

def integralSingularHomologyCoeffIso (n : ℕ) (X : Type) [TopologicalSpace X] :
    integralSingularHomology n X ≅
      (TopCat.toSSet.obj (TopCat.of X)).homology (ModuleCat.of ℤ ℤ) n :=
  HomologicalComplex.homologyMapIso (integralSingularChainsCoeffIso X) n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyCoeffIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyCoeffIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyCoeffIso ``Submission.DifferentialGeometry.Topology.integralSingularHomologyCoeffIso

theorem integralSingularHomologyCoeffIso_hom (n : ℕ) (X : Type) [TopologicalSpace X] :
    (integralSingularHomologyCoeffIso n X).hom =
      HomologicalComplex.homologyMap (integralSingularChainsCoeffIso X).hom n :=
  HomologicalComplex.homologyMapIso_hom _ n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyCoeffIso_hom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyCoeffIso_hom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyCoeffIso_hom ``Submission.DifferentialGeometry.Topology.integralSingularHomologyCoeffIso_hom

theorem integralSingularHomologyMap_eq_homologyMap (n : ℕ) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (c : integralSingularHomology n X) :
    (HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom f)) integralSingularCoefficients) n) c =
      integralSingularHomologyMap n f c :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyMap_eq_homologyMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyMap_eq_homologyMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyMap_eq_homologyMap ``Submission.DifferentialGeometry.Topology.integralSingularHomologyMap_eq_homologyMap

theorem integralSingularHomologyCoeffIso_hom_naturality (n : ℕ) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    (integralSingularHomologyCoeffIso n X).hom ≫
        (HomologicalComplex.homologyMap (SSet.chainComplexMap
          (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)) n) =
      (HomologicalComplex.homologyMap (SSet.chainComplexMap
          (TopCat.toSSet.map (TopCat.ofHom f)) integralSingularCoefficients) n) ≫
        (integralSingularHomologyCoeffIso n Y).hom := by
  have h := congrArg (fun k => HomologicalComplex.homologyMap k n)
    (integralSingularChainsCoeffIso_naturality f)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  rw [integralSingularHomologyCoeffIso_hom, integralSingularHomologyCoeffIso_hom]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyCoeffIso_hom_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyCoeffIso_hom_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyCoeffIso_hom_naturality ``Submission.DifferentialGeometry.Topology.integralSingularHomologyCoeffIso_hom_naturality

theorem integralSingularHomologyCoeffIso_naturality (n : ℕ) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (c : integralSingularHomology n X) :
    (integralSingularHomologyCoeffIso n Y).hom (integralSingularHomologyMap n f c) =
      (HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)) n)
        ((integralSingularHomologyCoeffIso n X).hom c) := by
  have h := congrArg (fun k => k c) (integralSingularHomologyCoeffIso_hom_naturality n f)
  simp only [ModuleCat.comp_apply] at h
  rw [integralSingularHomologyCoeffIso_hom]
  rw [← integralSingularHomologyMap_eq_homologyMap n f c]
  exact h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularHomologyCoeffIso_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularHomologyCoeffIso_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularHomologyCoeffIso_naturality ``Submission.DifferentialGeometry.Topology.integralSingularHomologyCoeffIso_naturality

def integralReducedSingularHomologyIso (n : ℕ) (X : Type) [TopologicalSpace X] :
    integralSingularHomology (n + 1) X ≅
      reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of X) (n + 1) :=
  integralSingularHomologyCoeffIso (n + 1) X ≪≫
    (reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) (TopCat.of X) n).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralReducedSingularHomologyIso then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralReducedSingularHomologyIso"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralReducedSingularHomologyIso ``Submission.DifferentialGeometry.Topology.integralReducedSingularHomologyIso

def integralReducedSingularHomologyEquiv (n : ℕ) (X : Type) [TopologicalSpace X] :
    integralSingularHomology (n + 1) X ≃ₗ[ℤ]
      reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of X) (n + 1) :=
  (integralReducedSingularHomologyIso n X).toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralReducedSingularHomologyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralReducedSingularHomologyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralReducedSingularHomologyEquiv ``Submission.DifferentialGeometry.Topology.integralReducedSingularHomologyEquiv

theorem integralReducedSingularHomologyEquiv_naturality (n : ℕ) {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (c : integralSingularHomology (n + 1) X) :
    reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) (n + 1)
        (integralReducedSingularHomologyEquiv n X c) =
      integralReducedSingularHomologyEquiv n Y (integralSingularHomologyMap (n + 1) f c) := by
  have h1 : reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) (n + 1)
      ((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) (TopCat.of X) n).inv
        ((integralSingularHomologyCoeffIso (n + 1) X).hom c)) =
      (reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ) (TopCat.of Y) n).inv
        ((HomologicalComplex.homologyMap (SSet.chainComplexMap
          (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)) (n + 1))
            ((integralSingularHomologyCoeffIso (n + 1) X).hom c)) := by
    have h := congrArg (fun k => k ((reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ)
      (TopCat.of X) n).inv ((integralSingularHomologyCoeffIso (n + 1) X).hom c)))
      (reducedSingularHomologySuccIso_naturality (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) n)
    simp only [ModuleCat.comp_apply] at h
    rw [Iso.inv_hom_id_apply] at h
    have h2 := congrArg (fun z => (reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ)
      (TopCat.of Y) n).inv z) h
    simpa only [Iso.hom_inv_id_apply] using h2
  have h2 : (HomologicalComplex.homologyMap (SSet.chainComplexMap
        (TopCat.toSSet.map (TopCat.ofHom f)) (ModuleCat.of ℤ ℤ)) (n + 1))
          ((integralSingularHomologyCoeffIso (n + 1) X).hom c) =
      (integralSingularHomologyCoeffIso (n + 1) Y).hom
        (integralSingularHomologyMap (n + 1) f c) :=
    (integralSingularHomologyCoeffIso_naturality (n + 1) f c).symm
  exact h1.trans (congrArg (fun z => (reducedSingularHomologySuccIso (ModuleCat.of ℤ ℤ)
    (TopCat.of Y) n).inv z) h2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralReducedSingularHomologyEquiv_naturality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralReducedSingularHomologyEquiv_naturality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralReducedSingularHomologyEquiv_naturality ``Submission.DifferentialGeometry.Topology.integralReducedSingularHomologyEquiv_naturality

theorem exists_linearMap_eq_one_iff_exists_reducedLinearMap (n : ℕ) (X : Type) [TopologicalSpace X]
    (c : integralSingularHomology (n + 1) X) :
    (∃ φ : integralSingularHomology (n + 1) X →ₗ[ℤ] ℤ, φ c = 1) ↔
      ∃ ψ : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of X) (n + 1) →ₗ[ℤ] ℤ,
        ψ (integralReducedSingularHomologyEquiv n X c) = 1 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨φ, hφ⟩ := h
    refine ⟨φ.comp (integralReducedSingularHomologyEquiv n X).symm.toLinearMap, ?_⟩
    exact (congrArg φ (LinearEquiv.symm_apply_apply
      (integralReducedSingularHomologyEquiv n X) c)).trans hφ
  · obtain ⟨ψ, hψ⟩ := h
    refine ⟨ψ.comp (integralReducedSingularHomologyEquiv n X).toLinearMap, ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hψ]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_linearMap_eq_one_iff_exists_reducedLinearMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_linearMap_eq_one_iff_exists_reducedLinearMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_linearMap_eq_one_iff_exists_reducedLinearMap ``Submission.DifferentialGeometry.Topology.exists_linearMap_eq_one_iff_exists_reducedLinearMap

private noncomputable def moduleCatIsoAddEquiv {A B : ModuleCat ℤ} (e : A ≅ B) : A ≃+ B where
  toFun := fun x => e.hom x
  invFun := fun y => e.inv y
  left_inv := fun x => by
    change e.inv (e.hom x) = x
    rw [Iso.hom_inv_id_apply]
  right_inv := fun y => by
    change e.hom (e.inv y) = y
    rw [Iso.inv_hom_id_apply]
  map_add' := fun x y => map_add (ConcreteCategory.hom e.hom) x y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.moduleCatIsoAddEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.moduleCatIsoAddEquiv target :: scope.openDecls } }

noncomputable def liftedSphereReducedHomologyEquiv :
    reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (liftedHomotopySphere 1)) 2 ≃+ ℤ :=
  (moduleCatIsoAddEquiv (reducedSingularHomologyIso (ModuleCat.of ℤ ℤ)
      (Homeomorph.ulift.toHomotopyEquiv) 2)).trans
    (DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.liftedSphereReducedHomologyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.liftedSphereReducedHomologyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.liftedSphereReducedHomologyEquiv ``Submission.DifferentialGeometry.Topology.liftedSphereReducedHomologyEquiv

theorem exists_reducedFunctional_integralLiftedSphereGenerator :
    ∃ ψ : reducedSingularHomology (ModuleCat.of ℤ ℤ)
        (TopCat.of (liftedHomotopySphere.{0} 1)) 2 →ₗ[ℤ] ℤ,
      ψ (integralReducedSingularHomologyEquiv 1 (liftedHomotopySphere.{0} 1)
        (integralLiftedSphereGenerator.{0} 1)) = 1 :=
  (exists_linearMap_eq_one_iff_exists_reducedLinearMap 1 (liftedHomotopySphere.{0} 1)
    (integralLiftedSphereGenerator.{0} 1)).mp
      ⟨integralLiftedSphereTopEquiv.{0} 1, integralLiftedSphereGenerator_coordinate.{0} 1⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.exists_reducedFunctional_integralLiftedSphereGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.exists_reducedFunctional_integralLiftedSphereGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.exists_reducedFunctional_integralLiftedSphereGenerator ``Submission.DifferentialGeometry.Topology.exists_reducedFunctional_integralLiftedSphereGenerator

theorem isSphereHomologyGenerator_squareSphereFundamentalClass_iff_exists_reducedFunctional :
    IsSphereHomologyGenerator.{0} 1 squareSphereFundamentalClass.{0} ↔
      ∃ ψ : reducedSingularHomology (ModuleCat.of ℤ ℤ)
          (TopCat.of (liftedHomotopySphere.{0} 1)) 2 →ₗ[ℤ] ℤ,
        ψ (integralReducedSingularHomologyEquiv 1 (liftedHomotopySphere.{0} 1)
          squareSphereFundamentalClass.{0}) = 1 := by
  have hgen : IsSphereHomologyGenerator.{0} 1 squareSphereFundamentalClass.{0} ↔
      ∃ φ : integralSingularHomology 2 (liftedHomotopySphere.{0} 1) →ₗ[ℤ] ℤ,
        φ squareSphereFundamentalClass.{0} = 1 :=
    isSphereHomologyGenerator_iff_exists_functional 1 squareSphereFundamentalClass.{0}
  exact hgen.trans (exists_linearMap_eq_one_iff_exists_reducedLinearMap 1
    (liftedHomotopySphere.{0} 1) squareSphereFundamentalClass.{0})

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isSphereHomologyGenerator_squareSphereFundamentalClass_iff_exists_reducedFunctional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isSphereHomologyGenerator_squareSphereFundamentalClass_iff_exists_reducedFunctional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isSphereHomologyGenerator_squareSphereFundamentalClass_iff_exists_reducedFunctional ``Submission.DifferentialGeometry.Topology.isSphereHomologyGenerator_squareSphereFundamentalClass_iff_exists_reducedFunctional

end DifferentialGeometry.Topology
