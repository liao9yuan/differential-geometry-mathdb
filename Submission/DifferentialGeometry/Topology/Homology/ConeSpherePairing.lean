import Submission.DifferentialGeometry.Topology.Homology.TwoCycleRealization
import Submission.DifferentialGeometry.Topology.Homology.HurewiczTwoAdditivity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicTopology _root_.ContinuousMap
open scoped _root_.Simplicial

namespace DifferentialGeometry.Topology

universe u

variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

def integralSingularConeSphereClass (x : X) (σ : integralSingularSimplex 2 X) :
    HomotopyGroup (Fin 2) X x :=
  (homotopyGroupFreeSphereEquiv 1 x).symm
    (ZerothHomotopy.mk (integralSingularConeSphereMap x σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeSphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeSphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeSphereClass ``Submission.DifferentialGeometry.Topology.integralSingularConeSphereClass

def integralSingularConeSpherePairing (x : X) :
    (integralSingularChains X).X 2 →ₗ[ℤ] Additive (HomotopyGroup (Fin 2) X x) :=
  (integralSingularChainBasis 2 X).constr ℕ
    (fun σ => Additive.ofMul (integralSingularConeSphereClass x σ))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeSpherePairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeSpherePairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeSpherePairing ``Submission.DifferentialGeometry.Topology.integralSingularConeSpherePairing

theorem integralSingularConeSpherePairing_simplex (x : X) (σ : integralSingularSimplex 2 X) :
    integralSingularConeSpherePairing x (integralSimplexChain 2 σ) =
      Additive.ofMul (integralSingularConeSphereClass x σ) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis 2 X).constr_basis ℕ _ σ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeSpherePairing_simplex then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeSpherePairing_simplex"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeSpherePairing_simplex ``Submission.DifferentialGeometry.Topology.integralSingularConeSpherePairing_simplex

variable (x : X)
    (hfaces : ∀ τ : integralSingularSimplex 3 X,
      integralSingularConeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ) *
        integralSingularConeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ) =
      integralSingularConeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ) *
        integralSingularConeSphereClass x ((TopCat.toSSet.obj (TopCat.of X)).δ 3 τ))

include hfaces

theorem integralSingularConeSpherePairing_boundary (b : (integralSingularChains X).X 3) :
    integralSingularConeSpherePairing x ((integralSingularChains X).d 3 2 b) = 0 := by
  have heq : (integralSingularConeSpherePairing x).comp
      ((integralSingularChains X).d 3 2).hom = 0 := by
    apply (integralSingularChainBasis 3 X).ext
    intro τ
    simp only [LinearMap.comp_apply, integralSingularChainBasis_apply, LinearMap.zero_apply]
    rw [integralSimplexChain_boundary, map_sum]
    simp only [map_zsmul, integralSingularConeSpherePairing_simplex]
    rw [Fin.sum_univ_four]
    norm_num
    have h := congrArg Additive.ofMul (hfaces τ)
    change Additive.ofMul (integralSingularConeSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 0 τ)) +
      Additive.ofMul (integralSingularConeSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 2 τ)) =
      Additive.ofMul (integralSingularConeSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 1 τ)) +
      Additive.ofMul (integralSingularConeSphereClass x
        ((TopCat.toSSet.obj (TopCat.of X)).δ 3 τ)) at h
    have hz := sub_eq_zero.mpr h
    convert hz using 1
    abel
  exact LinearMap.congr_fun heq b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeSpherePairing_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeSpherePairing_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeSpherePairing_boundary ``Submission.DifferentialGeometry.Topology.integralSingularConeSpherePairing_boundary

private theorem integralSingularConeSpherePairing_range_le_ker :
    LinearMap.range (integralSingularBoundaryToCycles 1 X) ≤
      ((integralSingularConeSpherePairing x).comp
        (Submodule.subtype (integralSingularCycles 1 X))).ker := by
  rw [LinearMap.range_le_ker_iff]
  apply LinearMap.ext
  intro b
  rw [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    integralSingularBoundaryToCycles_coe, integralSingularConeSpherePairing_boundary x hfaces]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.integralSingularConeSpherePairing_range_le_ker
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.integralSingularConeSpherePairing_range_le_ker target :: scope.openDecls } }

def integralSingularConeSphereHomologyPairing :
    integralSingularHomology 2 X →+ Additive (HomotopyGroup (Fin 2) X x) :=
  AddMonoidHom.mk' (fun y =>
    (Submodule.liftQ (LinearMap.range (integralSingularBoundaryToCycles 1 X))
      ((integralSingularConeSpherePairing x).comp (integralSingularCycles 1 X).subtype)
      (integralSingularConeSpherePairing_range_le_ker x hfaces))
        ((integralSingularHomologyCycleEquiv 1 X) y)) (by
          intro y₁ y₂
          rw [map_add, map_add])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeSphereHomologyPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeSphereHomologyPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeSphereHomologyPairing ``Submission.DifferentialGeometry.Topology.integralSingularConeSphereHomologyPairing

theorem integralSingularConeSphereHomologyPairing_cycle (z : integralSingularCycles 1 X) :
    integralSingularConeSphereHomologyPairing x hfaces (integralSingularCycleClass 1 X z) =
      integralSingularConeSpherePairing x z.val := by
  change (Submodule.liftQ (LinearMap.range (integralSingularBoundaryToCycles 1 X))
      ((integralSingularConeSpherePairing x).comp (integralSingularCycles 1 X).subtype)
      (integralSingularConeSpherePairing_range_le_ker x hfaces))
      ((integralSingularHomologyCycleEquiv 1 X) (integralSingularCycleClass 1 X z)) = _
  rw [integralSingularCycleClass, AddEquiv.apply_symm_apply, Submodule.liftQ_apply,
    LinearMap.comp_apply, Submodule.subtype_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.integralSingularConeSphereHomologyPairing_cycle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.integralSingularConeSphereHomologyPairing_cycle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.integralSingularConeSphereHomologyPairing_cycle ``Submission.DifferentialGeometry.Topology.integralSingularConeSphereHomologyPairing_cycle

omit hfaces in
theorem sphereHurewicz_integralSingularConeSphereClass (σ : integralSingularSimplex 2 X) :
    sphereHurewicz 1 x (simplexBoundarySphereClass.{u} 1)
      (integralSingularConeSphereClass x σ) =
        integralSingularCycleClass 1 X
          (integralSingularTwoCycleProjection x (integralSimplexChain 2 σ)) := by
  change freeSphereHomologyImage 1 (simplexBoundarySphereClass.{u} 1)
    ((homotopyGroupFreeSphereEquiv 1 x) ((homotopyGroupFreeSphereEquiv 1 x).symm
      (ZerothHomotopy.mk (integralSingularConeSphereMap x σ)))) = _
  rw [Equiv.apply_symm_apply, integralSingularConeSphereMap_simplexBoundarySphereClass]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_integralSingularConeSphereClass then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_integralSingularConeSphereClass"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_integralSingularConeSphereClass ``Submission.DifferentialGeometry.Topology.sphereHurewicz_integralSingularConeSphereClass

omit hfaces in
private def sphereHurewiczTwoLinearMap
    (c : integralSingularHomology 2 (liftedHomotopySphere.{u} 1)) :
    Additive (HomotopyGroup (Fin 2) X x) →ₗ[ℤ] integralSingularHomology 2 X where
  toFun a := sphereHurewicz 1 x c a.toMul
  map_add' a b := sphereHurewicz_two_mul x c a.toMul b.toMul
  map_smul' k a :=
    map_intCast_smul
      (AddMonoidHom.mk' (fun b : Additive (HomotopyGroup (Fin 2) X x) =>
        sphereHurewicz 1 x c b.toMul)
        (fun b d => sphereHurewicz_two_mul x c b.toMul d.toMul)) ℤ ℤ k a

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.sphereHurewiczTwoLinearMap
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.sphereHurewiczTwoLinearMap target :: scope.openDecls } }

omit hfaces in
private theorem sphereHurewicz_integralSingularConeSpherePairing
    (b : (integralSingularChains X).X 2) :
    sphereHurewicz 1 x (simplexBoundarySphereClass.{u} 1)
      (integralSingularConeSpherePairing x b).toMul =
        integralSingularCycleClass 1 X (integralSingularTwoCycleProjection x b) := by
  have heq : (sphereHurewiczTwoLinearMap x (simplexBoundarySphereClass.{u} 1)).comp
      (integralSingularConeSpherePairing x) =
        (integralSingularCycleClassLinearMap 1 X).comp
          (integralSingularTwoCycleProjection x) := by
    apply (integralSingularChainBasis 2 X).ext
    intro σ
    simp only [LinearMap.comp_apply, integralSingularChainBasis_apply,
      integralSingularConeSpherePairing_simplex, integralSingularCycleClassLinearMap_apply]
    exact sphereHurewicz_integralSingularConeSphereClass x σ
  exact LinearMap.congr_fun heq b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.sphereHurewicz_integralSingularConeSpherePairing
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.sphereHurewicz_integralSingularConeSpherePairing target :: scope.openDecls } }

theorem sphereHurewicz_integralSingularConeSphereHomologyPairing
    (y : integralSingularHomology 2 X) :
    sphereHurewicz 1 x (simplexBoundarySphereClass.{u} 1)
      (integralSingularConeSphereHomologyPairing x hfaces y).toMul = y := by
  obtain ⟨z, rfl⟩ := integralSingularCycleClass_surjective 1 X y
  rw [integralSingularConeSphereHomologyPairing_cycle,
    sphereHurewicz_integralSingularConeSpherePairing, integralSingularTwoCycleProjection_cycle]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.sphereHurewicz_integralSingularConeSphereHomologyPairing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.sphereHurewicz_integralSingularConeSphereHomologyPairing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.sphereHurewicz_integralSingularConeSphereHomologyPairing ``Submission.DifferentialGeometry.Topology.sphereHurewicz_integralSingularConeSphereHomologyPairing

end DifferentialGeometry.Topology
