import Submission.DifferentialGeometry.Topology.LocalDegree.SphereHomology
import Submission.DifferentialGeometry.Topology.LocalDegree.ZeroSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
open _root_.CategoryTheory _root_.CategoryTheory.Limits
noncomputable section
namespace DifferentialGeometry.LocalDegree
open _root_.Submission.DifferentialGeometry.Homology


abbrev EuclideanSphere (d : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.EuclideanSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.EuclideanSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.EuclideanSphere ``Submission.DifferentialGeometry.LocalDegree.EuclideanSphere

def euclideanZeroSphereHomeomorphReal : EuclideanSphere 0 ≃ₜ ZeroSphere :=
  ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm.toHomeomorph).subtype
    (fun x ↦ by
      simp only [Metric.mem_sphere, dist_zero_right]
      exact ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm.norm_map x).symm ▸ Iff.rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanZeroSphereHomeomorphReal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanZeroSphereHomeomorphReal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanZeroSphereHomeomorphReal ``Submission.DifferentialGeometry.LocalDegree.euclideanZeroSphereHomeomorphReal


@[simp]
theorem euclideanZeroSphereHomeomorphReal_north :
    euclideanZeroSphereHomeomorphReal (euclideanNorth 0) = zeroSpherePositive := by
  apply Subtype.ext
  apply (OrthonormalBasis.singleton (Fin 1) ℝ).repr.injective
  change (OrthonormalBasis.singleton (Fin 1) ℝ).repr
      ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm (euclideanNorth 0).val) =
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr 1
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext i
  have hi : i = 0 := Fin.eq_zero i
  simp [euclideanNorth, hi]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanZeroSphereHomeomorphReal_north then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanZeroSphereHomeomorphReal_north"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanZeroSphereHomeomorphReal_north ``Submission.DifferentialGeometry.LocalDegree.euclideanZeroSphereHomeomorphReal_north

private def moduleIsoAddEquiv {A B : ModuleCat ℤ} (e : A ≅ B) : A ≃+ B where
  toFun := e.hom
  invFun := e.inv
  left_inv x := congr($(e.hom_inv_id) x)
  right_inv x := congr($(e.inv_hom_id) x)
  map_add' x y := e.hom.hom.map_add' x y

run_cmd do
  let target := ``Submission.DifferentialGeometry.LocalDegree.moduleIsoAddEquiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.LocalDegree.moduleIsoAddEquiv target :: scope.openDecls } }

def realZeroSphereReducedHomologyEquiv :
    reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of ZeroSphere) 0 ≃+ zeroSphereReducedH0 where
  toFun c := (reducedSingularHomologyZeroIso (ModuleCat.of ℤ ℤ) (TopCat.of ZeroSphere)).hom c
  invFun c := (reducedSingularHomologyZeroIso (ModuleCat.of ℤ ℤ) (TopCat.of ZeroSphere)).inv c
  left_inv c := congr($((reducedSingularHomologyZeroIso (ModuleCat.of ℤ ℤ)
    (TopCat.of ZeroSphere)).hom_inv_id) c)
  right_inv c := congr($((reducedSingularHomologyZeroIso (ModuleCat.of ℤ ℤ)
    (TopCat.of ZeroSphere)).inv_hom_id) c)
  map_add' c d := (reducedSingularHomologyZeroIso (ModuleCat.of ℤ ℤ)
    (TopCat.of ZeroSphere)).hom.hom.map_add' c d

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.realZeroSphereReducedHomologyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.realZeroSphereReducedHomologyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.realZeroSphereReducedHomologyEquiv ``Submission.DifferentialGeometry.LocalDegree.realZeroSphereReducedHomologyEquiv


theorem realZeroSphereReducedHomologyEquiv_map (f : C(ZeroSphere, ZeroSphere))
    (c : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of ZeroSphere) 0) :
    realZeroSphereReducedHomologyEquiv
        (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ) (TopCat.ofHom f) 0 c) =
      zeroSphereReducedMap f (realZeroSphereReducedHomologyEquiv c) := by
  apply Subtype.ext
  exact congr($(reducedSingularHomologyZeroIso_naturality (ModuleCat.of ℤ ℤ) (TopCat.ofHom f)) c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.realZeroSphereReducedHomologyEquiv_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.realZeroSphereReducedHomologyEquiv_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.realZeroSphereReducedHomologyEquiv_map ``Submission.DifferentialGeometry.LocalDegree.realZeroSphereReducedHomologyEquiv_map

def euclideanZeroSphereReducedHomologyEquiv :
    reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere 0)) 0 ≃+ ℤ :=
  (moduleIsoAddEquiv (reducedSingularHomologyIso (ModuleCat.of ℤ ℤ)
    euclideanZeroSphereHomeomorphReal.toHomotopyEquiv 0)).trans
      (realZeroSphereReducedHomologyEquiv.trans zeroSphereReducedEquiv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanZeroSphereReducedHomologyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanZeroSphereReducedHomologyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanZeroSphereReducedHomologyEquiv ``Submission.DifferentialGeometry.LocalDegree.euclideanZeroSphereReducedHomologyEquiv


theorem euclideanZeroSphereReducedHomologyEquiv_apply
    (c : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere 0)) 0) :
    euclideanZeroSphereReducedHomologyEquiv c =
      zeroSphereReducedEquiv (realZeroSphereReducedHomologyEquiv
        (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
          (TopCat.ofHom euclideanZeroSphereHomeomorphReal.toHomotopyEquiv.toFun) 0 c)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanZeroSphereReducedHomologyEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanZeroSphereReducedHomologyEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanZeroSphereReducedHomologyEquiv_apply ``Submission.DifferentialGeometry.LocalDegree.euclideanZeroSphereReducedHomologyEquiv_apply

def euclideanSphereTopReducedHomologyEquiv : (d : ℕ) →
    reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere d)) d ≃+ ℤ
  | 0 => euclideanZeroSphereReducedHomologyEquiv
  | d + 1 => (moduleIsoAddEquiv
      (euclideanSphereReducedHomologySuccIso (ModuleCat.of ℤ ℤ) (d + 1) d)).trans
        (euclideanSphereTopReducedHomologyEquiv d)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv


@[simp]
theorem euclideanSphereTopReducedHomologyEquiv_zero :
    euclideanSphereTopReducedHomologyEquiv 0 = euclideanZeroSphereReducedHomologyEquiv := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_zero ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_zero

theorem euclideanSphereTopReducedHomologyEquiv_succ (d : ℕ)
    (c : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere (d + 1))) (d + 1)) :
    euclideanSphereTopReducedHomologyEquiv (d + 1) c =
      euclideanSphereTopReducedHomologyEquiv d
        ((euclideanSphereReducedHomologySuccIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom c) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_succ ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_succ


def euclideanSphereTopGenerator (d : ℕ) :
    reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere d)) d :=
  (euclideanSphereTopReducedHomologyEquiv d).symm 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator


@[simp]
theorem euclideanSphereTopReducedHomologyEquiv_generator (d : ℕ) :
    euclideanSphereTopReducedHomologyEquiv d (euclideanSphereTopGenerator d) = 1 :=
  (euclideanSphereTopReducedHomologyEquiv d).apply_symm_apply 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_generator ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_generator


theorem euclideanSphereTopGenerator_ne_zero (d : ℕ) : euclideanSphereTopGenerator d ≠ 0 := by
  intro h
  have hh := congrArg (euclideanSphereTopReducedHomologyEquiv d) h
  simp at hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_ne_zero ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_ne_zero


theorem euclideanSphereTopReducedHomologyEquiv_smul_generator (d : ℕ)
    (c : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere d)) d) :
    euclideanSphereTopReducedHomologyEquiv d c • euclideanSphereTopGenerator d = c := by
  apply (euclideanSphereTopReducedHomologyEquiv d).injective
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_smul_generator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_smul_generator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_smul_generator ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereTopReducedHomologyEquiv_smul_generator


theorem euclideanSphereTopGenerator_unique_coefficient (d : ℕ)
    (c : reducedSingularHomology (ModuleCat.of ℤ ℤ) (TopCat.of (EuclideanSphere d)) d) :
    ∃! m : ℤ, c = m • euclideanSphereTopGenerator d := by
  refine ⟨euclideanSphereTopReducedHomologyEquiv d c,
    (euclideanSphereTopReducedHomologyEquiv_smul_generator d c).symm, ?_⟩
  intro m hm
  have h := congrArg (euclideanSphereTopReducedHomologyEquiv d) hm
  simpa using h.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_unique_coefficient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_unique_coefficient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_unique_coefficient ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_unique_coefficient

theorem euclideanSphereTopGenerator_zero_comparison :
    realZeroSphereReducedHomologyEquiv
      (reducedSingularHomologyMap (ModuleCat.of ℤ ℤ)
        (TopCat.ofHom euclideanZeroSphereHomeomorphReal.toHomotopyEquiv.toFun) 0
          (euclideanSphereTopGenerator 0)) = zeroSphereGenerator := by
  apply zeroSphereReducedEquiv.injective
  change euclideanSphereTopReducedHomologyEquiv 0 (euclideanSphereTopGenerator 0) = _
  rw [euclideanSphereTopReducedHomologyEquiv_generator, zeroSphereReducedEquiv_generator]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_zero_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_zero_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_zero_comparison ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_zero_comparison


theorem euclideanSphereTopGenerator_connecting (d : ℕ) :
    (euclideanSphereReducedHomologySuccIso (ModuleCat.of ℤ ℤ) (d + 1) d).hom
        (euclideanSphereTopGenerator (d + 1)) = euclideanSphereTopGenerator d := by
  apply (euclideanSphereTopReducedHomologyEquiv d).injective
  rw [← euclideanSphereTopReducedHomologyEquiv_succ]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_connecting then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_connecting"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_connecting ``Submission.DifferentialGeometry.LocalDegree.euclideanSphereTopGenerator_connecting

end DifferentialGeometry.LocalDegree
