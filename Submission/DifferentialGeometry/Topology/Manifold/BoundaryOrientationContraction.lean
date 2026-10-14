import Mathlib.LinearAlgebra.Orientation
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Function _root_.Module
namespace DifferentialGeometry.Topology.Manifold
variable {E F G : Type*} [AddCommGroup E] [Module ℝ E]
variable [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]

private def normalFirstBasis (e : (ℝ × F) ≃ₗ[ℝ] E) (b : _root_.Module.Basis (Fin 2) ℝ F) : _root_.Module.Basis (Fin 3) ℝ E :=
  (((Basis.singleton (Fin 1) ℝ).prod b).reindex finSumFinEquiv).map e

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstBasis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.normalFirstBasis target :: scope.openDecls } }

private theorem normalFirstBasis_zero (e : (ℝ × F) ≃ₗ[ℝ] E) (b : _root_.Module.Basis (Fin 2) ℝ F) :
    normalFirstBasis e b 0 = e (1, 0) := by
  simp only [normalFirstBasis, Basis.map_apply, Basis.coe_reindex]
  change e (((Basis.singleton (Fin 1) ℝ).prod b) (Sum.inl 0)) = e (1, 0)
  simp [Basis.prod_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstBasis_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.normalFirstBasis_zero target :: scope.openDecls } }

private theorem normalFirstBasis_succ (e : (ℝ × F) ≃ₗ[ℝ] E) (b : _root_.Module.Basis (Fin 2) ℝ F) (i : Fin 2) :
    normalFirstBasis e b i.succ = e (0, b i) := by
  simp only [normalFirstBasis, Basis.map_apply, Basis.coe_reindex]
  fin_cases i
  · change e (((Basis.singleton (Fin 1) ℝ).prod b) (Sum.inr 0)) = e (0, b 0)
    simp [Basis.prod_apply]
  · change e (((Basis.singleton (Fin 1) ℝ).prod b) (Sum.inr 1)) = e (0, b 1)
    simp [Basis.prod_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstBasis_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.normalFirstBasis_succ target :: scope.openDecls } }

def normalFirstContraction (e : (ℝ × F) ≃ₗ[ℝ] E) :
    (E [⋀^Fin 3]→ₗ[ℝ] ℝ) →ₗ[ℝ] (F [⋀^Fin 2]→ₗ[ℝ] ℝ) where
  toFun ω := (ω.curryLeft (e (1, 0))).compLinearMap
    (e.toLinearMap.comp (LinearMap.inr ℝ ℝ F))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.normalFirstContraction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.normalFirstContraction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.normalFirstContraction ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstContraction

theorem normalFirstContraction_apply (e : (ℝ × F) ≃ₗ[ℝ] E)
    (ω : E [⋀^Fin 3]→ₗ[ℝ] ℝ) (v : Fin 2 → F) :
    normalFirstContraction e ω v = ω (Matrix.vecCons (e (1, 0)) (fun i => e (0, v i))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.normalFirstContraction_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.normalFirstContraction_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.normalFirstContraction_apply ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstContraction_apply

theorem normalFirstContraction_ne_zero (e : (ℝ × F) ≃ₗ[ℝ] E) (b : _root_.Module.Basis (Fin 2) ℝ F)
    (ω : E [⋀^Fin 3]→ₗ[ℝ] ℝ) (hω : ω ≠ 0) : normalFirstContraction e ω ≠ 0 := by
  intro hz
  have hval : normalFirstContraction e ω b = ω (normalFirstBasis e b) := by
    rw [normalFirstContraction_apply]
    congr 1
    funext i
    cases i using Fin.cases with
    | zero => exact (normalFirstBasis_zero e b).symm
    | succ i => exact (normalFirstBasis_succ e b i).symm
  have hne := (ω.map_basis_ne_zero_iff (normalFirstBasis e b)).mpr hω
  apply hne
  rw [← hval, hz]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.normalFirstContraction_ne_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.normalFirstContraction_ne_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.normalFirstContraction_ne_zero ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstContraction_ne_zero

def normalFirstOrientation (e : (ℝ × F) ≃ₗ[ℝ] E) (b : _root_.Module.Basis (Fin 2) ℝ F) :
    Orientation ℝ E (Fin 3) → Orientation ℝ F (Fin 2) :=
  Quotient.map (fun ω => (⟨normalFirstContraction e ω.val,
    normalFirstContraction_ne_zero e b ω.val ω.property⟩ : RayVector ℝ (F [⋀^Fin 2]→ₗ[ℝ] ℝ)))
    (fun _ _ h => h.map (normalFirstContraction e))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.normalFirstOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.normalFirstOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.normalFirstOrientation ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstOrientation

theorem normalFirstOrientation_apply (e : (ℝ × F) ≃ₗ[ℝ] E) (b : _root_.Module.Basis (Fin 2) ℝ F)
    (ω : E [⋀^Fin 3]→ₗ[ℝ] ℝ) (hω : ω ≠ 0) :
    normalFirstOrientation e b (rayOfNeZero ℝ ω hω) =
      rayOfNeZero ℝ (normalFirstContraction e ω) (normalFirstContraction_ne_zero e b ω hω) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.normalFirstOrientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.normalFirstOrientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.normalFirstOrientation_apply ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstOrientation_apply

theorem normalFirstOrientation_basis_independent (e : (ℝ × F) ≃ₗ[ℝ] E)
    (b b' : _root_.Module.Basis (Fin 2) ℝ F) (o : Orientation ℝ E (Fin 3)) :
    normalFirstOrientation e b o = normalFirstOrientation e b' o := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.normalFirstOrientation_basis_independent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.normalFirstOrientation_basis_independent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.normalFirstOrientation_basis_independent ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstOrientation_basis_independent

theorem normalFirstOrientation_neg (e : (ℝ × F) ≃ₗ[ℝ] E) (b : _root_.Module.Basis (Fin 2) ℝ F)
    (o : Orientation ℝ E (Fin 3)) : normalFirstOrientation e b (-o) = -normalFirstOrientation e b o := by
  induction o using Module.Ray.ind with
  | h ω hω =>
    rw [neg_rayOfNeZero, normalFirstOrientation_apply, normalFirstOrientation_apply, neg_rayOfNeZero]
    congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.normalFirstOrientation_neg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.normalFirstOrientation_neg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.normalFirstOrientation_neg ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstOrientation_neg

def normalFirstReflection : (ℝ × F) ≃ₗ[ℝ] (ℝ × F) :=
  (LinearEquiv.neg ℝ : ℝ ≃ₗ[ℝ] ℝ).prodCongr (LinearEquiv.refl ℝ F)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.normalFirstReflection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.normalFirstReflection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.normalFirstReflection ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstReflection

private theorem normalFirstContraction_reflect (e : (ℝ × F) ≃ₗ[ℝ] E)
    (ω : E [⋀^Fin 3]→ₗ[ℝ] ℝ) :
    normalFirstContraction (normalFirstReflection.trans e) ω = -normalFirstContraction e ω := by
  ext v
  simp only [normalFirstContraction_apply, normalFirstReflection, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.neg_apply, LinearEquiv.refl_apply, neg_zero,
    AlternatingMap.neg_apply]
  change ω.curryLeft (e (-1, 0)) (fun i => e (0, v i)) =
    -(ω.curryLeft (e (1, 0)) (fun i => e (0, v i)))
  have he : e (-1, 0) = -e (1, 0) := by
    have h := map_neg e (1, (0 : F))
    simpa only [Prod.neg_mk, neg_zero] using h
  rw [he, map_neg]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstContraction_reflect
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Topology.Manifold.normalFirstContraction_reflect target :: scope.openDecls } }

theorem normalFirstOrientation_reflect_normal (e : (ℝ × F) ≃ₗ[ℝ] E)
    (b : _root_.Module.Basis (Fin 2) ℝ F) (o : Orientation ℝ E (Fin 3)) :
    normalFirstOrientation (normalFirstReflection.trans e) b o = -normalFirstOrientation e b o := by
  induction o using Module.Ray.ind with
  | h ω hω =>
    rw [normalFirstOrientation_apply, normalFirstOrientation_apply, neg_rayOfNeZero]
    congr 1
    exact normalFirstContraction_reflect e ω

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.normalFirstOrientation_reflect_normal then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.normalFirstOrientation_reflect_normal"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.normalFirstOrientation_reflect_normal ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstOrientation_reflect_normal

theorem normalFirstOrientation_map (e : (ℝ × F) ≃ₗ[ℝ] E) (g : E ≃ₗ[ℝ] G)
    (b : _root_.Module.Basis (Fin 2) ℝ F) (o : Orientation ℝ E (Fin 3)) :
    normalFirstOrientation (e.trans g) b (Orientation.map (Fin 3) g o) = normalFirstOrientation e b o := by
  induction o using Module.Ray.ind with
  | h ω hω =>
    rw [Orientation.map_apply, normalFirstOrientation_apply, normalFirstOrientation_apply]
    congr 1
    ext v
    simp only [normalFirstContraction_apply, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    cases i using Fin.cases <;> simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.Manifold.normalFirstOrientation_map then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.Manifold.normalFirstOrientation_map"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.Manifold.normalFirstOrientation_map ``Submission.DifferentialGeometry.Topology.Manifold.normalFirstOrientation_map
end DifferentialGeometry.Topology.Manifold
