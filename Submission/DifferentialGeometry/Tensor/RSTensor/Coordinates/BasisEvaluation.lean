import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Tensor.Coordinates.ModelBasis
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Tensor.Multilinear

noncomputable section


namespace DifferentialGeometry
namespace Tensor
namespace Coordinates

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]

noncomputable def eval0SLinear (n : ℕ) :
    Tensor0SModel n ℝ E →ₗ[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) where
  toFun := fun Φ φ => Φ (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k))
  map_add' Φ₁ Φ₂ := by
    funext φ
    simp [add_apply]
  map_smul' c Φ := by
    funext φ
    simp [smul_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.eval0SLinear then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.eval0SLinear"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.eval0SLinear ``Submission.DifferentialGeometry.Tensor.Coordinates.eval0SLinear

@[simp] lemma eval0SLinear_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    eval0SLinear (E := E) n Φ φ =
      Φ (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.eval0SLinear_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.eval0SLinear_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.eval0SLinear_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.eval0SLinear_apply

private lemma eval0SLinear_injective (n : ℕ) :
    Function.Injective (eval0SLinear (E := E) n) := by
  intro Φ₁ Φ₂ h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (e := fun _ : Fin n => DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) ?_
  intro v
  exact congr_fun h v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.eval0SLinear_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.eval0SLinear_injective target :: scope.openDecls } }

private lemma finrank_tensor0SModel_local (n : ℕ) :
    Module.finrank ℝ (Tensor0SModel n ℝ E) =
      (Module.finrank ℝ E) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      rw [(continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.finrank_eq]
      exact Module.finrank_self ℝ
  | succ n ih =>
      rw [(continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) ℝ).toLinearEquiv.finrank_eq]
      let φ : (E →L[ℝ] Tensor0SModel n ℝ E) ≃ₗ[ℝ]
          (E →ₗ[ℝ] Tensor0SModel n ℝ E) :=
        { toFun := fun f => f.toLinearMap
          invFun := fun f => LinearMap.toContinuousLinearMap f
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      rw [φ.finrank_eq, Module.finrank_linearMap, ih]
      ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.finrank_tensor0SModel_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.finrank_tensor0SModel_local target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma finrank_basis_pi_local (n : ℕ) :
    Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) =
      (Module.finrank ℝ E) ^ n := by
  rw [Module.finrank_pi, Fintype.card_pi]
  simp [Fintype.card_fin]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.finrank_basis_pi_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.finrank_basis_pi_local target :: scope.openDecls } }

private lemma eval0SLinear_bijective (n : ℕ) :
    Function.Bijective (eval0SLinear (E := E) n) := by
  have h_inj := eval0SLinear_injective (E := E) n
  refine ⟨h_inj, ?_⟩
  have h_eq : Module.finrank ℝ (Tensor0SModel n ℝ E) =
      Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) := by
    rw [finrank_tensor0SModel_local, finrank_basis_pi_local]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_eq).mp h_inj

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.eval0SLinear_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.eval0SLinear_bijective target :: scope.openDecls } }

noncomputable def eval0SLinearEquiv (n : ℕ) :
    Tensor0SModel n ℝ E ≃ₗ[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) :=
  LinearEquiv.ofBijective (eval0SLinear (E := E) n)
    (eval0SLinear_bijective (E := E) n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.eval0SLinearEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.eval0SLinearEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.eval0SLinearEquiv ``Submission.DifferentialGeometry.Tensor.Coordinates.eval0SLinearEquiv

@[simp] private lemma eval0SLinearEquiv_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    eval0SLinearEquiv (E := E) n Φ φ =
      Φ (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.eval0SLinearEquiv_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.eval0SLinearEquiv_apply target :: scope.openDecls } }

noncomputable def eval0SCLE (n : ℕ) :
    Tensor0SModel n ℝ E ≃L[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) :=
  (eval0SLinearEquiv (E := E) n).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.eval0SCLE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.eval0SCLE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.eval0SCLE ``Submission.DifferentialGeometry.Tensor.Coordinates.eval0SCLE

@[simp] lemma eval0SCLE_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    eval0SCLE (E := E) n Φ φ =
      Φ (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.eval0SCLE_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.eval0SCLE_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.eval0SCLE_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.eval0SCLE_apply

noncomputable def evalAtBasisLinearTensorRSModel (r s : ℕ) :
    TensorRSModel r s ℝ E →ₗ[ℝ]
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) → ℝ) where
  toFun := fun T p =>
    (T ((eval0SCLE (E := E) r).symm (Pi.single p.1 (1 : ℝ))))
      (fun k : Fin s => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (p.2 k))
  map_add' T₁ T₂ := by
    funext p
    simp [add_apply, add_apply]
  map_smul' c T := by
    funext p
    simp [smul_apply, smul_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.evalAtBasisLinearTensorRSModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.evalAtBasisLinearTensorRSModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.evalAtBasisLinearTensorRSModel ``Submission.DifferentialGeometry.Tensor.Coordinates.evalAtBasisLinearTensorRSModel

@[simp] lemma evalAtBasisLinear_TensorRSModel_apply (r s : ℕ)
    (T : TensorRSModel r s ℝ E)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    evalAtBasisLinearTensorRSModel (E := E) r s T (Idx, Jdx) =
      (T ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))))
        (fun k : Fin s => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (Jdx k)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.evalAtBasisLinear_TensorRSModel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.evalAtBasisLinear_TensorRSModel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.evalAtBasisLinear_TensorRSModel_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.evalAtBasisLinear_TensorRSModel_apply

private lemma evalAtBasisLinear_TensorRSModel_injective (r s : ℕ) :
    Function.Injective (evalAtBasisLinearTensorRSModel (E := E) r s) := by
  intro T₁ T₂ h
  have h_pt :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
        T₁ ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) =
        T₂ ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))) := by
    intro Idx
    apply eval0SLinear_injective (E := E) s
    funext Jdx
    have h_pair := congr_fun h (Idx, Jdx)
    simpa [evalAtBasisLinearTensorRSModel, eval0SLinear_apply] using h_pair
  let bPi : Module.Basis (Fin r → Fin (Module.finrank ℝ E)) ℝ
      ((Fin r → Fin (Module.finrank ℝ E)) → ℝ) :=
    Pi.basisFun ℝ (Fin r → Fin (Module.finrank ℝ E))
  let bTen : Module.Basis (Fin r → Fin (Module.finrank ℝ E)) ℝ
      (Tensor0SModel r ℝ E) :=
    bPi.map (eval0SLinearEquiv (E := E) r).symm
  have h_basis :
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
        bTen Idx =
        (eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ)) := by
    intro Idx
    have : bPi Idx = Pi.single Idx (1 : ℝ) := by
      simp [bPi, Pi.basisFun_apply]
    simp [bTen, Module.Basis.map_apply, this, eval0SCLE]
  have h_linear :
      (T₁ : Tensor0SModel r ℝ E →ₗ[ℝ] Tensor0SModel s ℝ E) =
      (T₂ : Tensor0SModel r ℝ E →ₗ[ℝ] Tensor0SModel s ℝ E) := by
    refine Module.Basis.ext bTen ?_
    intro Idx
    rw [h_basis Idx]
    exact h_pt Idx
  exact ContinuousLinearMap.coe_injective h_linear

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.evalAtBasisLinear_TensorRSModel_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.evalAtBasisLinear_TensorRSModel_injective target :: scope.openDecls } }

private lemma finrank_tensorRSModel_local (r s : ℕ) :
    Module.finrank ℝ (TensorRSModel r s ℝ E) =
      (Module.finrank ℝ E) ^ (r + s) := by
  have : FiniteDimensional ℝ (Tensor0SModel r ℝ E) :=
    continuousMultilinearMap_finiteDimensional r
  have : FiniteDimensional ℝ (Tensor0SModel s ℝ E) :=
    continuousMultilinearMap_finiteDimensional s
  have : Module.Free ℝ (Tensor0SModel s ℝ E) := inferInstance
  have e : (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) ≃ₗ[ℝ]
      (Tensor0SModel r ℝ E →ₗ[ℝ] Tensor0SModel s ℝ E) :=
    LinearMap.toContinuousLinearMap.symm
  change Module.finrank ℝ (Tensor0SModel r ℝ E →L[ℝ] Tensor0SModel s ℝ E) =
      (Module.finrank ℝ E) ^ (r + s)
  rw [e.finrank_eq, Module.finrank_linearMap,
    finrank_tensor0SModel_local (E := E) r,
    finrank_tensor0SModel_local (E := E) s, ← pow_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.finrank_tensorRSModel_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.finrank_tensorRSModel_local target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma finrank_basis_pair_pi_local (r s : ℕ) :
    Module.finrank ℝ
      (((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E))) → ℝ) =
      (Module.finrank ℝ E) ^ (r + s) := by
  rw [Module.finrank_pi, Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
  simp [Fintype.card_fin, pow_add]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.finrank_basis_pair_pi_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.finrank_basis_pair_pi_local target :: scope.openDecls } }

private lemma evalAtBasisLinear_TensorRSModel_bijective (r s : ℕ) :
    Function.Bijective (evalAtBasisLinearTensorRSModel (E := E) r s) := by
  have : FiniteDimensional ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_finiteDimensional r s
  have h_inj := evalAtBasisLinear_TensorRSModel_injective (E := E) r s
  refine ⟨h_inj, ?_⟩
  have h_eq : Module.finrank ℝ (TensorRSModel r s ℝ E) =
      Module.finrank ℝ
        (((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) → ℝ) := by
    rw [finrank_tensorRSModel_local, finrank_basis_pair_pi_local]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_eq).mp h_inj

run_cmd do
  let target := ``Submission.DifferentialGeometry.Tensor.Coordinates.evalAtBasisLinear_TensorRSModel_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Tensor.Coordinates.evalAtBasisLinear_TensorRSModel_bijective target :: scope.openDecls } }

noncomputable def evalAtBasisCLETensorRSModel (r s : ℕ) :
    TensorRSModel r s ℝ E ≃L[ℝ]
      ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)) → ℝ) :=
  haveI : FiniteDimensional ℝ (TensorRSModel r s ℝ E) :=
    tensorRSModel_finiteDimensional r s
  (LinearEquiv.ofBijective (evalAtBasisLinearTensorRSModel (E := E) r s)
    (evalAtBasisLinear_TensorRSModel_bijective (E := E) r s)).toContinuousLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.evalAtBasisCLETensorRSModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.evalAtBasisCLETensorRSModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.evalAtBasisCLETensorRSModel ``Submission.DifferentialGeometry.Tensor.Coordinates.evalAtBasisCLETensorRSModel

@[simp] lemma evalAtBasisCLE_TensorRSModel_apply (r s : ℕ)
    (T : TensorRSModel r s ℝ E)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    evalAtBasisCLETensorRSModel (E := E) r s T (Idx, Jdx) =
      (T ((eval0SCLE (E := E) r).symm (Pi.single Idx (1 : ℝ))))
        (fun k : Fin s => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (Jdx k)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.evalAtBasisCLE_TensorRSModel_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.evalAtBasisCLE_TensorRSModel_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.evalAtBasisCLE_TensorRSModel_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.evalAtBasisCLE_TensorRSModel_apply

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
theorem contMDiffOn_into_tensorRSModel_of_eval_basis
    {r s : ℕ}
    {f : M → (ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
              ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)}
    {U : Set M} :
    ContMDiffOn I
      𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
            ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) ∞ f U ↔
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun b : M =>
            evalAtBasisCLETensorRSModel (E := E) r s (f b) (Idx, Jdx)) U := by
  constructor
  · intro hf Idx Jdx
    have hCLE :
        ContMDiff
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
                ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ)
          𝓘(ℝ, (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)) → ℝ) ∞
          (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
                    ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ =>
            evalAtBasisCLETensorRSModel (E := E) r s T) :=
      (evalAtBasisCLETensorRSModel (E := E) r s).toContinuousLinearMap.contMDiff
    have hcomp :
        ContMDiffOn I 𝓘(ℝ, (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) → ℝ) ∞
          (fun b : M => evalAtBasisCLETensorRSModel (E := E) r s (f b)) U :=
      hCLE.comp_contMDiffOn hf
    have hpi := (contMDiffOn_pi_space).1 hcomp
    exact hpi (Idx, Jdx)
  · intro h
    have hpi : ContMDiffOn I
        𝓘(ℝ, (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) → ℝ) ∞
        (fun b : M => evalAtBasisCLETensorRSModel (E := E) r s (f b)) U := by
      rw [contMDiffOn_pi_space]
      intro p
      exact h p.1 p.2
    have hsymm_smooth :
        ContMDiff 𝓘(ℝ, (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) → ℝ)
          𝓘(ℝ, ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ →L[ℝ]
                ContinuousMultilinearMap ℝ (fun _ : Fin s => E) ℝ) ∞
          (fun g : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)) → ℝ =>
            (evalAtBasisCLETensorRSModel (E := E) r s).symm g) :=
      ((evalAtBasisCLETensorRSModel (E := E) r s).symm.toContinuousLinearMap).contMDiff
    have hcomp := hsymm_smooth.comp_contMDiffOn hpi
    refine hcomp.congr ?_
    intro b _
    exact ((evalAtBasisCLETensorRSModel (E := E) r s).symm_apply_apply (f b)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.contMDiffOn_into_tensorRSModel_of_eval_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.contMDiffOn_into_tensorRSModel_of_eval_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.contMDiffOn_into_tensorRSModel_of_eval_basis ``Submission.DifferentialGeometry.Tensor.Coordinates.contMDiffOn_into_tensorRSModel_of_eval_basis

end Coordinates
end Tensor
end DifferentialGeometry

end
