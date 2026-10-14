import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.Covariant
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.UnitModel
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Basis

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor.Multilinear
open _root_.Submission.DifferentialGeometry.Analysis.Spectral (operatorFieldApply operatorFieldApplication_toSection)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

noncomputable def reindexCoefficientInputSlotsFiber (r s : ℕ) (σ' : Equiv.Perm (Fin r)) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x) :
    Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x :=
  A.comp
    ((tensor0SSpaceContinuousLinearEquiv (I := I) r
      x).symm.toContinuousLinearMap.comp
      (((ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℝ
            σ').toContinuousLinearEquiv.toContinuousLinearMap).comp
        (tensor0SSpaceContinuousLinearEquiv (I := I) r x).toContinuousLinearMap))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlotsFiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlotsFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlotsFiber ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlotsFiber

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem reindexCoefficientInputSlotsFiber_apply (r s : ℕ) (σ' : Equiv.Perm (Fin r)) (x : M)
    (A : Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x)
    (D : Tensor0SSpace r I x) :
    reindexCoefficientInputSlotsFiber (I := I) r s σ' x A D =
      A (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SSpace.toModel D))) := by
  rw [reindexCoefficientInputSlotsFiber, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlotsFiber_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlotsFiber_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlotsFiber_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlotsFiber_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem reindexCoefficientInputSlotsFiber_contMDiff (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) x
        (reindexCoefficientInputSlotsFiber (I := I) r s σ' x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SSpace r I x)
    (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
    (φ := fun x => reindexCoefficientInputSlotsFiber (I := I) r s σ' x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x))
  intro Y
  have hYσ : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel r ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel r ℝ E)
        (E := fun z : M => Tensor0SSpace r I z) x
        (Tensor0SSpace.ofModel
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SSpace.toModel (Y x))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ'
            (Tensor0SSpace.toModel (Y x))) : Tensor0SSpace r I x))).mpr ?_
    have hYcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => Y x)).mp Y.contMDiff
    intro τ x₀
    refine (hYcoord (τ ∘ σ') x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ'
        (Tensor0SSpace.toModel (Y x)))
        (fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((Bundle.Trivialization.symmL ℝ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀) x)
            ((Module.finBasis ℝ E) (τ j)))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  have hRY := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff hYσ
  refine hRY.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SSpace s I z) x t)
    (reindexCoefficientInputSlotsFiber_apply (I := I) r s σ' x
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlotsFiber_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlotsFiber_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlotsFiber_contMDiff ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlotsFiber_contMDiff

noncomputable def reindexCoefficientInputSlots (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) :
    SmoothCcTensor g₀ r s where
  toSection :=
    { toFun := fun x : M =>
        (show TensorRSSpace r s I x from
          reindexCoefficientInputSlotsFiber (I := I) r s σ' x
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x))
      contMDiff_toFun := reindexCoefficientInputSlotsFiber_contMDiff (I := I) (M := M) g₀ r s R σ' }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlots ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlots

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
@[simp] theorem reindexCoefficientInputSlots_toSection (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r)) (x : M) :
    (reindexCoefficientInputSlots (I := I) (M := M) g₀ r s R σ').toSection x =
      (show TensorRSSpace r s I x from
        reindexCoefficientInputSlotsFiber (I := I) r s σ' x
          (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlots_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlots_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlots_toSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.reindexCoefficientInputSlots_toSection

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem unitModel_operatorFieldApply_reindexCoefficientInputSlots
    (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (R : SmoothCcTensor g₀ r s) (σ' : Equiv.Perm (Fin r))
    (W W' : SmoothCcTensor g₀ 0 r)
    (hWW' : ∀ x : M, unitModel (I := I) (M := M) g₀ r W' x =
      ContinuousMultilinearMap.domDomCongr σ' (unitModel (I := I) (M := M) g₀ r W x))
    (x : M) :
    unitModel (I := I) (M := M) g₀ s
        (operatorFieldApply (I := I) (M := M) g₀ r s
          (reindexCoefficientInputSlots (I := I) (M := M) g₀ r s R σ') W) x =
      unitModel (I := I) (M := M) g₀ s
        (operatorFieldApply (I := I) (M := M) g₀ r s R W') x := by
  rw [unitModel, unitModel, operatorFieldApplication_toSection,
    operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, reindexCoefficientInputSlots_toSection]
  rw [reindexCoefficientInputSlotsFiber_apply (I := I) r s σ' x
    (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
      W.toSection x) (unitTensor (I := I) (M := M) x))]
  have hWu : Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
        W.toSection x) (unitTensor (I := I) (M := M) x)) =
      unitModel (I := I) (M := M) g₀ r W x := rfl
  have hW'u :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
        W'.toSection x) (unitTensor (I := I) (M := M) x) =
      Tensor0SSpace.ofModel (unitModel (I := I) (M := M) g₀ r W' x) := by
    rw [show unitModel (I := I) (M := M) g₀ r W' x =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace r I x from
            W'.toSection x) (unitTensor (I := I) (M := M) x)) from rfl,
      Tensor0SSpace.ofModel_toModel]
  rw [hWu, ← hWW' x, hW'u]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_operatorFieldApply_reindexCoefficientInputSlots then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_operatorFieldApply_reindexCoefficientInputSlots"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_operatorFieldApply_reindexCoefficientInputSlots ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.unitModel_operatorFieldApply_reindexCoefficientInputSlots

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
