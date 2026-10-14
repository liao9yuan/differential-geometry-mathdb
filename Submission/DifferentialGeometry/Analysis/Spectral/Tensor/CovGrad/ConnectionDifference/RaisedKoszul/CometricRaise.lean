import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.CovariantOrderFibreNormBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricDoubleTrace
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.RicciDeTurck.Linearization
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.SlotInsertion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.Matrix _root_.Submission.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck

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

def cometricRaiseSlot0FieldFun (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g₀ 0 (s + 2)) (x : M) : Tensor0SBundle.TensorRSSpace 1 (s + 1) I x :=
  cometricRaiseSlot0Fib g₀ s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from S.toSection x)
      (unitTensor (I := I) (M := M) x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0FieldFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0FieldFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0FieldFun ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0FieldFun

noncomputable def cometricRaiseSlot0FieldSection (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g₀ 0 (s + 2)) :=
  letI : NormedAddCommGroup (TensorRSModel 1 (s + 1) ℝ E) :=
    Tensor0SBundle.tensorRSModelNormedAddCommGroup 1 (s + 1)
  letI : NormedSpace ℝ (TensorRSModel 1 (s + 1) ℝ E) :=
    Tensor0SBundle.tensorRSModelNormedSpace 1 (s + 1)
  letI : TopologicalSpace (_root_.Bundle.TotalSpace (TensorRSModel 1 (s + 1) ℝ E)
      (fun y : M => TensorRSSpace 1 (s + 1) I y)) :=
    Tensor0SBundle.tensorRSBundleTopology 1 (s + 1)
  letI : FiberBundle (TensorRSModel 1 (s + 1) ℝ E)
      (fun y : M => TensorRSSpace 1 (s + 1) I y) :=
    Tensor0SBundle.tensorRSBundleFiber 1 (s + 1)
  letI : VectorBundle ℝ (TensorRSModel 1 (s + 1) ℝ E)
      (fun y : M => TensorRSSpace 1 (s + 1) I y) :=
    Tensor0SBundle.tensorRSBundle_vector 1 (s + 1)
  letI : ContMDiffVectorBundle (∞ : WithTop ℕ∞) (TensorRSModel 1 (s + 1) ℝ E)
      (fun y : M => TensorRSSpace 1 (s + 1) I y) I :=
    Tensor0SBundle.tensorRSBundle_smooth ∞ 1 (s + 1)
  (⟨cometricRaiseSlot0FieldFun (I := I) (M := M) g₀ s S,
      cometricRaiseSlot0Fib_section_contMDiff (I := I) g₀ s
        (fun x : M =>
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from S.toSection x)
            (unitTensor (I := I) (M := M) x))
        (contMDiff_unitEvalSection (I := I) (M := M) g₀ (s + 2) S)⟩ :
    ContMDiffSection I (TensorRSModel 1 (s + 1) ℝ E) ∞ (fun y : M => TensorRSSpace 1 (s + 1) I y))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0FieldSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0FieldSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0FieldSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0FieldSection

def cometricRaiseSlot0Field (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g₀ 0 (s + 2)) : SmoothCcTensor g₀ 1 (s + 1) where
  toSection := cometricRaiseSlot0FieldSection (I := I) (M := M) g₀ s S
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] lemma cometricRaiseSlot0Field_toSection (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : SmoothCcTensor g₀ 0 (s + 2)) (x : M) :
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ s S).toSection x =
      cometricRaiseSlot0Fib g₀ s x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from S.toSection x)
          (unitTensor (I := I) (M := M) x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field_toSection ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Field_toSection

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma cometricRaiseSlot0Fib_clm_apply (g₀ : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (D : Tensor0SSpace (s + 2) I x) (om : Tensor0SSpace 1 I x) :
    (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
        cometricRaiseSlot0Fib g₀ s x D) om =
      Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) (s + 1) x
        (inverseMetricSharpFib (I := I) g₀ x om) D := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Fib_clm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Fib_clm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Fib_clm_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.cometricRaiseSlot0Fib_clm_apply

noncomputable def koszulCovecCc (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 3 :=
  (1 / 2 : ℝ) •
    (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 3) 2)
          (ccTensor02SymmCovGrad3 (I := I) g₀ T)
        + domDomCongrSection (I := I) g₀ (finRotate 3) (ccTensor02SymmCovGrad3 (I := I) g₀ T)
        - domDomCongrSection (I := I) g₀ (Equiv.swap (1 : Fin 3) 2)
          (ccTensor02SymmCovGrad3 (I := I) g₀ T))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma koszulCovecCc_unitModel (g₀ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
    (x : M) (a b c : TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ T) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x c,
          tangentSpaceModelContinuousLinearEquiv (I := I) x a,
          tangentSpaceModelContinuousLinearEquiv (I := I) x b] =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3 (ccTensor02SymmCovGrad3 (I := I) g₀ T) x
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x b,
              tangentSpaceModelContinuousLinearEquiv (I := I) x a,
              tangentSpaceModelContinuousLinearEquiv (I := I) x c]
          + unitModel (I := I) (M := M) g₀ 3 (ccTensor02SymmCovGrad3 (I := I) g₀ T) x
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x a,
              tangentSpaceModelContinuousLinearEquiv (I := I) x b,
              tangentSpaceModelContinuousLinearEquiv (I := I) x c]
          - unitModel (I := I) (M := M) g₀ 3 (ccTensor02SymmCovGrad3 (I := I) g₀ T) x
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x c,
              tangentSpaceModelContinuousLinearEquiv (I := I) x b,
              tangentSpaceModelContinuousLinearEquiv (I := I) x a]) := by
  classical
  set W : SmoothCcTensor g₀ 0 3 := ccTensor02SymmCovGrad3 (I := I) g₀ T with hW
  have hperm : ∀ (σ : Equiv.Perm (Fin 3)) (m : Fin 3 → E),
      unitModel (I := I) (M := M) g₀ 3 (domDomCongrSection (I := I) g₀ σ W) x m =
        unitModel (I := I) (M := M) g₀ 3 W x (fun i => m (σ i)) := by
    intro σ m
    rw [domDomCongrSection_unitModel (I := I) g₀ σ W x,
      ContinuousMultilinearMap.domDomCongr_apply]
  have hlin : unitModel (I := I) (M := M) g₀ 3 (koszulCovecCc (I := I) g₀ T) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x c,
          tangentSpaceModelContinuousLinearEquiv (I := I) x a,
          tangentSpaceModelContinuousLinearEquiv (I := I) x b] =
      (1 / 2 : ℝ) *
        (unitModel (I := I) (M := M) g₀ 3 (domDomCongrSection (I := I) g₀
              (Equiv.swap (0 : Fin 3) 2) W) x
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x c,
              tangentSpaceModelContinuousLinearEquiv (I := I) x a,
              tangentSpaceModelContinuousLinearEquiv (I := I) x b]
          + unitModel (I := I) (M := M) g₀ 3 (domDomCongrSection (I := I) g₀ (finRotate 3) W) x
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x c,
              tangentSpaceModelContinuousLinearEquiv (I := I) x a,
              tangentSpaceModelContinuousLinearEquiv (I := I) x b]
          - unitModel (I := I) (M := M) g₀ 3 (domDomCongrSection (I := I) g₀
              (Equiv.swap (1 : Fin 3) 2) W) x
            ![tangentSpaceModelContinuousLinearEquiv (I := I) x c,
              tangentSpaceModelContinuousLinearEquiv (I := I) x a,
              tangentSpaceModelContinuousLinearEquiv (I := I) x b]) := by
    simp only [koszulCovecCc, unitModel, SmoothCcTensor.toSection_smul,
      SmoothCcTensor.toSection_add,
      SmoothCcTensor.toSection_sub, ContMDiffSection.coe_smul, ContMDiffSection.coe_add,
      ContMDiffSection.coe_sub, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
]
    rfl
  rw [hlin, hperm, hperm, hperm]
  have e1 : (fun i => (![tangentSpaceModelContinuousLinearEquiv (I := I) x c,
      tangentSpaceModelContinuousLinearEquiv (I := I) x a,
      tangentSpaceModelContinuousLinearEquiv (I := I) x b] : Fin 3 → E)
      ((Equiv.swap (0 : Fin 3) 2) i)) =
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x b,
        tangentSpaceModelContinuousLinearEquiv (I := I) x a,
        tangentSpaceModelContinuousLinearEquiv (I := I) x c] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  have e2 : (fun i => (![tangentSpaceModelContinuousLinearEquiv (I := I) x c,
      tangentSpaceModelContinuousLinearEquiv (I := I) x a,
      tangentSpaceModelContinuousLinearEquiv (I := I) x b] : Fin 3 → E)
      ((finRotate 3) i)) =
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x a,
        tangentSpaceModelContinuousLinearEquiv (I := I) x b,
        tangentSpaceModelContinuousLinearEquiv (I := I) x c] := by
    funext i; fin_cases i <;> simp [finRotate_apply]
  have e3 : (fun i => (![tangentSpaceModelContinuousLinearEquiv (I := I) x c,
      tangentSpaceModelContinuousLinearEquiv (I := I) x a,
      tangentSpaceModelContinuousLinearEquiv (I := I) x b] : Fin 3 → E)
      ((Equiv.swap (1 : Fin 3) 2) i)) =
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x c,
        tangentSpaceModelContinuousLinearEquiv (I := I) x b,
        tangentSpaceModelContinuousLinearEquiv (I := I) x a] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_def]
  rw [e1, e2, e3]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc_unitModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc_unitModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc_unitModel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.koszulCovecCc_unitModel

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
