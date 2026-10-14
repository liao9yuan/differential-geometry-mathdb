import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Calculus.TensorRS
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.HomTensor.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.HomTensorRSFiberNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Connection.Realization
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] in
private theorem homTensorTangentSpaceFiniteDimensional {x : M} :
    FiniteDimensional ℝ (TangentSpace I x) :=
  Tensor0SBundle.tangentSpace_finiteDimensional x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.homTensorTangentSpaceFiniteDimensional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.homTensorTangentSpaceFiniteDimensional target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem homTensorRSSpaceFiniteDimensional {r t : ℕ} {x : M} :
    FiniteDimensional ℝ (TensorRSSpace r t I x) :=
  Tensor0SBundle.tensorRSSpace_finiteDimensional r t x

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSSpaceFiniteDimensional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.homTensorRSSpaceFiniteDimensional target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem homTensorRSSpaceT2 {r t : ℕ} {x : M} :
    T2Space (TensorRSSpace r t I x) := by
  unfold TensorRSSpace
  exact ContinuousLinearMap.instT2Space

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSSpaceT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.homTensorRSSpaceT2 target :: scope.openDecls } }

def homTensorRSApplyFib (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : SmoothCcTensor g r a) (x : M) :
    TensorRSSpace r c I x :=
  Ψ x (W.toSection x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSApplyFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSApplyFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSApplyFib ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSApplyFib

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem homTensorRSApplyFib_contMDiff (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r c I z) x
        (homTensorRSApplyFib (I := I) (M := M) g r a c Ψ W x)) :=
  ContMDiff.clm_bundle_apply (b := id) hΨ W.toSection.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSApplyFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSApplyFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSApplyFib_contMDiff ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSApplyFib_contMDiff

def homTensorRSApply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) : SmoothCcTensor g r c where
  toSection :=
    { toFun := fun x : M => homTensorRSApplyFib (I := I) (M := M) g r a c Ψ W x
      contMDiff_toFun := homTensorRSApplyFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSApply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSApply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSApply ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSApply

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma homTensorRSApply_toSection (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) (x : M) :
    (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection x = Ψ x (W.toSection x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSApply_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSApply_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSApply_toSection ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSApply_toSection

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
theorem homTensorRSApply_add_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W₁ W₂ : SmoothCcTensor g r a) :
    homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ (W₁ + W₂) =
      homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₁ + homTensorRSApply (I := I) (M := M) g r a
        c Ψ hΨ W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₁ +
        homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₂).toSection x) =
      (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₁).toSection x +
        (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W₂).toSection x from rfl]
  rw [homTensorRSApply_toSection, homTensorRSApply_toSection, homTensorRSApply_toSection]
  rw [show ((W₁ + W₂).toSection x : TensorRSSpace r a I x) = W₁.toSection x + W₂.toSection x from by
    rw [SmoothCcTensor.toSection_add]; rfl]
  rw [map_add (Ψ x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSApply_add_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSApply_add_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSApply_add_right ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSApply_add_right

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    [SigmaCompactSpace M] in
theorem homTensorRSApply_smul_right (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (k : ℝ) (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ (k • W) =
      k • homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((k • homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection x) =
      k • (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection x from rfl]
  rw [homTensorRSApply_toSection, homTensorRSApply_toSection]
  rw [show ((k • W).toSection x : TensorRSSpace r a I x) = k • W.toSection x from by
    rw [SmoothCcTensor.toSection_smul]; rfl]
  rw [map_smul (Ψ x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSApply_smul_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSApply_smul_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSApply_smul_right ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSApply_smul_right

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem homTensorRSApplyFib_add_left (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ₁ Ψ₂ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : SmoothCcTensor g r a) (x : M) :
    homTensorRSApplyFib (I := I) (M := M) g r a c (fun y => Ψ₁ y + Ψ₂ y) W x =
      homTensorRSApplyFib (I := I) (M := M) g r a c Ψ₁ W x +
        homTensorRSApplyFib (I := I) (M := M) g r a c Ψ₂ W x := by
  rw [homTensorRSApplyFib, homTensorRSApplyFib, homTensorRSApplyFib, add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSApplyFib_add_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSApplyFib_add_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSApplyFib_add_left ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSApplyFib_add_left

noncomputable def slotInsertHomTensorRSFib (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) :
    TensorRSSpace r (a + 1) I x →L[ℝ] TensorRSSpace r (c + 1) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (a + 1) I x) :=
    homTensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r (a + 1) I x) :=
    homTensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun D =>
        covGradBundleEquiv (I := I) (M := M) r c x
          (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D))
      map_add' := fun D₁ D₂ => by
        rw [map_add (covGradBundleEquiv (I := I) (M := M) r a x).symm,
          ContinuousLinearMap.comp_add, map_add (covGradBundleEquiv (I := I) (M := M) r c x)]
      map_smul' := fun k D => by
        rw [map_smul (covGradBundleEquiv (I := I) (M := M) r a x).symm,
          ContinuousLinearMap.comp_smul, map_smul (covGradBundleEquiv (I := I) (M := M) r c x)]
        rfl }

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib ``Submission.DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma slotInsertHomTensorRSFib_apply (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (D : TensorRSSpace r (a + 1) I x) :
    slotInsertHomTensorRSFib (I := I) (M := M) r a c x A D =
      covGradBundleEquiv (I := I) (M := M) r c x
        (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D)) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply ``Submission.DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma slotInsertHomTensorRSFib_apply_eval (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (D : TensorRSSpace r (a + 1) I x)
    (Dlow : Tensor0SSpace r I x) (v0 : TangentSpace I x) (vs : Fin c → TangentSpace I x) :
    Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          slotInsertHomTensorRSFib (I := I) (M := M) r a c x A D) Dlow) (Fin.cons v0 vs) =
      Tensor0SSpace.eval
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          A ((covGradBundleEquiv (I := I) (M := M) r a x).symm D v0)) Dlow) vs := by
  rw [slotInsertHomTensorRSFib_apply (I := I) (M := M) r a c x A D]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r c x
    (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D)) Dlow (Fin.cons v0 vs)]
  have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) = vs := by
    funext j; simp [Matrix.vecTail, Fin.cons_succ]
  have hhead : (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) 0 = v0 := by simp [Fin.cons_zero]
  rw [htail, hhead, ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply_eval ``Submission.DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply_eval

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
lemma slotInsertHomTensorRSFib_apply_toModel (r a c : ℕ) (x : M)
    (A : TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (D : TensorRSSpace r (a + 1) I x)
    (Dlow : Tensor0SSpace r I x) (v0 : E) (vs : Fin c → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          slotInsertHomTensorRSFib (I := I) (M := M) r a c x A D) Dlow) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          A ((covGradBundleEquiv (I := I) (M := M) r a x).symm D
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v0))) Dlow) vs := by
  rw [slotInsertHomTensorRSFib_apply (I := I) (M := M) r a c x A D]
  rw [covGradBundleEquiv_apply_toModel (I := I) (M := M) r c x
    (A.comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm D)) Dlow (Fin.cons v0 vs)]
  have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (c + 1) → E) = vs := by
    funext j
    simp [Matrix.vecTail, Fin.cons_succ]
  have hhead : (Fin.cons v0 vs : Fin (c + 1) → E) 0 = v0 := by
    simp [Fin.cons_zero]
  rw [htail, hhead, ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply_toModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply_toModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply_toModel ``Submission.DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply_toModel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem slotInsertHomTensorRSFib_apply_apply_contMDiff (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : NormedAddCommGroup (TensorRSModel r (a + 1) ℝ E) :=
      tensorRSModelNormedAddCommGroup r (a + 1)
    letI : NormedSpace ℝ (TensorRSModel r (a + 1) ℝ E) :=
      tensorRSModelNormedSpace r (a + 1)
    letI := tensorRSBundleTopology (I := I) (M := M) r (a + 1)
    letI := tensorRSBundleFiber (I := I) (M := M) r (a + 1)
    letI := tensorRSBundle_vector (I := I) (M := M) r (a + 1)
    letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (a + 1)
    ∀ (D : Cₛ^∞⟮I; TensorRSModel r (a + 1) ℝ E,
        (fun z : M => TensorRSSpace r (a + 1) I z)⟯)
      (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r c I z) x
        ((Ψ x) ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x) (Y x)))) := by
  let : NormedAddCommGroup (TensorRSModel r (a + 1) ℝ E) :=
    tensorRSModelNormedAddCommGroup r (a + 1)
  let : NormedSpace ℝ (TensorRSModel r (a + 1) ℝ E) :=
    tensorRSModelNormedSpace r (a + 1)
  let := tensorRSBundleTopology (I := I) (M := M) r (a + 1)
  let := tensorRSBundleFiber (I := I) (M := M) r (a + 1)
  let := tensorRSBundle_vector (I := I) (M := M) r (a + 1)
  let := tensorRSBundle_smooth (I := I) (M := M) ∞ r (a + 1)
  intro D Y
  have hH :=
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r a).comp D.contMDiff
  have hstep1 := ContMDiff.clm_bundle_apply (b := id) hH Y.contMDiff
  have hstep2 := ContMDiff.clm_bundle_apply (b := id) hΨ hstep1
  refine hstep2.congr ?_
  intro x
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply_apply_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply_apply_contMDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
private theorem slotInsertHomTensorRSFib_apply_contMDiff (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    letI : NormedAddCommGroup (TensorRSModel r (a + 1) ℝ E) :=
      tensorRSModelNormedAddCommGroup r (a + 1)
    letI : NormedSpace ℝ (TensorRSModel r (a + 1) ℝ E) :=
      tensorRSModelNormedSpace r (a + 1)
    letI := tensorRSBundleTopology (I := I) (M := M) r (a + 1)
    letI := tensorRSBundleFiber (I := I) (M := M) r (a + 1)
    letI := tensorRSBundle_vector (I := I) (M := M) r (a + 1)
    letI := tensorRSBundle_smooth (I := I) (M := M) ∞ r (a + 1)
    ∀ (D : Cₛ^∞⟮I; TensorRSModel r (a + 1) ℝ E,
      (fun z : M => TensorRSSpace r (a + 1) I z)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r c I z) x
        ((Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x)))) := by
  let : NormedAddCommGroup (TensorRSModel r (a + 1) ℝ E) :=
    tensorRSModelNormedAddCommGroup r (a + 1)
  let : NormedSpace ℝ (TensorRSModel r (a + 1) ℝ E) :=
    tensorRSModelNormedSpace r (a + 1)
  let := tensorRSBundleTopology (I := I) (M := M) r (a + 1)
  let := tensorRSBundleFiber (I := I) (M := M) r (a + 1)
  let := tensorRSBundle_vector (I := I) (M := M) r (a + 1)
  let := tensorRSBundle_smooth (I := I) (M := M) ∞ r (a + 1)
  intro D
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r c I z)
    (φ := fun x => (Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x)))
  intro Y
  exact slotInsertHomTensorRSFib_apply_apply_contMDiff (I := I) (M := M) r a c Ψ hΨ D Y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply_contMDiff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_apply_contMDiff target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
theorem covGradBundleEquiv_section_contMDiff (r c : ℕ)
    (G : Π x : M, TangentSpace I x →L[ℝ] TensorRSSpace r c I x)
    (hG : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r c I z) x (G x))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (c + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (c + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (c + 1) I z) x
        (covGradBundleEquiv (I := I) (M := M) r c x (G x))) := by
  let : NormedAddCommGroup (TensorRSModel r (c + 1) ℝ E) :=
    tensorRSModelNormedAddCommGroup r (c + 1)
  let : NormedSpace ℝ (TensorRSModel r (c + 1) ℝ E) :=
    tensorRSModelNormedSpace r (c + 1)
  let := tensorRSBundleTopology (I := I) (M := M) r (c + 1)
  let := tensorRSBundleFiber (I := I) (M := M) r (c + 1)
  let := tensorRSBundle_vector (I := I) (M := M) r (c + 1)
  let := tensorRSBundle_smooth (I := I) (M := M) ∞ r (c + 1)
  have hcomp :=
    (covGradBundleSmoothEquiv (I := I) (M := M) r c).toDiffeomorph.contMDiff.comp hG
  refine hcomp.congr ?_
  intro x
  rw [Function.comp_apply,
    covGradBundleSmoothEquiv_toDiffeomorph_apply (I := I) (M := M) r c x (G x)]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covGradBundleEquiv_section_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covGradBundleEquiv_section_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covGradBundleEquiv_section_contMDiff ``Submission.DifferentialGeometry.Geometry.Connection.covGradBundleEquiv_section_contMDiff

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem slotInsertHomTensorRSFib_contMDiff (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (a + 1) ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (a + 1) ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r (a + 1) I z →L[ℝ] TensorRSSpace r (c + 1) I z) x
        (slotInsertHomTensorRSFib (I := I) (M := M) r a c x (Ψ x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r (a + 1) I z)
    (V₂ := fun z : M => TensorRSSpace r (c + 1) I z)
    (φ := fun x => slotInsertHomTensorRSFib (I := I) (M := M) r a c x (Ψ x))
  intro D
  have hG := slotInsertHomTensorRSFib_apply_contMDiff (I := I) (M := M) r a c Ψ hΨ D
  have hcov := covGradBundleEquiv_section_contMDiff (I := I) (M := M) r c
    (fun x => (Ψ x).comp ((covGradBundleEquiv (I := I) (M := M) r a x).symm (D x))) hG
  refine hcov.congr ?_
  intro x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_contMDiff ``Submission.DifferentialGeometry.Geometry.Connection.slotInsertHomTensorRSFib_contMDiff

end Connection
end Geometry
end DifferentialGeometry

end
