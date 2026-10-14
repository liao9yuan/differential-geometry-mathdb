import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.CurvatureOperator.CovariantDerivativeGrid

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance tensorRSRiemannianNormedAddCommGroup
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Curvature.tensorRSRiemannianNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Curvature.tensorRSRiemannianNormedAddCommGroup target :: scope.openDecls } }

noncomputable def curvOpField (g : SmoothRiemannianMetric I M) (s : ℕ) :
    SmoothCcTensor g (s + 0) (s + 0) :=
  (Classical.choose (exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g)) s

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvOpField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvOpField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvOpField ``Submission.DifferentialGeometry.Geometry.Curvature.curvOpField

theorem curvOpField_apply_eq_pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
  (Classical.choose_spec (exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g)
    s S).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.curvOpField_apply_eq_pureRGenuineDiffOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.curvOpField_apply_eq_pureRGenuineDiffOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.curvOpField_apply_eq_pureRGenuineDiffOp ``Submission.DifferentialGeometry.Geometry.Curvature.curvOpField_apply_eq_pureRGenuineDiffOp

theorem operatorFieldApplication_curvOpField_eq_pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
  curvOpField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g s S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_curvOpField_eq_pureRGenuineDiffOp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_curvOpField_eq_pureRGenuineDiffOp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_curvOpField_eq_pureRGenuineDiffOp ``Submission.DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_curvOpField_eq_pureRGenuineDiffOp

noncomputable def genuineDiffCurvSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    SmoothCcTensor g 0 (s + 1) :=
  operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineDiffCurvSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineDiffCurvSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineDiffCurvSection ``Submission.DifferentialGeometry.Geometry.Curvature.genuineDiffCurvSection

@[simp] lemma genuineDiffCurvSection_toSection
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M) :
    (genuineDiffCurvSection (I := I) (M := M) g s S).toSection x =
      (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
        (covGrad (I := I) (M := M) g (s + 0) (s + 0)
          (curvOpField (I := I) (M := M) g s)).toSection x).comp
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from S.toSection x) := by
  rw [genuineDiffCurvSection,
    operatorFieldApplication_toSection (I := I) (M := M) g (s + 0) (s + 0 + 1)
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineDiffCurvSection_toSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineDiffCurvSection_toSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineDiffCurvSection_toSection ``Submission.DifferentialGeometry.Geometry.Curvature.genuineDiffCurvSection_toSection

theorem genuineDiffCurvSection_eq_covGrad_sub_slotExtend
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    genuineDiffCurvSection (I := I) (M := M) g s S =
      covGrad (I := I) (M := M) g 0 (s + 0)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) -
        operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
          (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
            (curvOpField (I := I) (M := M) g s))
          (covGrad (I := I) (M := M) g 0 (s + 0) S) := by
  classical
  have hbase : operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    (Classical.choose_spec (exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M)
      g) s S).symm
  have hB := covGrad_operatorFieldApply_eq (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  have hgds : operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S =
      genuineDiffCurvSection (I := I) (M := M) g s S := rfl
  rw [hgds] at hB
  have hB' := eq_sub_of_add_eq (hB.symm)
  rw [hB', hbase]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.genuineDiffCurvSection_eq_covGrad_sub_slotExtend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.genuineDiffCurvSection_eq_covGrad_sub_slotExtend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.genuineDiffCurvSection_eq_covGrad_sub_slotExtend ``Submission.DifferentialGeometry.Geometry.Curvature.genuineDiffCurvSection_eq_covGrad_sub_slotExtend

theorem operatorFieldApplication_slotExtend_curvOpField_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
          (curvOpField (I := I) (M := M) g s).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
        vs := by
  classical
  rw [operatorFieldApplication_toSection (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
      (slotExtend (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))
      (covGrad (I := I) (M := M) g 0 (s + 0) S) x,
    ContinuousLinearMap.comp_apply,
    slotExtend_toSection (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s) x]
  rw [slotExtendFib_apply_eval (I := I) (M := M) (s + 0) (s + 0) x
    (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
      (curvOpField (I := I) (M := M) g s).toSection x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 (s + 0) S).toSection x) d) v0 vs]
  rw [tensor0S_curry_covGrad_operatorFieldApplication_eq (I := I) (M := M) g (s + 0) S x d v0]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_slotExtend_curvOpField_covGrad_unit_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_slotExtend_curvOpField_covGrad_unit_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_slotExtend_curvOpField_covGrad_unit_eval ``Submission.DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_slotExtend_curvOpField_covGrad_unit_eval

theorem covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
          tensorCovDerivAt (I := I) (M := M) g 0 (s + 0)
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x v0) d)
        vs =
      Tensor0SSpace.toModel
          ((genuineDiffCurvSection (I := I) (M := M) g s S).toSection x d)
          (Fin.cons v0 vs) +
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            (curvOpField (I := I) (M := M) g s).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs := by
  classical
  have hbase : operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S =
      pureRGenuineDiffOp (I := I) (M := M) g 0 s S :=
    (Classical.choose_spec (exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M)
      g) s S).symm
  have hB := covGrad_operatorFieldApply_eq (I := I) (M := M) g (s + 0) (s + 0)
    (curvOpField (I := I) (M := M) g s) S
  rw [hbase] at hB
  have hsec := congrArg (fun T : SmoothCcTensor g 0 (s + 0 + 1) => T.toSection x) hB
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply] at hsec
  have happ :
      (covGrad (I := I) (M := M) g 0 (s + 0)
          (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toSection x d =
        (genuineDiffCurvSection (I := I) (M := M) g s S).toSection x d +
          (operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d := by
    rw [hsec, add_apply]
    rfl
  have hlhs :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0)
              (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x v0) d)
          vs =
        Tensor0SSpace.toModel
          ((covGrad (I := I) (M := M) g 0 (s + 0)
            (pureRGenuineDiffOp (I := I) (M := M) g 0 s S)).toSection x d)
          (Fin.cons v0 vs) := by
    have h := covGrad_toSection_apply_eval (I := I) (M := M) g 0 (s + 0)
      (pureRGenuineDiffOp (I := I) (M := M) g 0 s S) x d (Fin.cons v0 vs)
    refine Eq.symm (h.trans ?_)
    have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (s + 0 + 1) → E) = vs := by
      funext j; simp [Matrix.vecTail, Fin.cons_succ]
    have hhead : (Fin.cons v0 vs : Fin (s + 0 + 1) → E) 0 = v0 := by simp [Fin.cons_zero]
    rw [htail, hhead]
  have hterm2 :
      Tensor0SSpace.toModel
          ((operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d)
          (Fin.cons v0 vs) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            (curvOpField (I := I) (M := M) g s).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs :=
    operatorFieldApplication_slotExtend_curvOpField_covGrad_unit_eval (I := I) (M := M) g s S x d v0 vs
  rw [hlhs, happ, Tensor0SSpace.toModel_add, add_apply, hterm2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator ``Submission.DifferentialGeometry.Geometry.Curvature.covGrad_pureRGenuineDiffOp_unit_eval_eq_genuineDiffCurv_add_spectator

theorem operatorFieldApplication_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) :
    operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0 + 1)
          (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s))) S =
      covGrad (I := I) (M := M) g 0 (s + 0 + 1)
          (genuineDiffCurvSection (I := I) (M := M) g s S) -
        operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
          (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
          (covGrad (I := I) (M := M) g 0 (s + 0) S) := by
  classical
  have hB := covGrad_operatorFieldApply_eq (I := I) (M := M) g (s + 0) (s + 0 + 1)
    (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S
  have hgds : operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) S =
      genuineDiffCurvSection (I := I) (M := M) g s S := rfl
  rw [hgds] at hB
  exact (eq_sub_of_add_eq hB.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend ``Submission.DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend

theorem operatorFieldApplication_slotExtend_covGrad_curvOpField_covGrad_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0 + 1) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
          (covGrad (I := I) (M := M) g (s + 0) (s + 0)
            (curvOpField (I := I) (M := M) g s)).toSection x)
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
        vs := by
  classical
  rw [operatorFieldApplication_toSection (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
      (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
        (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
      (covGrad (I := I) (M := M) g 0 (s + 0) S) x,
    ContinuousLinearMap.comp_apply,
    slotExtend_toSection (I := I) (M := M) g (s + 0) (s + 0 + 1)
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)) x]
  rw [slotExtendFib_apply_eval (I := I) (M := M) (s + 0) (s + 0 + 1) x
    (show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)).toSection x)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
      (covGrad (I := I) (M := M) g 0 (s + 0) S).toSection x) d) v0 vs]
  rw [tensor0S_curry_covGrad_operatorFieldApplication_eq (I := I) (M := M) g (s + 0) S x d v0]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_slotExtend_covGrad_curvOpField_covGrad_unit_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_slotExtend_covGrad_curvOpField_covGrad_unit_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_slotExtend_covGrad_curvOpField_covGrad_unit_eval ``Submission.DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_slotExtend_covGrad_curvOpField_covGrad_unit_eval

theorem operatorFieldApplication_covGrad_covGrad_curvOpField_unit_eval
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (d : Tensor0SSpace 0 I x) (v0 : E) (vs : Fin (s + 0 + 1) → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0)
                (curvOpField (I := I) (M := M) g s))) S).toSection x) d)
        (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0 + 1)
              (genuineDiffCurvSection (I := I) (M := M) g s S) x v0) d)
          vs -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace (s + 0) I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
            (covGrad (I := I) (M := M) g (s + 0) (s + 0)
              (curvOpField (I := I) (M := M) g s)).toSection x)
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0) I x from
              tensorCovDerivAt (I := I) (M := M) g 0 (s + 0) S x v0) d))
          vs := by
  classical
  have hsec := operatorFieldApplication_covGrad_covGrad_curvOpField_eq_covGrad_genuineDiffCurv_sub_slotExtend
    (I := I) (M := M) g s S
  have happ :
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
          (operatorFieldApply (I := I) (M := M) g (s + 0) (s + 0 + 1 + 1)
            (covGrad (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0)
                (curvOpField (I := I) (M := M) g s))) S).toSection x) d =
        (covGrad (I := I) (M := M) g 0 (s + 0 + 1)
            (genuineDiffCurvSection (I := I) (M := M) g s S)).toSection x d -
          (operatorFieldApply (I := I) (M := M) g (s + 0 + 1) (s + 0 + 1 + 1)
            (slotExtend (I := I) (M := M) g (s + 0) (s + 0 + 1)
              (covGrad (I := I) (M := M) g (s + 0) (s + 0) (curvOpField (I := I) (M := M) g s)))
            (covGrad (I := I) (M := M) g 0 (s + 0) S)).toSection x d := by
    rw [hsec]
    rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
      sub_apply]
  rw [happ, Tensor0SSpace.toModel_sub, sub_apply]
  have hT1 :
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1 + 1) I x from
            (covGrad (I := I) (M := M) g 0 (s + 0 + 1)
              (genuineDiffCurvSection (I := I) (M := M) g s S)).toSection x) d)
          (Fin.cons v0 vs) =
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 0 + 1) I x from
            tensorCovDerivAt (I := I) (M := M) g 0 (s + 0 + 1)
              (genuineDiffCurvSection (I := I) (M := M) g s S) x v0) d)
          vs := by
    rw [covGrad_toSection_apply_eval (I := I) (M := M) g 0 (s + 0 + 1)
      (genuineDiffCurvSection (I := I) (M := M) g s S) x d (Fin.cons v0 vs)]
    have hhead : (Fin.cons v0 vs : Fin (s + 0 + 1 + 1) → E) 0 = v0 := by
      simp [Fin.cons_zero]
    have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (s + 0 + 1 + 1) → E) =
        (vs : Fin (s + 0 + 1) → E) := by
      funext j; simp [Matrix.vecTail, Fin.cons_succ]
    rw [hhead, htail]
  have hT2 := operatorFieldApplication_slotExtend_covGrad_curvOpField_covGrad_unit_eval
    (I := I) (M := M) g s S x d v0 vs
  rw [hT1, hT2]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_covGrad_covGrad_curvOpField_unit_eval then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_covGrad_covGrad_curvOpField_unit_eval"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_covGrad_covGrad_curvOpField_unit_eval ``Submission.DifferentialGeometry.Geometry.Curvature.operatorFieldApplication_covGrad_covGrad_curvOpField_unit_eval

end Curvature
end Geometry
end DifferentialGeometry

end
