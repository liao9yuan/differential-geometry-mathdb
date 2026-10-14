import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannian
open _root_.Submission.DifferentialGeometry.TensorRSNabla

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

noncomputable def scalarSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M => (ζ : M → ℝ) x • w.toSection x
      contMDiff_toFun := by
        exact ContMDiff.smul_section ζ.contMDiff w.toSection.contMDiff }
  hasCompactSupport := by
    classical
    refine HasCompactSupport.of_support_subset_isCompact w.hasCompactSupport ?_
    intro x hx
    rw [Function.mem_support] at hx
    refine subset_tsupport w.toFun ?_
    rw [Function.mem_support]
    intro hw_zero
    apply hx
    change TensorRSSpace.toModel ((ζ : M → ℝ) x • w.toSection x) = 0
    rw [TensorRSSpace.toModel_smul,
      show TensorRSSpace.toModel (w.toSection x) = w.toFun x from rfl, hw_zero,
      smul_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M]
    [SigmaCompactSpace M] in
@[simp] lemma scalarSmul_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) (x : M) :
    (scalarSmul (I := I) (M := M) g r s ζ w).toSection x =
      (ζ : M → ℝ) x • w.toSection x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul_toSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul_toSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul_toSection_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul_toSection_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [SigmaCompactSpace M] in
lemma scalarSmul_toFun_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) (x : M) :
    (scalarSmul (I := I) (M := M) g r s ζ w).toFun x =
      (ζ : M → ℝ) x • w.toFun x := by
  rw [SmoothCcTensor.toFun_apply, scalarSmul_toSection_apply,
    TensorRSSpace.toModel_smul]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul_toFun_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul_toFun_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul_toFun_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.scalarSmul_toFun_apply

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem tensorCovDerivAt_scalarSmul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w : SmoothCcTensor g r s) (x : M) (v : E) :
    tensorCovDerivAt (I := I) (M := M) g r s
        (scalarSmul (I := I) (M := M) g r s ζ w) x v =
      (ζ : M → ℝ) x • tensorCovDerivAt (I := I) (M := M) g r s w x v +
        (mvfderiv (I := I) (ζ : M → ℝ) x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v)) •
          w.toSection x := by
  unfold tensorCovDerivAt
  have hpt : (fun y : M => (scalarSmul (I := I) (M := M) g r s ζ w).toSection y) =
      (fun y : M => (ζ : M → ℝ) y) • (fun y : M => w.toSection y) := by
    funext y
    rw [scalarSmul_toSection_apply]
    rfl
  rw [hpt]
  have hζ_mdiff : MDiffAt (fun y : M => (ζ : M → ℝ) y) x :=
    (ζ.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt
  have hw_mdiff :=
    (w.toSection.contMDiff.mdifferentiable (by norm_num)).mdifferentiableAt (x := x)
  have hcov_leibniz :=
    (tensorRSCovariantDerivative I M r s
        (LeviCivita (I := I) g)).isCovariantDerivativeOn.leibniz
      (σ := fun y : M => w.toSection y)
      (g := fun y : M => (ζ : M → ℝ) y)
      (hσ := hw_mdiff)
      (hg := hζ_mdiff)
      (hx := (by trivial : x ∈ (Set.univ : Set M)))
  change (tensorRSCovariantDerivative I M r s (LeviCivita (I := I) g)).toFun
      ((fun y : M => (ζ : M → ℝ) y) • fun y : M => w.toSection y) x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v) = _
  rw [hcov_leibniz]
  rw [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_scalarSmul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_scalarSmul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_scalarSmul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivAt_scalarSmul

noncomputable def tensorCovDerivCrossLeft
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
      (mvfderiv (I := I) (ζ : M → ℝ) x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) *
        tensorInnerPointwise (I := I) (M := M) g r s x
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s w x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))
          (S.toFun x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossLeft then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossLeft"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossLeft ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossLeft

noncomputable def tensorCovDerivCrossRight
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
      (mvfderiv (I := I) (ζ : M → ℝ) x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
            ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) *
        tensorInnerPointwise (I := I) (M := M) g r s x
          (w.toFun x)
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma tensorCovDerivCrossLeft_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          (mvfderiv (I := I) (ζ : M → ℝ) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))
              (S.toFun x)) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossLeft_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossLeft_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossLeft_def ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossLeft_def

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
lemma tensorCovDerivCrossRight_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          (mvfderiv (I := I) (ζ : M → ℝ) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (w.toFun x)
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)))) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_def ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivCrossRight_def

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private lemma tensorCovDerivPointwiseInner_scalarSmul_left_summand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
        tensorInnerPointwise (I := I) (M := M) g r s x
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s
              (scalarSmul (I := I) (M := M) g r s ζ w) x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s S x
              ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))) =
      (ζ : M → ℝ) x *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)))) +
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          (mvfderiv (I := I) (ζ : M → ℝ) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)) *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (w.toFun x)
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)))) := by
  rw [tensorCovDerivAt_scalarSmul (I := I) (M := M) g r s ζ w x
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)]
  simp only [TensorRSSpace.toModel_add, TensorRSSpace.toModel_smul]
  have hwx : TensorRSSpace.toModel (w.toSection x) = w.toFun x := rfl
  rw [hwx]
  rw [tensorInnerPointwise_add_left]
  simp only [tensorInnerPointwise_smul_left]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_scalarSmul_left_summand
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_scalarSmul_left_summand target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private lemma tensorCovDerivPointwiseInner_scalarSmul_right_summand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
        tensorInnerPointwise (I := I) (M := M) g r s x
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s w x ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))
          (TensorRSSpace.toModel
            (tensorCovDerivAt (I := I) (M := M) g r s
              (scalarSmul (I := I) (M := M) g r s ζ S) x
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))) =
      (ζ : M → ℝ) x *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)))) +
        (gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
          (mvfderiv (I := I) (ζ : M → ℝ) x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))
              (S.toFun x)) := by
  rw [tensorCovDerivAt_scalarSmul (I := I) (M := M) g r s ζ S x
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)]
  simp only [TensorRSSpace.toModel_add, TensorRSSpace.toModel_smul]
  have hSx : TensorRSSpace.toModel (S.toSection x) = S.toFun x := rfl
  rw [hSx]
  rw [tensorInnerPointwise_add_right]
  simp only [tensorInnerPointwise_smul_right]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_scalarSmul_right_summand
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_scalarSmul_right_summand target :: scope.openDecls } }

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma smul_const_tensorCovDerivPointwiseInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (ζ : M → ℝ) x *
          ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s x
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s w x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S x
                  ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)))) =
      (ζ : M → ℝ) x *
        tensorCovDerivPointwiseInner (I := I) (M := M) g r s w S x := by
  rw [tensorCovDerivPointwiseInner_def, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smul_const_tensorCovDerivPointwiseInner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.smul_const_tensorCovDerivPointwiseInner target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem tensorCovDerivPointwiseInner_scalarSmul_left
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (ζ : C^∞⟮I, M; ℝ⟯) (w S : SmoothCcTensor g r s) (x : M) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s
        (scalarSmul (I := I) (M := M) g r s ζ w) S x =
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s w
          (scalarSmul (I := I) (M := M) g r s ζ S) x -
        tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x +
        tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x := by
  classical
  have hLHS :
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s
          (scalarSmul (I := I) (M := M) g r s ζ w) S x =
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (ζ : M → ℝ) x *
              ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                tensorInnerPointwise (I := I) (M := M) g r s x
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s w x
                      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S x
                      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))))) +
          tensorCovDerivCrossRight (I := I) (M := M) g r s ζ w S x := by
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossRight_def,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact tensorCovDerivPointwiseInner_scalarSmul_left_summand
      (I := I) (M := M) g r s ζ w S x i j
  have hRHS :
      tensorCovDerivPointwiseInner (I := I) (M := M) g r s w
          (scalarSmul (I := I) (M := M) g r s ζ S) x =
        (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            (ζ : M → ℝ) x *
              ((gramMatrixAt (I := I) (M := M) g x)⁻¹ i j *
                tensorInnerPointwise (I := I) (M := M) g r s x
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s w x
                      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)))
                  (TensorRSSpace.toModel
                    (tensorCovDerivAt (I := I) (M := M) g r s S x
                      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))))) +
          tensorCovDerivCrossLeft (I := I) (M := M) g r s ζ w S x := by
    rw [tensorCovDerivPointwiseInner_def, tensorCovDerivCrossLeft_def,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact tensorCovDerivPointwiseInner_scalarSmul_right_summand
      (I := I) (M := M) g r s ζ w S x i j
  rw [hLHS, hRHS]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_scalarSmul_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_scalarSmul_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_scalarSmul_left ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorCovDerivPointwiseInner_scalarSmul_left

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
