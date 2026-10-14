import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Inclusion
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTensor.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.SmoothRepresentative.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

noncomputable def oneMinusConnLapSmooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    SmoothCcTensor g r s :=
  T - rawTensorConnLapSmooth (I := I) g r s T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] lemma oneMinusConnLapSmooth_toSection_apply
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s)
    (x : M) :
    (oneMinusConnLapSmooth (I := I) g r s T).toSection x =
      T.toSection x -
        rawTensorConnLap (I := I) g r s (fun z : M => T.toSection z) x := by
  unfold oneMinusConnLapSmooth
  rw [SmoothCcTensor.toSection_sub, ContMDiffSection.coe_sub, Pi.sub_apply,
    rawTensorConnLapSmooth_toSection_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_toSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_toSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_toSection_apply ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_toSection_apply

noncomputable def oneMinusConnLapSmoothIter
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ℕ → SmoothCcTensor g r s → SmoothCcTensor g r s
  | 0,     T => T
  | k + 1, T => oneMinusConnLapSmooth (I := I) g r s
                  (oneMinusConnLapSmoothIter g r s k T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem oneMinusConnLapSmoothIter_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (T : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s 0 T = T := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_zero ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_zero

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
@[simp] theorem oneMinusConnLapSmoothIter_succ
    (g : SmoothRiemannianMetric I M) (r s k : ℕ) (T : SmoothCcTensor g r s) :
    oneMinusConnLapSmoothIter (I := I) g r s (k + 1) T =
      oneMinusConnLapSmooth (I := I) g r s
        (oneMinusConnLapSmoothIter (I := I) g r s k T) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_succ ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmoothIter_succ

theorem oneMinusConnLapSmooth_toL2_inner_eq_h1_two
    (g : SmoothRiemannianMetric I M) (T v : SmoothCcTensor g 0 2) :
    ⟪((oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
          TensorL2 0 2 g),
        (v : TensorL2 0 2 g)⟫_ℝ =
      ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨T⟩,
        smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨v⟩⟫_ℝ := by
  have h_rhs :
      ⟪smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨T⟩,
          smoothToTensorH1Compl (I := I) (M := M) g 0 2 ⟨v⟩⟫_ℝ =
        ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ +
          ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [smoothToTensorH1Compl_apply, smoothToTensorH1Compl_apply,
      UniformSpace.Completion.inner_coe, SmoothCcTensorH1.inner_def,
      tensorH1Inner_def]
    rw [show tensorL2Inner (I := I) (M := M) g 0 2
            (⟨T⟩ : SmoothCcTensorH1 g 0 2).toCcTensor.toFun
            (⟨v⟩ : SmoothCcTensorH1 g 0 2).toCcTensor.toFun =
          ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ by
        rw [UniformSpace.Completion.inner_coe]
        exact (SmoothCcTensor.inner_def _ _).symm]
  rw [h_rhs]
  have h_dir :
      ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2 T v x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
          (covGrad (I := I) (M := M) g 0 2 T).toFun
          (covGrad (I := I) (M := M) g 0 2 v).toFun :=
    (tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
      (I := I) (M := M) g 0 2 T v).symm
  have h_green :
      tensorL2Inner (I := I) (M := M) g 0 (2 + 1)
          (covGrad (I := I) (M := M) g 0 2 T).toFun
          (covGrad (I := I) (M := M) g 0 2 v).toFun =
        - tensorL2Inner (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun :=
    tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_two
      (I := I) (M := M) g T v
  have h_lhs :
      ⟪((oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
            TensorL2 0 2 g),
          (v : TensorL2 0 2 g)⟫_ℝ =
        tensorL2Inner (I := I) (M := M) g 0 2
            (oneMinusConnLapSmooth (I := I) g 0 2 T).toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact SmoothCcTensor.inner_def _ _
  have h_l2_Tv :
      ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ =
        tensorL2Inner (I := I) (M := M) g 0 2 T.toFun v.toFun := by
    rw [UniformSpace.Completion.inner_coe]
    exact SmoothCcTensor.inner_def _ _
  have h_split :
      tensorL2Inner (I := I) (M := M) g 0 2
          (oneMinusConnLapSmooth (I := I) g 0 2 T).toFun v.toFun =
        tensorL2Inner (I := I) (M := M) g 0 2 T.toFun v.toFun -
          tensorL2Inner (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun := by
    have h_coe :
        ⟪((oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
              TensorL2 0 2 g),
            (v : TensorL2 0 2 g)⟫_ℝ =
          ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ -
            ⟪((rawTensorConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
                TensorL2 0 2 g),
              (v : TensorL2 0 2 g)⟫_ℝ := by
      rw [show (oneMinusConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) =
            T - rawTensorConnLapSmooth (I := I) g 0 2 T from rfl,
        UniformSpace.Completion.coe_sub, inner_sub_left]
    rw [← h_lhs, h_coe]
    rw [show ⟪(T : TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ =
          tensorL2Inner (I := I) (M := M) g 0 2 T.toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact SmoothCcTensor.inner_def _ _]
    rw [show ⟪((rawTensorConnLapSmooth (I := I) g 0 2 T : SmoothCcTensor g 0 2) :
            TensorL2 0 2 g), (v : TensorL2 0 2 g)⟫_ℝ =
          tensorL2Inner (I := I) (M := M) g 0 2
            (rawTensorConnLapSmooth (I := I) g 0 2 T).toFun v.toFun by
        rw [UniformSpace.Completion.inner_coe]; exact SmoothCcTensor.inner_def _ _]
  rw [h_lhs, h_split, h_l2_Tv, h_dir, h_green]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_toL2_inner_eq_h1_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_toL2_inner_eq_h1_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_toL2_inner_eq_h1_two ``Submission.DifferentialGeometry.Analysis.Spectral.oneMinusConnLapSmooth_toL2_inner_eq_h1_two

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem tensorParseval_l2Coeff_ofCompact_sq
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (h_compact : IsCompactOperator (tensorResolventL2
      (I := I) (M := M) g r s))
    (u : TensorL2 r s g) :
    ∑' i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s,
        (tensorL2Coeff (I := I) (M := M) h_compact u i) ^ 2 =
      ‖u‖ ^ 2 := by
  rw [tensorParseval_norm_sq (I := I) (M := M) h_compact u]
  refine tsum_congr (fun i => ?_)
  rw [tensorL2Coeff_eq_inner (I := I) (M := M) h_compact u i,
    Real.norm_eq_abs, sq_abs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorParseval_l2Coeff_ofCompact_sq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorParseval_l2Coeff_ofCompact_sq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorParseval_l2Coeff_ofCompact_sq ``Submission.DifferentialGeometry.Analysis.Spectral.tensorParseval_l2Coeff_ofCompact_sq

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem summable_tensorSobolevWeight_of_even
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s → ℝ)
    {a : ℝ} {k : ℕ} (hak : a ≤ (2 * k : ℕ))
    (h2k : Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M)
      g r s =>
      tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) * (c i) ^ 2)) :
    Summable (fun i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r
      s =>
      tensorSobolevWeight (I := I) (M := M) i a * (c i) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) h2k
  · have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i a :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i a
    positivity
  · have hmono :
        tensorSobolevWeight (I := I) (M := M) i a ≤
          tensorSobolevWeight (I := I) (M := M) i (2 * k : ℕ) :=
      tensorSobolevWeight_mono (I := I) (M := M) i hak
    exact mul_le_mul_of_nonneg_right hmono (sq_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.summable_tensorSobolevWeight_of_even then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.summable_tensorSobolevWeight_of_even"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.summable_tensorSobolevWeight_of_even ``Submission.DifferentialGeometry.Analysis.Spectral.summable_tensorSobolevWeight_of_even

end Spectral
end Analysis
end DifferentialGeometry

end
