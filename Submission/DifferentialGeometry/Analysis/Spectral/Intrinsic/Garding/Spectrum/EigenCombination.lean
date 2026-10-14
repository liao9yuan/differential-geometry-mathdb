import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Pairing.FaithfulH1Embedding
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactResolvent
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.InteriorRegularity.TensorAllOrdersRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

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

variable (g : SmoothRiemannianMetric I M)

abbrev eigenSmooth
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
      SmoothCcTensor g 0 2 :=
  eigenvectorSmooth (I := I) (M := M) g 0 2 i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.eigenSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.eigenSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.eigenSmooth ``Submission.DifferentialGeometry.Analysis.Spectral.eigenSmooth

def finiteEigenCombo
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
      SmoothCcTensor g 0 2 :=
  ∑ i ∈ F, c i • eigenSmooth (I := I) (M := M) g i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenCombo"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenCombo

omit [BoundarylessManifold I M] in
lemma finiteEigenCombo_eq
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    finiteEigenCombo (I := I) (M := M) g F c =
      ∑ i ∈ F, c i • eigenSmooth (I := I) (M := M) g i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_eq ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_eq

omit [BoundarylessManifold I M] in
theorem finiteEigenCombo_contMDiff
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun x : M =>
        TotalSpace.mk' (TensorRSModel 0 2 ℝ E) x
          ((finiteEigenCombo (I := I) (M := M) g F c).toSection x)) :=
  (finiteEigenCombo (I := I) (M := M) g F c).toSection.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_contMDiff ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_contMDiff

omit [BoundarylessManifold I M] in
lemma hCompact : IsCompactOperator (tensorResolventL2 (I := I) (M := M) g 0 2) :=
  tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.hCompact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.hCompact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.hCompact ``Submission.DifferentialGeometry.Analysis.Spectral.hCompact

omit [BoundarylessManifold I M] in
theorem finiteEigenCombo_toL2
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    (finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g) =
      ∑ i ∈ F, c i •
        tensorResolventEigenbasisVec (I := I) (M := M)
          (hCompact (I := I) (M := M) g) i := by
  rw [← SmoothCcTensor.toL2_apply, finiteEigenCombo_eq, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, SmoothCcTensor.toL2_apply,
    eigenvectorSmooth_toL2 (I := I) (M := M) g 0 2 i]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_toL2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_toL2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_toL2 ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_toL2

open scoped _root_.Classical in
omit [BoundarylessManifold I M] in
theorem tensorL2Coeff_ofCompact_eigenSmooth
    (i j : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        ((eigenSmooth (I := I) (M := M) g j : TensorL2 0 2 g)) i =
      (if i = j then (1 : ℝ) else 0) := by
  classical
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (hCompact (I := I) (M := M) g) with hb_def
  have hbj : (eigenSmooth (I := I) (M := M) g j : TensorL2 0 2 g) = b j := by
    rw [hb_def, tensorResolventHilbertEigenbasisSigma_apply
      (I := I) (M := M) (hCompact (I := I) (M := M) g) j,
      eigenvectorSmooth_toL2 (I := I) (M := M) g 0 2 j]
  rw [tensorL2Coeff_eq_inner, hbj]
  have horth := b.orthonormal
  rw [orthonormal_iff_ite] at horth
  exact horth i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_eigenSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_eigenSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_eigenSmooth ``Submission.DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_ofCompact_eigenSmooth

open scoped _root_.Classical in
omit [BoundarylessManifold I M] in
theorem finiteEigenCombo_tensorL2Coeff
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        ((finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g)) i =
      (if i ∈ F then c i else 0) := by
  classical
  rw [tensorL2Coeff_eq_inner, finiteEigenCombo_toL2,
    inner_sum]
  have h_term : ∀ j ∈ F,
      (_root_.Inner.inner ℝ
          (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (hCompact (I := I) (M := M) g) i)
          (c j • tensorResolventEigenbasisVec (I := I) (M := M)
            (hCompact (I := I) (M := M) g) j) : ℝ) =
        (if i = j then c j else 0) := by
    intro j _
    rw [inner_smul_right]
    rw [show tensorResolventEigenbasisVec (I := I) (M := M)
            (hCompact (I := I) (M := M) g) j =
          tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
            (hCompact (I := I) (M := M) g) j from
        (tensorResolventHilbertEigenbasisSigma_apply
          (I := I) (M := M) (hCompact (I := I) (M := M) g) j).symm]
    have horth := (tensorResolventHilbertEigenbasisSigma
        (I := I) (M := M) (hCompact (I := I) (M := M) g)).orthonormal
    rw [orthonormal_iff_ite] at horth
    rw [horth i j]
    by_cases h : i = j <;> simp [h]
  rw [Finset.sum_congr rfl h_term]
  by_cases hiF : i ∈ F
  · rw [Finset.sum_eq_single i]
    · simp [hiF]
    · intro j _ hji
      rw [if_neg (fun h => hji h.symm)]
    · intro h; exact absurd hiF h
  · rw [if_neg hiF, Finset.sum_eq_zero]
    intro j hj
    rw [if_neg (fun h => hiF (by rw [h]; exact hj))]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_tensorL2Coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_tensorL2Coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_tensorL2Coeff ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_tensorL2Coeff

theorem finiteEigenCombo_weakSolution
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (v : SmoothCcTensor g 0 2) :
    ∫ x, tensorCovDerivPointwiseInner (I := I) (M := M) g 0 2
        (finiteEigenCombo (I := I) (M := M) g F c) v x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      tensorL2Inner (I := I) (M := M) g 0 2
        (- rawTensorConnLapSmooth (I := I) g 0 2
            (finiteEigenCombo (I := I) (M := M) g F c)).toFun v.toFun := by
  set u : SmoothCcTensor g 0 2 := finiteEigenCombo (I := I) (M := M) g F c with hu
  rw [(tensorL2Inner_covGrad_eq_integral_tensorCovDerivPointwiseInner
        (I := I) (M := M) g 0 2 u v).symm]
  rw [tensorL2Inner_covGrad_eq_neg_tensorL2Inner_rawConnLap_two
    (I := I) (M := M) g u v]
  rw [show (- rawTensorConnLapSmooth (I := I) g 0 2 u).toFun =
        (-1 : ℝ) • (rawTensorConnLapSmooth (I := I) g 0 2 u).toFun by
      funext x
      rw [Pi.smul_apply, SmoothCcTensor.toFun_apply, SmoothCcTensor.toFun_apply,
        SmoothCcTensor.toSection_neg, ContMDiffSection.coe_neg, Pi.neg_apply,
        TensorRSSpace.toModel_neg, neg_one_smul]]
  rw [tensorL2Inner_smul_left]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_weakSolution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_weakSolution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_weakSolution ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_weakSolution

theorem rawConnLapSmooth_tensorL2Coeff
    (T : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (rawTensorConnLapSmooth (I := I) g 0 2 T)) i =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) *
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 T) i := by
  have h_split :
      rawTensorConnLapSmooth (I := I) g 0 2 T =
        T - oneMinusConnLapSmooth (I := I) g 0 2 T := by
    rw [show oneMinusConnLapSmooth (I := I) g 0 2 T =
          T - rawTensorConnLapSmooth (I := I) g 0 2 T from rfl]
    abel
  rw [h_split, map_sub, tensorL2Coeff_eq_inner, inner_sub_right,
    ← tensorL2Coeff_eq_inner, ← tensorL2Coeff_eq_inner,
    tensorL2Coeff_ofCompact_oneMinusConnLapSmooth
      (I := I) (M := M) g (hCompact (I := I) (M := M) g) T i]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.rawConnLapSmooth_tensorL2Coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.rawConnLapSmooth_tensorL2Coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.rawConnLapSmooth_tensorL2Coeff ``Submission.DifferentialGeometry.Analysis.Spectral.rawConnLapSmooth_tensorL2Coeff

theorem rawConnLapIter_tensorL2Coeff
    (T : SmoothCcTensor g 0 2)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) (j : ℕ) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g 0 2 j T)) i =
      (- TensorEigenIdx.lambda (I := I) (M := M) i) ^ j *
        tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
          (SmoothCcTensor.toL2 T) i := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [rawTensorConnLapIter_succ,
        rawConnLapSmooth_tensorL2Coeff (I := I) (M := M) g
          (rawTensorConnLapIter (I := I) g 0 2 j T) i, ih, pow_succ]
      ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.rawConnLapIter_tensorL2Coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.rawConnLapIter_tensorL2Coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.rawConnLapIter_tensorL2Coeff ``Submission.DifferentialGeometry.Analysis.Spectral.rawConnLapIter_tensorL2Coeff

open scoped _root_.Classical in
private lemma finiteEigenCombo_iterRawConnLap_tensorL2Coeff
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (j : ℕ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2
          (rawTensorConnLapIter (I := I) g 0 2 j
            (finiteEigenCombo (I := I) (M := M) g F c))) i =
      (if i ∈ F then (- TensorEigenIdx.lambda (I := I) (M := M) i) ^ j * c i
        else 0) := by
  rw [rawConnLapIter_tensorL2Coeff (I := I) (M := M) g
    (finiteEigenCombo (I := I) (M := M) g F c) i j,
    show SmoothCcTensor.toL2 (finiteEigenCombo (I := I) (M := M) g F c) =
        (finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g) from
      SmoothCcTensor.toL2_apply _,
    finiteEigenCombo_tensorL2Coeff (I := I) (M := M) g F c i]
  by_cases h : i ∈ F <;> simp [h]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_iterRawConnLap_tensorL2Coeff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_iterRawConnLap_tensorL2Coeff target :: scope.openDecls } }

theorem finiteEigenCombo_iterRawConnLap_l2NormSq
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (j : ℕ) :
    ‖SmoothCcTensor.toL2
        (rawTensorConnLapIter (I := I) g 0 2 j
          (finiteEigenCombo (I := I) (M := M) g F c))‖ ^ 2 =
      ∑ i ∈ F,
        (TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * j) * (c i) ^ 2 := by
  classical
  rw [← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M)
    (hCompact (I := I) (M := M) g)]
  rw [tsum_eq_sum (s := F) (f := fun i =>
      (tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        (SmoothCcTensor.toL2
          (rawTensorConnLapIter (I := I) g 0 2 j
            (finiteEigenCombo (I := I) (M := M) g F c))) i) ^ 2) ?_]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [finiteEigenCombo_iterRawConnLap_tensorL2Coeff (I := I) (M := M) g F c j i,
      if_pos hi, mul_pow, ← pow_mul, mul_comm j 2]
    rw [(even_two_mul j).neg_pow (TensorEigenIdx.lambda (I := I) (M := M) i)]
  · intro b hb
    simp only [finiteEigenCombo_iterRawConnLap_tensorL2Coeff
      (I := I) (M := M) g F c j b]
    rw [if_neg hb]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_iterRawConnLap_l2NormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_iterRawConnLap_l2NormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_iterRawConnLap_l2NormSq ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_iterRawConnLap_l2NormSq

theorem finiteEigenCombo_l2NormSq
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) :
    ‖(finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g)‖ ^ 2 =
      ∑ i ∈ F, (c i) ^ 2 := by
  have h := finiteEigenCombo_iterRawConnLap_l2NormSq (I := I) (M := M) g F c 0
  rw [rawTensorConnLapIter_zero, SmoothCcTensor.toL2_apply] at h
  rw [h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_l2NormSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_l2NormSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_l2NormSq ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_l2NormSq

open scoped _root_.Classical in
def finiteEigenComboHs
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (σ : ℝ) :
    TensorHs (I := I) (M := M) g 0 2 σ where
  coeff i := if i ∈ F then c i else 0
  weighted_summable := by
    classical
    refine summable_of_ne_finset_zero (s := F) ?_
    intro i hiF
    rw [if_neg hiF]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs

open scoped _root_.Classical in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma finiteEigenComboHs_coeff
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (σ : ℝ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    (finiteEigenComboHs (I := I) (M := M) g F c σ).coeff i =
      (if i ∈ F then c i else 0) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_coeff ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_coeff

omit [BoundarylessManifold I M] in
lemma finiteEigenComboHs_coeff_eq
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (σ : ℝ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    (finiteEigenComboHs (I := I) (M := M) g F c σ).coeff i =
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) (M := M) g)
        ((finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g)) i := by
  rw [finiteEigenCombo_tensorL2Coeff (I := I) (M := M) g F c i]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_coeff_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_coeff_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_coeff_eq ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_coeff_eq

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem finiteEigenCombo_spectral_normSq
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (σ : ℝ) :
    ‖finiteEigenComboHs (I := I) (M := M) g F c σ‖ ^ 2 =
      ∑ i ∈ F,
        (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ σ * (c i) ^ 2 := by
  classical
  rw [TensorHs.norm_sq_eq_tsum (I := I) (M := M)]
  rw [tsum_eq_sum (s := F) (f := fun i =>
      tensorSobolevWeight (I := I) (M := M) i σ *
        ((finiteEigenComboHs (I := I) (M := M) g F c σ).coeff i) ^ 2) ?_]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [finiteEigenComboHs_coeff, if_pos hi]
    unfold tensorSobolevWeight
    rfl
  · intro b hb
    simp only [finiteEigenComboHs_coeff]
    rw [if_neg hb]
    ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_spectral_normSq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_spectral_normSq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_spectral_normSq ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenCombo_spectral_normSq

end Spectral
end Analysis
end DifferentialGeometry

end
