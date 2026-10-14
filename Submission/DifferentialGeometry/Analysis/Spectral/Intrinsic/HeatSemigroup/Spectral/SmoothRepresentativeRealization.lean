import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Spectral.Smoothing
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Duhamel.Smoothing
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.TensorHsInterpolationLimit
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Spectrum.GardingReduction
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.Garding.AllOrder
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.SmoothTensorAllOrderCompleteness

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev
    DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev

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


theorem eigenSpan_pouHs_le_spectral (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g 0 2))
        (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g 0 2 → ℝ),
        (tensorPouSobolevHsNorm (I := I) (M := M) g k
            (finiteEigenCombo (I := I) (M := M) g F c)).toReal ≤
          (C * (k + 1)) *
            ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖ := by
  obtain ⟨C, hC_nn, hC⟩ :=
    DifferentialGeometry.Analysis.Elliptic.exists_tensorPouSobolevHsNorm_k_le_sum_rawConnLapIter
      (I := I) (M := M) g 2 k
  refine ⟨C, hC_nn, fun F c => ?_⟩
  exact eigenSpan_pouHs_le_spectral_of_elliptic (I := I) (M := M) g F c k hC_nn
    (hC (finiteEigenCombo (I := I) (M := M) g F c))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.eigenSpan_pouHs_le_spectral then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.eigenSpan_pouHs_le_spectral"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.eigenSpan_pouHs_le_spectral ``Submission.DifferentialGeometry.Analysis.Spectral.eigenSpan_pouHs_le_spectral

omit [BoundarylessManifold I M] in
theorem finiteEigenComboHs_tensorHsToL2_eq
    (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ
        (finiteEigenComboHs (I := I) (M := M) g F c σ) =
      (finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g) := by
  classical
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) with hb_def
  apply b.repr.injective
  ext i
  have hlhs : (b.repr (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ
        (finiteEigenComboHs (I := I) (M := M) g F c σ))) i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ
          (finiteEigenComboHs (I := I) (M := M) g F c σ)) i := rfl
  have hrhs : (b.repr ((finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g))) i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
        ((finiteEigenCombo (I := I) (M := M) g F c : TensorL2 0 2 g)) i := rfl
  rw [hlhs, hrhs,
    tensorHsToL2_tensorL2Coeff (I := I) (M := M)
      (h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ]
  exact finiteEigenComboHs_coeff_eq (I := I) (M := M) g F c σ i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_tensorHsToL2_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_tensorHsToL2_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_tensorHsToL2_eq ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_tensorHsToL2_eq

def eigenIdxFinset (n : ℕ) :
    Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :=
  (tensorEigenIdx_one_add_lambda_lt_finite (I := I) (M := M) g 0 2 ((n : ℝ) + 1)).toFinset

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.eigenIdxFinset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.eigenIdxFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.eigenIdxFinset ``Submission.DifferentialGeometry.Analysis.Spectral.eigenIdxFinset

omit [BoundarylessManifold I M] in
lemma mem_eigenIdxFinset (n : ℕ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    i ∈ eigenIdxFinset (I := I) (M := M) g n ↔
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < (n : ℝ) + 1 := by
  unfold eigenIdxFinset
  rw [Set.Finite.mem_toFinset]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.mem_eigenIdxFinset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.mem_eigenIdxFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.mem_eigenIdxFinset ``Submission.DifferentialGeometry.Analysis.Spectral.mem_eigenIdxFinset

omit [BoundarylessManifold I M] in
lemma eigenIdxFinset_mono : Monotone (eigenIdxFinset (I := I) (M := M) g) := by
  intro m n hmn i hi
  rw [mem_eigenIdxFinset] at hi ⊢
  have : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.eigenIdxFinset_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.eigenIdxFinset_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.eigenIdxFinset_mono ``Submission.DifferentialGeometry.Analysis.Spectral.eigenIdxFinset_mono

omit [BoundarylessManifold I M] in
lemma exists_mem_eigenIdxFinset
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    ∃ n : ℕ, i ∈ eigenIdxFinset (I := I) (M := M) g n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 + TensorEigenIdx.lambda (I := I) (M := M) i)
  refine ⟨n, ?_⟩
  rw [mem_eigenIdxFinset]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_mem_eigenIdxFinset then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_mem_eigenIdxFinset"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_mem_eigenIdxFinset ``Submission.DifferentialGeometry.Analysis.Spectral.exists_mem_eigenIdxFinset

omit [BoundarylessManifold I M] in
lemma tendsto_eigenIdxFinset_atTop :
    Tendsto (eigenIdxFinset (I := I) (M := M) g) _root_.Filter.atTop atTop :=
  tendsto_atTop_finset_of_monotone (eigenIdxFinset_mono (I := I) (M := M) g)
    (exists_mem_eigenIdxFinset (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tendsto_eigenIdxFinset_atTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tendsto_eigenIdxFinset_atTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tendsto_eigenIdxFinset_atTop ``Submission.DifferentialGeometry.Analysis.Spectral.tendsto_eigenIdxFinset_atTop

def spectralPartialSum (u : TensorL2 0 2 g) (n : ℕ) : SmoothCcTensor g 0 2 :=
  finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g n)
    (fun i => tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.spectralPartialSum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.spectralPartialSum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.spectralPartialSum ``Submission.DifferentialGeometry.Analysis.Spectral.spectralPartialSum

omit [BoundarylessManifold I M] in
theorem spectralPartialSum_toL2_tendsto (u : TensorL2 0 2 g) :
    Tendsto (fun n => (spectralPartialSum (I := I) (M := M) g u n : TensorL2 0 2 g))
      atTop (𝓝 u) := by
  classical
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) with hb_def
  have hsum : HasSum (fun i => b.repr u i • b i) u := b.hasSum_repr u
  have hpartial : _root_.Filter.Tendsto
      (fun s : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0
        2) =>
        ∑ i ∈ s, b.repr u i • b i) _root_.Filter.atTop (𝓝 u) := hsum
  have hcomp := hpartial.comp (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g)
  refine hcomp.congr (fun n => ?_)
  simp only [Function.comp_apply]
  rw [spectralPartialSum, finiteEigenCombo_toL2 (I := I) (M := M) g]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← tensorResolventHilbertEigenbasisSigma_apply (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) i, ← hb_def]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.spectralPartialSum_toL2_tendsto then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.spectralPartialSum_toL2_tendsto"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.spectralPartialSum_toL2_tendsto ``Submission.DifferentialGeometry.Analysis.Spectral.spectralPartialSum_toL2_tendsto

private def weightedPartial (u : TensorL2 0 2 g) (k n : ℕ) : ℝ :=
  ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
    (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * k : ℕ) : ℝ) *
      (tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) ^ 2

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.weightedPartial
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.weightedPartial target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
private lemma weightedPartial_term_nonneg (u : TensorL2 0 2 g) (k : ℕ)
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :
    0 ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * k : ℕ) : ℝ) *
      (tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) ^ 2 := by
  have hbase : 0 ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    have := tensor_lambda_nonneg (I := I) (M := M) i
    linarith
  have hw : 0 ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * k : ℕ) : ℝ) :=
    Real.rpow_nonneg hbase _
  positivity

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.weightedPartial_term_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.weightedPartial_term_nonneg target :: scope.openDecls } }

open scoped _root_.Classical in
omit [BoundarylessManifold I M] in
private lemma toHs_spectralPartialSum_sub (u : TensorL2 0 2 g) (k : ℕ) {m n : ℕ}
    (hmn : n ≤ m) :
    SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
        (spectralPartialSum (I := I) (M := M) g u m) -
      SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
        (spectralPartialSum (I := I) (M := M) g u n) =
      SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
        (finiteEigenCombo (I := I) (M := M) g
          (eigenIdxFinset (I := I) (M := M) g m \ eigenIdxFinset (I := I) (M := M) g n)
          (fun i => tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i)) := by
  classical
  set c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i with hc
  have hsub : finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g m) c -
        finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g n) c =
      finiteEigenCombo (I := I) (M := M) g
        (eigenIdxFinset (I := I) (M := M) g m \ eigenIdxFinset (I := I) (M := M) g n) c := by
    rw [finiteEigenCombo_eq, finiteEigenCombo_eq, finiteEigenCombo_eq]
    rw [Finset.sum_sdiff_eq_sub (eigenIdxFinset_mono (I := I) (M := M) g hmn)]
  rw [show SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
        (spectralPartialSum (I := I) (M := M) g u m) -
      SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
        (spectralPartialSum (I := I) (M := M) g u n) =
      SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
        (finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g m) c -
          finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g n) c) from ?_]
  · rw [hsub]
  · rw [SmoothCcTensor.toHs, SmoothCcTensor.toHs, SmoothCcTensor.toHs]
    rw [show (⟨finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g m) c -
            finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g n) c⟩ :
          SmoothCcTensorHs g 0 2 k) =
        (⟨finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g m) c⟩ :
            SmoothCcTensorHs g 0 2 k) -
          (⟨finiteEigenCombo (I := I) (M := M) g (eigenIdxFinset (I := I) (M := M) g n) c⟩ :
            SmoothCcTensorHs g 0 2 k) from
      SmoothCcTensorHs.ext (by rw [SmoothCcTensorHs.toCcTensor_sub])]
    rw [UniformSpace.Completion.coe_sub]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.toHs_spectralPartialSum_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.toHs_spectralPartialSum_sub target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
private lemma weightedPartial_le_tsum (u : TensorL2 0 2 g) (k n : ℕ)
    (v : TensorHs (I := I) (M := M) g 0 2 ((2 * k : ℕ) : ℝ))
    (hv : ∀ i, v.coeff i = tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) :
    weightedPartial (I := I) (M := M) g u k n ≤ ‖v‖ ^ 2 := by
  classical
  rw [TensorHs.norm_sq_eq_tsum (I := I) (M := M) v]
  unfold weightedPartial
  have hterm : ∀ i,
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ ((2 * k : ℕ) : ℝ) *
        (tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) ^ 2 =
      tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) * (v.coeff i) ^ 2 := by
    intro i
    rw [hv i, tensorSobolevWeight]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  refine Summable.sum_le_tsum _ (fun i _ => ?_) v.weighted_summable
  have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i ((2 * k : ℕ) : ℝ) :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i ((2 * k : ℕ) : ℝ)
  positivity

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.weightedPartial_le_tsum
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.weightedPartial_le_tsum target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
private lemma weightedPartial_cauchySeq (u : TensorL2 0 2 g) (k : ℕ)
    (v : TensorHs (I := I) (M := M) g 0 2 ((2 * k : ℕ) : ℝ))
    (hv : ∀ i, v.coeff i = tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) :
    CauchySeq (fun n => weightedPartial (I := I) (M := M) g u k n) := by
  classical
  have hmono : Monotone (fun n => weightedPartial (I := I) (M := M) g u k n) := by
    intro m n hmn
    unfold weightedPartial
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (eigenIdxFinset_mono (I := I) (M := M) g hmn)
      (fun i _ _ => weightedPartial_term_nonneg (I := I) (M := M) g u k i)
  have hbdd : BddAbove (Set.range (fun n => weightedPartial (I := I) (M := M) g u k n)) := by
    refine ⟨‖v‖ ^ 2, ?_⟩
    rintro x ⟨n, rfl⟩
    exact weightedPartial_le_tsum (I := I) (M := M) g u k n v hv
  exact (tendsto_atTop_ciSup hmono hbdd).cauchySeq

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.weightedPartial_cauchySeq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.weightedPartial_cauchySeq target :: scope.openDecls } }

open scoped _root_.Classical in
omit [BoundarylessManifold I M] in
private lemma finiteEigenComboHs_sdiff_normSq (u : TensorL2 0 2 g) (k : ℕ) {m n : ℕ}
    (hmn : n ≤ m) :
    ‖finiteEigenComboHs (I := I) (M := M) g
        (eigenIdxFinset (I := I) (M := M) g m \ eigenIdxFinset (I := I) (M := M) g n)
        (fun i => tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i)
        ((2 * k : ℕ) : ℝ)‖ ^ 2 =
      weightedPartial (I := I) (M := M) g u k m -
        weightedPartial (I := I) (M := M) g u k n := by
  classical
  rw [finiteEigenCombo_spectral_normSq (I := I) (M := M) g]
  unfold weightedPartial
  rw [Finset.sum_sdiff_eq_sub (eigenIdxFinset_mono (I := I) (M := M) g hmn)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_sdiff_normSq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.finiteEigenComboHs_sdiff_normSq target :: scope.openDecls } }

open scoped _root_.Classical in
omit [BoundarylessManifold I M] in
private lemma dist_toHs_spectralPartialSum_le (u : TensorL2 0 2 g) (k : ℕ)
    {C : ℝ} (hC :
      ∀ (F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2))
        (c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ),
        (tensorPouSobolevHsNorm (I := I) (M := M) g k
            (finiteEigenCombo (I := I) (M := M) g F c)).toReal ≤
          (C * (k + 1)) *
            ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖)
    {m n : ℕ} (hmn : n ≤ m) :
    dist (SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
          (spectralPartialSum (I := I) (M := M) g u m))
        (SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
          (spectralPartialSum (I := I) (M := M) g u n)) ≤
      (C * (k + 1)) * Real.sqrt
        (weightedPartial (I := I) (M := M) g u k m -
          weightedPartial (I := I) (M := M) g u k n) := by
  classical
  rw [dist_eq_norm, toHs_spectralPartialSum_sub (I := I) (M := M) g u k hmn,
    tensorPouSobolevHilbert_norm_eq (I := I) (M := M) g k]
  set F : Finset (Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2) :=
    eigenIdxFinset (I := I) (M := M) g m \ eigenIdxFinset (I := I) (M := M) g n with hF
  set c : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i with hc
  refine le_trans (hC F c) ?_
  rw [show ‖finiteEigenComboHs (I := I) (M := M) g F c ((2 * k : ℕ) : ℝ)‖ =
        Real.sqrt (weightedPartial (I := I) (M := M) g u k m -
          weightedPartial (I := I) (M := M) g u k n) from ?_]
  rw [← finiteEigenComboHs_sdiff_normSq (I := I) (M := M) g u k hmn, hF, hc]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.dist_toHs_spectralPartialSum_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.dist_toHs_spectralPartialSum_le target :: scope.openDecls } }

theorem spectralPartialSum_toHs_cauchy (u : TensorL2 0 2 g)
    (hu : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : TensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ v = u)
    (k : ℕ) :
    CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
      (spectralPartialSum (I := I) (M := M) g u n)) := by
  classical
  obtain ⟨C, hC_nn, hC⟩ := eigenSpan_pouHs_le_spectral (I := I) (M := M) g k
  obtain ⟨v, hv_eq⟩ := hu ((2 * k : ℕ) : ℝ) (by positivity)
  have hv_coeff : ∀ i, v.coeff i = tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i := by
    intro i
    have := tensorHsToL2_tensorL2Coeff (I := I) (M := M)
      (h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
      (show (0 : ℝ) ≤ ((2 * k : ℕ) : ℝ) by positivity) v i
    rw [hv_eq] at this
    exact this.symm
  have hwcauchy := weightedPartial_cauchySeq (I := I) (M := M) g u k v hv_coeff
  set Ck : ℝ := C * (k + 1) with hCk
  have hCk_pos : 0 < Ck + 1 := by positivity
  rw [Metric.cauchySeq_iff'] at hwcauchy ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hwcauchy ((ε / (Ck + 1)) ^ 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hbound := dist_toHs_spectralPartialSum_le (I := I) (M := M) g u k hC hn
  have hwlt : weightedPartial (I := I) (M := M) g u k n -
      weightedPartial (I := I) (M := M) g u k N < (ε / (Ck + 1)) ^ 2 := by
    have := hN n hn
    rw [Real.dist_eq] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hwnn : 0 ≤ weightedPartial (I := I) (M := M) g u k n -
      weightedPartial (I := I) (M := M) g u k N := by
    have hmono : weightedPartial (I := I) (M := M) g u k N ≤
        weightedPartial (I := I) (M := M) g u k n := by
      unfold weightedPartial
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (eigenIdxFinset_mono (I := I) (M := M) g hn)
        (fun i _ _ => weightedPartial_term_nonneg (I := I) (M := M) g u k i)
    linarith
  calc _root_.Dist.dist (SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
            (spectralPartialSum (I := I) (M := M) g u n))
          (SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) k
            (spectralPartialSum (I := I) (M := M) g u N))
      ≤ Ck * Real.sqrt
          (weightedPartial (I := I) (M := M) g u k n -
            weightedPartial (I := I) (M := M) g u k N) := hbound
    _ < ε := by
        have hsqrt : Real.sqrt
            (weightedPartial (I := I) (M := M) g u k n -
              weightedPartial (I := I) (M := M) g u k N) < ε / (Ck + 1) := by
          rw [show ε / (Ck + 1) = Real.sqrt ((ε / (Ck + 1)) ^ 2) from
            (Real.sqrt_sq (by positivity)).symm]
          exact Real.sqrt_lt_sqrt hwnn hwlt
        have hCk_nn : 0 ≤ Ck := by positivity
        calc Ck * Real.sqrt
              (weightedPartial (I := I) (M := M) g u k n -
                weightedPartial (I := I) (M := M) g u k N)
            ≤ Ck * (ε / (Ck + 1)) := by
                apply mul_le_mul_of_nonneg_left (le_of_lt hsqrt) hCk_nn
          _ < ε := by
                rw [mul_div_assoc']
                rw [div_lt_iff₀ hCk_pos]
                nlinarith [hε, hCk_nn]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.spectralPartialSum_toHs_cauchy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.spectralPartialSum_toHs_cauchy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.spectralPartialSum_toHs_cauchy ``Submission.DifferentialGeometry.Analysis.Spectral.spectralPartialSum_toHs_cauchy

theorem spectralSmoothRealizesAsSmooth_holds :
    SpectralSmoothRealizesAsSmooth (I := I) (M := M) g 0 2 := by
  classical
  intro u hu
  have hcauchy : ∀ k : ℕ,
      CauchySeq (fun n => SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k)
        (spectralPartialSum (I := I) (M := M) g u n)) :=
    fun k => spectralPartialSum_toHs_cauchy (I := I) (M := M) g u hu (2 * k)
  obtain ⟨T, hT⟩ :=
    smoothCcTensor_limit_of_allOrders_toHs_cauchy (I := I) (M := M) g 0 2 u
      (fun n => spectralPartialSum (I := I) (M := M) g u n) hcauchy
      (spectralPartialSum_toL2_tendsto (I := I) (M := M) g u)
  exact ⟨T, hT⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.spectralSmoothRealizesAsSmooth_holds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.spectralSmoothRealizesAsSmooth_holds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.spectralSmoothRealizesAsSmooth_holds ``Submission.DifferentialGeometry.Analysis.Spectral.spectralSmoothRealizesAsSmooth_holds

theorem exists_smooth_covariant_two_tensor_representative_of_duhamel_smoothing
    {t : ℝ} (ht : 0 ≤ t)
    (φ : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ : ∀ i, Continuous (φ i))
    (hsmooth : ∀ c : ℝ, 0 ≤ c →
      Summable (fun i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i c *
          ∫ q in (0 : ℝ)..t, (φ i q) ^ 2)) :
    ∃ T : SmoothCcTensor g 0 2,
      ∀ i, tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
          (T : TensorL2 0 2 g) i =
        perModeConvolution (TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i)
          (φ i) t :=
  exists_smooth_tensor_representative_of_duhamel_smoothing
    (I := I) (M := M) ht
    (spectralSmoothRealizesAsSmooth_holds (I := I) (M := M) (g := g))
    φ hφ hsmooth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.exists_smooth_covariant_two_tensor_representative_of_duhamel_smoothing then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.exists_smooth_covariant_two_tensor_representative_of_duhamel_smoothing"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.exists_smooth_covariant_two_tensor_representative_of_duhamel_smoothing ``Submission.DifferentialGeometry.Analysis.Spectral.exists_smooth_covariant_two_tensor_representative_of_duhamel_smoothing

end Spectral
end Analysis
end DifferentialGeometry

end
