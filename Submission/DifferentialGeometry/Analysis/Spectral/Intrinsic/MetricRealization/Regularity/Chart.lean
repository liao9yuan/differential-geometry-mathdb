import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Reconstruction.SupercriticalTensor
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Component.ArbitraryOrderSobolevBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Regularity.ArbitraryOrderChartSobolev
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevBanach
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.Bootstrap.BootstrapMixed
import Submission.DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Spectral.Plancherel

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral
namespace MetricRealization

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [NeZero (Module.finrank ℝ E)] in
theorem resolvent_eigenvalue_inv_eq_one_add_lambda
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    (i.fst.val)⁻¹ = 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  change (i.fst.val)⁻¹ = 1 + tensorLaplacianEigenvalueOf i.fst.val
  rw [tensorLaplacianEigenvalueOf]
  field_simp
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.resolvent_eigenvalue_inv_eq_one_add_lambda then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.resolvent_eigenvalue_inv_eq_one_add_lambda"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.resolvent_eigenvalue_inv_eq_one_add_lambda ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.resolvent_eigenvalue_inv_eq_one_add_lambda

private def eigenbasisVec (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    TensorL2 r s g :=
  tensorResolventEigenbasisVec (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenbasisVec
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenbasisVec target :: scope.openDecls } }


private lemma eigenbasisVec_norm_eq_one (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    ‖eigenbasisVec (I := I) (M := M) g r s i‖ = 1 :=
  (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)).norm_eq_one i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenbasisVec_norm_eq_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenbasisVec_norm_eq_one target :: scope.openDecls } }

private def eigenvectorComp (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y =>
    ((tensorL2ChartComponent (I := I) (M := M) g r s
        (eigenbasisVec (I := I) (M := M) g r s i) α P₀ :
      Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ) y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvectorComp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvectorComp target :: scope.openDecls } }

private lemma eigenvectorComp_eq_ofCompact (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorComp (I := I) (M := M) g r s i α P₀ =
      eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀ := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvectorComp_eq_ofCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvectorComp_eq_ofCompact target :: scope.openDecls } }

private lemma eigenvectorComp_eq_unconditional (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    eigenvectorComp (I := I) (M := M) g r s i α P₀ =
      eigenvectorChartComponentFun (I := I) (M := M) g r s i α P₀ := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvectorComp_eq_unconditional
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvectorComp_eq_unconditional target :: scope.openDecls } }

private lemma eigenvectorComp_memWkp (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)
    (k : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (eigenvectorComp (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  rw [eigenvectorComp_eq_ofCompact]
  exact eigenvector_chartComponent_memWkp_arbitrary
    (I := I) (M := M) g r s i (2 * k) α P₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvectorComp_memWkp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvectorComp_memWkp target :: scope.openDecls } }

private lemma eigenvectorComp_wkpNorm_le_weight (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (k : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s,
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
            (eigenvectorComp (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal
            (C * tensorSobolevWeight (I := I) (M := M) i ((2 * k + 1 : ℕ) : ℝ)) := by
  classical
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    eigenvector_chartComponent_wkpNorm_arbitrary
      (I := I) (M := M) g r s (2 * k) α P₀
  refine ⟨C, hC_nn, fun i => ?_⟩
  have h := hC_bd i
  rw [eigenvectorComp_eq_unconditional]
  have h_norm_one : ‖tensorResolventEigenbasisVec (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i‖ = 1 :=
    eigenbasisVec_norm_eq_one (I := I) (M := M) g r s i
  rw [h_norm_one, ENNReal.ofReal_one, mul_one] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [show (2 * k) + 1 = 2 * k + 1 from rfl]
  have h_inv : (i.fst.val)⁻¹ = 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    resolvent_eigenvalue_inv_eq_one_add_lambda (I := I) (M := M) g r s i
  rw [h_inv]
  have h_base_nn : (0 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  rw [tensorSobolevWeight, ← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i)
    (2 * k + 1)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvectorComp_wkpNorm_le_weight
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenvectorComp_wkpNorm_le_weight target :: scope.openDecls } }

open _root_.Classical in
private def eigenFinsetSeq (g : SmoothRiemannianMetric I M) (r s : ℕ)
    [Encodable (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)]
    (n : ℕ) : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :=
  (Finset.range n).biUnion
    (fun m => (Encodable.decode₂
      (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) m).toFinset)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenFinsetSeq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenFinsetSeq target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma eigenFinsetSeq_monotone (g : SmoothRiemannianMetric I M) (r s : ℕ)
    [Encodable (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)] :
    Monotone (eigenFinsetSeq (I := I) (M := M) g r s) := by
  classical
  intro a b hab
  exact Finset.biUnion_subset_biUnion_of_subset_left _
    (Finset.range_subset_range.mpr hab)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenFinsetSeq_monotone
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenFinsetSeq_monotone target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma eigenFinsetSeq_mem (g : SmoothRiemannianMetric I M) (r s : ℕ)
    [Encodable (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)]
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    ∃ n, i ∈ eigenFinsetSeq (I := I) (M := M) g r s n := by
  classical
  refine ⟨Encodable.encode i + 1, ?_⟩
  rw [eigenFinsetSeq, Finset.mem_biUnion]
  refine ⟨Encodable.encode i, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
  rw [Option.mem_toFinset]
  exact Encodable.decode₂_encode i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenFinsetSeq_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenFinsetSeq_mem target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] in
private lemma eigenFinsetSeq_tendsto (g : SmoothRiemannianMetric I M) (r s : ℕ)
    [Encodable (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)] :
    Filter.Tendsto (eigenFinsetSeq (I := I) (M := M) g r s)
      Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_finset_of_monotone
    (eigenFinsetSeq_monotone (I := I) (M := M) g r s)
    (eigenFinsetSeq_mem (I := I) (M := M) g r s)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenFinsetSeq_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.eigenFinsetSeq_tendsto target :: scope.openDecls } }

private def ellOneCoeff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (C : ℝ) (k : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) : ℝ :=
  |spectralCoeff (I := I) (M := M) g r s u i| *
    (C * tensorSobolevWeight (I := I) (M := M) i ((2 * k + 1 : ℕ) : ℝ))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ellOneCoeff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.ellOneCoeff target :: scope.openDecls } }

private lemma ellOneCoeff_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) {C : ℝ} (hC : 0 ≤ C) (k : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    0 ≤ ellOneCoeff (I := I) (M := M) g r s u C k i := by
  unfold ellOneCoeff
  have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i ((2 * k + 1 : ℕ) : ℝ) :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i _
  have hc : 0 ≤ |spectralCoeff (I := I) (M := M) g r s u i| := abs_nonneg _
  positivity

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ellOneCoeff_nonneg
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.ellOneCoeff_nonneg target :: scope.openDecls } }

private lemma ellOneCoeff_summable (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u : TensorL2 r s g) (h_mem : MemAllTensorHs (I := I) (M := M) g r s u)
    (h_tail : EigenvalueTailSummable (I := I) (M := M) g r s)
    (C : ℝ) (k : ℕ) :
    Summable (ellOneCoeff (I := I) (M := M) g r s u C k) := by
  have h := spectralCoeff_weightedPow_summable (I := I) (M := M) g r s u h_mem h_tail
    (2 * k + 1)
  have h_eq :
      ellOneCoeff (I := I) (M := M) g r s u C k =
        fun i => C *
          (|spectralCoeff (I := I) (M := M) g r s u i| *
            tensorSobolevWeight (I := I) (M := M) i ((2 * k + 1 : ℕ) : ℝ)) := by
    funext i; unfold ellOneCoeff; ring
  rw [h_eq]
  exact h.mul_left C

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ellOneCoeff_summable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.ellOneCoeff_summable target :: scope.openDecls } }

private def partialSumFun (g : SmoothRiemannianMetric I M) (r s' : ℕ)
    (u : TensorL2 r s' g) (α : M) (P₀ : TensorCompIdx (E := E) r s')
    (s : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s')) :
    EuclN → ℝ :=
  fun y => ∑ i ∈ s,
    spectralCoeff (I := I) (M := M) g r s' u i *
      eigenvectorComp (I := I) (M := M) g r s' i α P₀ y

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumFun
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumFun target :: scope.openDecls } }


private lemma scaledEigenvectorComp_memWkp (g : SmoothRiemannianMetric I M)
    (r s' : ℕ) (u : TensorL2 r s' g) (k : ℕ) (α : M)
    (P₀ : TensorCompIdx (E := E) r s')
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s') :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (fun y => spectralCoeff (I := I) (M := M) g r s' u i *
        eigenvectorComp (I := I) (M := M) g r s' i α P₀ y)
      (chartTargetEuclid (I := I) (M := M) α) :=
  MemWkp.const_smul (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (eigenvectorComp_memWkp (I := I) (M := M) g r s' i k α P₀)
    (spectralCoeff (I := I) (M := M) g r s' u i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.scaledEigenvectorComp_memWkp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.scaledEigenvectorComp_memWkp target :: scope.openDecls } }


private lemma partialSumFun_memWkp (g : SmoothRiemannianMetric I M) (r s' : ℕ)
    (u : TensorL2 r s' g) (k : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s')
    (s : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s')) :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (partialSumFun (I := I) (M := M) g r s' u α P₀ s)
      (chartTargetEuclid (I := I) (M := M) α) :=
  memWkp_finset_sum (d := Module.finrank ℝ E)
    (chartTargetEuclid_isOpen (I := I) (M := M) α) s _
    (fun i _ => scaledEigenvectorComp_memWkp (I := I) (M := M) g r s' u k α P₀ i)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumFun_memWkp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumFun_memWkp target :: scope.openDecls } }

private lemma partialSumFun_wkpNorm_le (g : SmoothRiemannianMetric I M) (r s' : ℕ)
    (u : TensorL2 r s' g) (k : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s')
    {C : ℝ} (hC : 0 ≤ C)
    (hC_bd : ∀ i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s',
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
          (eigenvectorComp (I := I) (M := M) g r s' i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal
          (C * tensorSobolevWeight (I := I) (M := M) i ((2 * k + 1 : ℕ) : ℝ)))
    (s : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s')) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (partialSumFun (I := I) (M := M) g r s' u α P₀ s)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal (∑ i ∈ s, ellOneCoeff (I := I) (M := M) g r s' u C k i) := by
  classical
  have h_open := chartTargetEuclid_isOpen (I := I) (M := M) α
  have h := wkpNorm_finset_sum_le (d := Module.finrank ℝ E) h_open s
    (fun i => fun y => spectralCoeff (I := I) (M := M) g r s' u i *
      eigenvectorComp (I := I) (M := M) g r s' i α P₀ y)
    (fun i _ => scaledEigenvectorComp_memWkp (I := I) (M := M) g r s' u k α P₀ i)
    (fun i => ellOneCoeff (I := I) (M := M) g r s' u C k i)
    (fun i _ => ellOneCoeff_nonneg (I := I) (M := M) g r s' u hC k i)
    1
    (fun i _ => ?_)
  · rw [mul_one] at h
    exact h
  · rw [mul_one]
    have h_smul := wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) h_open
      (eigenvectorComp_memWkp (I := I) (M := M) g r s' i k α P₀)
      (spectralCoeff (I := I) (M := M) g r s' u i)
    rw [h_smul]
    have h_enorm : ‖spectralCoeff (I := I) (M := M) g r s' u i‖ₑ =
        ENNReal.ofReal |spectralCoeff (I := I) (M := M) g r s' u i| := by
      rw [Real.enorm_eq_ofReal_abs]
    rw [h_enorm]
    refine (mul_le_mul_of_nonneg_left (hC_bd i) (zero_le)).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumFun_wkpNorm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumFun_wkpNorm_le target :: scope.openDecls } }

open _root_.Classical in
private lemma partialSumFun_sub_of_subset (g : SmoothRiemannianMetric I M)
    (r s' : ℕ) (u : TensorL2 r s' g) (α : M) (P₀ : TensorCompIdx (E := E) r s')
    {s t : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s')}
    (hst : s ⊆ t) :
    (fun y => partialSumFun (I := I) (M := M) g r s' u α P₀ t y -
        partialSumFun (I := I) (M := M) g r s' u α P₀ s y) =
      partialSumFun (I := I) (M := M) g r s' u α P₀ (t \ s) := by
  classical
  funext y
  rw [partialSumFun, partialSumFun, partialSumFun,
    Finset.sum_sdiff_eq_sub hst]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumFun_sub_of_subset
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumFun_sub_of_subset target :: scope.openDecls } }

private lemma partialSumFun_wkpNorm_sub_le (g : SmoothRiemannianMetric I M)
    (r s' : ℕ) (u : TensorL2 r s' g)
    (h_mem : MemAllTensorHs (I := I) (M := M) g r s' u)
    (h_tail : EigenvalueTailSummable (I := I) (M := M) g r s')
    (k : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s')
    {C : ℝ} (hC : 0 ≤ C)
    (hC_bd : ∀ i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s',
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
          (eigenvectorComp (I := I) (M := M) g r s' i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ENNReal.ofReal
          (C * tensorSobolevWeight (I := I) (M := M) i ((2 * k + 1 : ℕ) : ℝ)))
    {s t : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s')}
    (hst : s ⊆ t) :
    iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (fun y => partialSumFun (I := I) (M := M) g r s' u α P₀ t y -
          partialSumFun (I := I) (M := M) g r s' u α P₀ s y)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      ENNReal.ofReal
        ((∑' i, ellOneCoeff (I := I) (M := M) g r s' u C k i) -
          ∑ i ∈ s, ellOneCoeff (I := I) (M := M) g r s' u C k i) := by
  classical
  have h_summ := ellOneCoeff_summable (I := I) (M := M) g r s' u h_mem h_tail C k
  have h_nn := ellOneCoeff_nonneg (I := I) (M := M) g r s' u hC k
  rw [partialSumFun_sub_of_subset (I := I) (M := M) g r s' u α P₀ hst]
  refine (partialSumFun_wkpNorm_le (I := I) (M := M) g r s' u k α P₀ hC hC_bd
    (t \ s)).trans ?_
  rw [Finset.sum_sdiff_eq_sub hst]
  refine ENNReal.ofReal_le_ofReal ?_
  have h_t_le : ∑ i ∈ t, ellOneCoeff (I := I) (M := M) g r s' u C k i ≤
      ∑' i, ellOneCoeff (I := I) (M := M) g r s' u C k i :=
    Summable.sum_le_tsum t (fun i _ => h_nn i) h_summ
  linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumFun_wkpNorm_sub_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumFun_wkpNorm_sub_le target :: scope.openDecls } }

private def partialSumLp (g : SmoothRiemannianMetric I M) (r s' : ℕ)
    (u : TensorL2 r s' g) (α : M) (P₀ : TensorCompIdx (E := E) r s')
    (s : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s')) :
    Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
  ∑ i ∈ s, spectralCoeff (I := I) (M := M) g r s' u i •
    tensorL2ChartComponent (I := I) (M := M) g r s'
      (eigenbasisVec (I := I) (M := M) g r s' i) α P₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumLp
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumLp target :: scope.openDecls } }

private lemma partialSumLp_coeFn (g : SmoothRiemannianMetric I M) (r s' : ℕ)
    (u : TensorL2 r s' g) (α : M) (P₀ : TensorCompIdx (E := E) r s')
    (s : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s')) :
    ((partialSumLp (I := I) (M := M) g r s' u α P₀ s :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
      =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
      partialSumFun (I := I) (M := M) g r s' u α P₀ s := by
  classical
  have h_sum := coeFn_finsetSum_chartL2 (I := I) (M := M) α s
    (fun i => spectralCoeff (I := I) (M := M) g r s' u i •
      tensorL2ChartComponent (I := I) (M := M) g r s'
        (eigenbasisVec (I := I) (M := M) g r s' i) α P₀)
  refine h_sum.trans ?_
  have h_each : ∀ i ∈ s,
      ((spectralCoeff (I := I) (M := M) g r s' u i •
          tensorL2ChartComponent (I := I) (M := M) g r s'
            (eigenbasisVec (I := I) (M := M) g r s' i) α P₀ :
          Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) : EuclN → ℝ)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α]
        fun y => spectralCoeff (I := I) (M := M) g r s' u i *
          eigenvectorComp (I := I) (M := M) g r s' i α P₀ y := by
    intro i _
    have h := Lp.coeFn_smul (spectralCoeff (I := I) (M := M) g r s' u i)
      (tensorL2ChartComponent (I := I) (M := M) g r s'
        (eigenbasisVec (I := I) (M := M) g r s' i) α P₀)
    filter_upwards [h] with y hy
    rw [hy]
    rfl
  have h_fin := finsetSum_ae_eq (I := I) (M := M) α s h_each
  refine h_fin.trans (Filter.EventuallyEq.of_eq ?_)
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumLp_coeFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumLp_coeFn target :: scope.openDecls } }

private lemma partialSumLp_tendsto (g : SmoothRiemannianMetric I M) (r s' : ℕ)
    [Encodable (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s')]
    (u : TensorL2 r s' g) (α : M) (P₀ : TensorCompIdx (E := E) r s') :
    Filter.Tendsto
      (fun n => partialSumLp (I := I) (M := M) g r s' u α P₀
        (eigenFinsetSeq (I := I) (M := M) g r s' n))
      Filter.atTop
      (𝓝 (tensorL2ChartComponent (I := I) (M := M) g r s' u α P₀)) := by
  classical
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
    (g := g) (r := r) (s := s')
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s')
    with hb_def
  have h_repr : HasSum (fun i => b.repr u i • b i) u := b.hasSum_repr u
  have h_mapped :=
    h_repr.mapL (tensorL2ChartComponentCLM (I := I) (M := M) g r s' α P₀)
  have h_summand_eq : (fun i => tensorL2ChartComponentCLM (I := I) (M := M) g r s' α P₀
        (b.repr u i • b i)) =
      fun i => spectralCoeff (I := I) (M := M) g r s' u i •
        tensorL2ChartComponent (I := I) (M := M) g r s'
          (eigenbasisVec (I := I) (M := M) g r s' i) α P₀ := by
    funext i
    rw [map_smul]
    rw [tensorL2ChartComponentCLM_apply]
    have h_coeff : b.repr u i = spectralCoeff (I := I) (M := M) g r s' u i := rfl
    have h_vec : b i = eigenbasisVec (I := I) (M := M) g r s' i := by
      rw [hb_def, tensorResolventHilbertEigenbasisSigma_apply]
      rfl
    rw [h_coeff, h_vec]
  have h_limit_eq :
      tensorL2ChartComponentCLM (I := I) (M := M) g r s' α P₀ u =
        tensorL2ChartComponent (I := I) (M := M) g r s' u α P₀ :=
    tensorL2ChartComponentCLM_apply (I := I) (M := M) g r s' α P₀ u
  rw [h_summand_eq, h_limit_eq] at h_mapped
  have h_tendsto_finset :
      Filter.Tendsto (fun t : Finset _ =>
          ∑ i ∈ t, spectralCoeff (I := I) (M := M) g r s' u i •
            tensorL2ChartComponent (I := I) (M := M) g r s'
              (eigenbasisVec (I := I) (M := M) g r s' i) α P₀)
        Filter.atTop
        (𝓝 (tensorL2ChartComponent (I := I) (M := M) g r s' u α P₀)) := by
    have := h_mapped
    rwa [HasSum, SummationFilter.unconditional_filter] at this
  exact h_tendsto_finset.comp (eigenFinsetSeq_tendsto (I := I) (M := M) g r s')

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumLp_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.partialSumLp_tendsto target :: scope.openDecls } }

private lemma ellOnePartial_tendsto (g : SmoothRiemannianMetric I M) (r s' : ℕ)
    [Encodable (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s')]
    (u : TensorL2 r s' g) (h_mem : MemAllTensorHs (I := I) (M := M) g r s' u)
    (h_tail : EigenvalueTailSummable (I := I) (M := M) g r s') (C : ℝ) (k : ℕ) :
    Filter.Tendsto
      (fun n => ∑ i ∈ eigenFinsetSeq (I := I) (M := M) g r s' n,
        ellOneCoeff (I := I) (M := M) g r s' u C k i)
      Filter.atTop
      (𝓝 (∑' i, ellOneCoeff (I := I) (M := M) g r s' u C k i)) := by
  have h_summ := ellOneCoeff_summable (I := I) (M := M) g r s' u h_mem h_tail C k
  have h_hasSum := h_summ.hasSum
  have h_tendsto_finset :
      Filter.Tendsto
        (fun t : Finset _ => ∑ i ∈ t,
          ellOneCoeff (I := I) (M := M) g r s' u C k i)
        Filter.atTop
        (𝓝 (∑' i, ellOneCoeff (I := I) (M := M) g r s' u C k i)) := by
    have h := h_hasSum
    rw [h_hasSum.tsum_eq]
    rwa [HasSum, SummationFilter.unconditional_filter] at h
  exact h_tendsto_finset.comp (eigenFinsetSeq_tendsto (I := I) (M := M) g r s')

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.ellOnePartial_tendsto
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.ellOnePartial_tendsto target :: scope.openDecls } }

private lemma gateElement_chartComponent_memWkp_of_tail
    (g : SmoothRiemannianMetric I M) (r s' : ℕ)
    [Encodable (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s')]
    (u : TensorL2 r s' g) (h_mem : MemAllTensorHs (I := I) (M := M) g r s' u)
    (h_tail : EigenvalueTailSummable (I := I) (M := M) g r s')
    (k : ℕ) (α : M) (P₀ : TensorCompIdx (E := E) r s') :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (fun y => (tensorL2ChartComponent (I := I) (M := M) g r s' u α P₀ :
        Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α)) y)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  obtain ⟨C, hC_nn, hC_bd⟩ :=
    eigenvectorComp_wkpNorm_le_weight (I := I) (M := M) g r s' k α P₀
  set useq : ℕ → EuclN → ℝ := fun n =>
    partialSumFun (I := I) (M := M) g r s' u α P₀
      (eigenFinsetSeq (I := I) (M := M) g r s' n) with huseq_def
  have h_useq_mem : ∀ n, MemWkp (d := Module.finrank ℝ E) (2 * k) 2 (useq n) Ω :=
    fun n => partialSumFun_memWkp (I := I) (M := M) g r s' u k α P₀ _
  set S := ∑' i, ellOneCoeff (I := I) (M := M) g r s' u C k i with hS_def
  have h_partial_tendsto :=
    ellOnePartial_tendsto (I := I) (M := M) g r s' u h_mem h_tail C k
  have h_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
        (fun y => useq m y - useq n y) Ω ≤ ENNReal.ofReal ε := by
    intro ε hε
    have h_gap_tendsto : Filter.Tendsto
        (fun n => S - ∑ i ∈ eigenFinsetSeq (I := I) (M := M) g r s' n,
          ellOneCoeff (I := I) (M := M) g r s' u C k i)
        Filter.atTop (𝓝 (S - S)) :=
      Filter.Tendsto.const_sub S h_partial_tendsto
    rw [sub_self] at h_gap_tendsto
    have h_eventually : ∀ᶠ n in Filter.atTop,
        S - ∑ i ∈ eigenFinsetSeq (I := I) (M := M) g r s' n,
          ellOneCoeff (I := I) (M := M) g r s' u C k i < ε :=
      (h_gap_tendsto.eventually (gt_mem_nhds hε)).mono
        (fun n hn => by simpa using hn)
    obtain ⟨N, hN⟩ := h_eventually.exists_forall_of_atTop
    refine ⟨N, fun m n hm hn => ?_⟩
    have h_ellOne_nn := ellOneCoeff_nonneg (I := I) (M := M) g r s' u hC_nn k
    have h_mono_partial : ∀ {a b : ℕ}, a ≤ b →
        (∑ i ∈ eigenFinsetSeq (I := I) (M := M) g r s' a,
          ellOneCoeff (I := I) (M := M) g r s' u C k i) ≤
        ∑ i ∈ eigenFinsetSeq (I := I) (M := M) g r s' b,
          ellOneCoeff (I := I) (M := M) g r s' u C k i := by
      intro a b hab
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (eigenFinsetSeq_monotone (I := I) (M := M) g r s' hab)
        (fun i _ _ => h_ellOne_nn i)
    have key : ∀ {a c : ℕ}, N ≤ a → a ≤ c →
        iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
          (fun y => useq c y - useq a y) Ω ≤ ENNReal.ofReal ε := by
      intro a c haN hac
      have h_sub : eigenFinsetSeq (I := I) (M := M) g r s' a ⊆
          eigenFinsetSeq (I := I) (M := M) g r s' c :=
        eigenFinsetSeq_monotone (I := I) (M := M) g r s' hac
      have h_bd := partialSumFun_wkpNorm_sub_le (I := I) (M := M) g r s' u
        h_mem h_tail k α P₀ hC_nn hC_bd h_sub
      refine h_bd.trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have h_gap_a : S - ∑ i ∈ eigenFinsetSeq (I := I) (M := M) g r s' a,
          ellOneCoeff (I := I) (M := M) g r s' u C k i < ε := hN a haN
      linarith [h_gap_a]
    rcases le_total m n with hmn | hnm
    · have h := key hm hmn
      have h_neg : (fun y => useq m y - useq n y) =
          (fun y => (-1 : ℝ) * (useq n y - useq m y)) := by
        funext y; ring
      rw [h_neg]
      have h_nm_mem : MemWkp (d := Module.finrank ℝ E) (2 * k) 2
          (fun y => useq n y - useq m y) Ω :=
        MemWkp.sub (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          hΩ_open (h_useq_mem n) (h_useq_mem m)
      rw [wkpNorm_const_smul (d := Module.finrank ℝ E)
        (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_nm_mem (-1)]
      rw [show ‖(-1 : ℝ)‖ₑ = 1 by rw [enorm_neg, enorm_one], one_mul]
      exact key hm hmn
    · exact key hn hnm
  obtain ⟨F_lim, hF_lim_mem, hF_lim_tendsto⟩ :=
    MemWkp.exists_limit_of_wkpNorm_cauchy
      (d := Module.finrank ℝ E) hΩ_open (2 * k) 2
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      h_useq_mem h_cauchy
  have hF_lim_memLp : _root_.MeasureTheory.MemLp F_lim 2 ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω) :=
    hF_lim_mem.memLp
  set T : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
    tensorL2ChartComponent (I := I) (M := M) g r s' u α P₀ with hT_def
  set Flim_Lp : _root_.MeasureTheory.Lp ℝ 2 (chartLebesgueMeasure (I := I) (M := M) α) :=
    hF_lim_memLp.toLp F_lim with hFlim_Lp_def
  have h_lp_T : Filter.Tendsto
      (fun n => partialSumLp (I := I) (M := M) g r s' u α P₀
        (eigenFinsetSeq (I := I) (M := M) g r s' n)) Filter.atTop (𝓝 T) :=
    partialSumLp_tendsto (I := I) (M := M) g r s' u α P₀
  have h_lp_Flim : Filter.Tendsto
      (fun n => partialSumLp (I := I) (M := M) g r s' u α P₀
        (eigenFinsetSeq (I := I) (M := M) g r s' n)) Filter.atTop (𝓝 Flim_Lp) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h_norm_eq : ∀ n,
        ‖partialSumLp (I := I) (M := M) g r s' u α P₀
            (eigenFinsetSeq (I := I) (M := M) g r s' n) - Flim_Lp‖ =
          (_root_.MeasureTheory.eLpNorm (fun y => useq n y - F_lim y) 2
            (chartLebesgueMeasure (I := I) (M := M) α)).toReal := by
      intro n
      rw [Lp.norm_def]
      congr 1
      refine _root_.MeasureTheory.eLpNorm_congr_ae ?_
      have h1 := Lp.coeFn_sub (partialSumLp (I := I) (M := M) g r s' u α P₀
        (eigenFinsetSeq (I := I) (M := M) g r s' n)) Flim_Lp
      have h2 := partialSumLp_coeFn (I := I) (M := M) g r s' u α P₀
        (eigenFinsetSeq (I := I) (M := M) g r s' n)
      have h3 : (Flim_Lp : EuclN → ℝ)
          =ᵐ[chartLebesgueMeasure (I := I) (M := M) α] F_lim :=
        MemLp.coeFn_toLp hF_lim_memLp
      filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
      rw [hy1, Pi.sub_apply, hy2, hy3]
    have h_eLp_Flim : Filter.Tendsto
        (fun n => _root_.MeasureTheory.eLpNorm (fun y => useq n y - F_lim y) 2
          (chartLebesgueMeasure (I := I) (M := M) α)) Filter.atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        (g := fun _ => (0 : ℝ≥0∞))
        (h := fun n => iteratedWeakSobolevNorm (d := Module.finrank ℝ E) (2 * k) 2
          (fun y => useq n y - F_lim y) Ω)
        tendsto_const_nhds hF_lim_tendsto (fun _ => zero_le)
        (fun n => eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) (2 * k) 2 Ω _)
    have h_toReal : Filter.Tendsto
        (fun n => (_root_.MeasureTheory.eLpNorm (fun y => useq n y - F_lim y) 2
          (chartLebesgueMeasure (I := I) (M := M) α)).toReal) Filter.atTop (𝓝 0) := by
      have := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))).tendsto.comp
        h_eLp_Flim
      change Filter.Tendsto
          (fun n => (_root_.MeasureTheory.eLpNorm (fun y => useq n y - F_lim y) 2
            (chartLebesgueMeasure (I := I) (M := M) α)).toReal)
          Filter.atTop _ at this
      exact this
    refine h_toReal.congr ?_
    intro n; exact (h_norm_eq n).symm
  have hT_eq : T = Flim_Lp := tendsto_nhds_unique h_lp_T h_lp_Flim
  have hae : F_lim =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict Ω]
      (fun y => (T : EuclN → ℝ) y) := by
    have h3 : (Flim_Lp : EuclN → ℝ)
        =ᵐ[chartLebesgueMeasure (I := I) (M := M) α] F_lim :=
      MemLp.coeFn_toLp hF_lim_memLp
    rw [hT_eq]
    exact h3.symm
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hΩ_open hae).mp hF_lim_mem

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.gateElement_chartComponent_memWkp_of_tail
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.MetricRealization.gateElement_chartComponent_memWkp_of_tail target :: scope.openDecls } }

theorem spectralChartRegularity_of_eigenvalueTailSummable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_tail : EigenvalueTailSummable (I := I) (M := M) g r s) :
    SpectralChartRegularity (I := I) (M := M) g r s := by
  intro u h_mem k α P₀
  have : Countable (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :=
    DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.countable_tensorEigenIdx
      (I := I) (M := M) (g := g) (r := r) (s := s)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
  let : Encodable (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :=
    Encodable.ofCountable _
  exact gateElement_chartComponent_memWkp_of_tail (I := I) (M := M) g r s u h_mem
    h_tail k α P₀

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralChartRegularity_of_eigenvalueTailSummable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralChartRegularity_of_eigenvalueTailSummable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralChartRegularity_of_eigenvalueTailSummable ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralChartRegularity_of_eigenvalueTailSummable

theorem spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_tail : EigenvalueTailSummable (I := I) (M := M) g r s) :
    SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s :=
  spectralSmooth_realizesAsSmooth_of_reduction (I := I) (M := M) g r s
    (spectralChartRegularity_of_eigenvalueTailSummable (I := I) (M := M) g r s h_tail)
    (tensorSuperCriticalReconstruct (I := I) (M := M) g r s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable ``Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization.spectralSmoothRealizesAsSmooth_of_eigenvalueTailSummable

end MetricRealization
end Spectral
end Analysis
end DifferentialGeometry

end
