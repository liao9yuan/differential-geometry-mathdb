import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChristoffelCorrectionL2.FiberNormGradientDecomp
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChristoffelCorrectionL2.IntrinsicCovAtomL2Fiber
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.ChristoffelCorrectionL2.IntrinsicSlotOpNormRiem
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorComponent.GradientLpNormPerIndex

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace HebeyBlock

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Tensor.TensorRSRiemannianBundle
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

private local instance tensorRSRiemannianNormedAddCommGroup
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorRSRiemannianNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.tensorRSRiemannianNormedAddCommGroup target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma a3_pouTsupport_isCompact (α : M) :
    IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).isCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.a3_pouTsupport_isCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.a3_pouTsupport_isCompact target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma a3_pouTsupport_subset_chartSource (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source :=
  chartAtlasPOU_isSubordinate (I := I) (M := M) α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.a3_pouTsupport_subset_chartSource
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.a3_pouTsupport_subset_chartSource target :: scope.openDecls } }

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompactSpace M] in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma chartTensorRSCovariantDerivative_totalSpace_continuousOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) (k : Fin (Module.finrank ℝ E)) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    ContinuousOn
      (fun b : M =>
        (TotalSpace.mk' (TensorRSModel r s ℝ E)
          (E := fun y : M => TensorRSSpace r s I y) b
          (chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b) :
          _root_.Bundle.TotalSpace (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y)))
      (chartAt H α).source := by
  classical
  have hbase_eq :
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet =
        (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  have hsmooth :=
    tensorCovDeriv_chartBasis_contMDiffOn (I := I) (M := M) g r s
      S.toCcTensor α k
  have hcont :
      ContinuousOn
        (fun b : M =>
          (TotalSpace.mk' (TensorRSModel r s ℝ E)
            (E := fun y : M => TensorRSSpace r s I y) b
            (tensorCovDerivAt (I := I) (M := M) g r s S.toCcTensor b
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b)) :
            _root_.Bundle.TotalSpace (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y)))
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    hsmooth.continuousOn
  rw [hbase_eq] at hcont
  refine hcont.congr ?_
  intro b hb
  have hcov_eq :=
    chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
      (I := I) (M := M) g r s α S.toCcTensor (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) hb
  simp only [hcov_eq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSCovariantDerivative_totalSpace_continuousOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSCovariantDerivative_totalSpace_continuousOn target :: scope.openDecls } }

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma chartTensorRSCovariantDerivative_pouWeightedNorm_aestronglyMeasurable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    _root_.MeasureTheory.AEStronglyMeasurable
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b‖ ^ 2))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  set ρ : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  set f : M → ℝ := fun b : M =>
    ρ b *
      Real.sqrt
        (∑ k : Fin (Module.finrank ℝ E),
          ‖chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b‖ ^ 2) with hf_def
  have h_indicator_eq :
      f = (tsupport ρ).indicator f := by
    funext b
    by_cases hb : b ∈ tsupport ρ
    · rw [Set.indicator_of_mem hb]
    · rw [Set.indicator_of_notMem hb]
      have hρ_zero : ρ b = 0 := by
        by_contra hne
        exact hb (subset_tsupport _ hne)
      rw [hf_def]; simp only [hρ_zero, _root_.MulZeroClass.zero_mul]
  have h_meas : MeasurableSet (tsupport ρ) :=
    (isClosed_tsupport _).measurableSet
  rw [h_indicator_eq, aestronglyMeasurable_indicator_iff h_meas]
  refine ContinuousOn.aestronglyMeasurable_of_isCompact ?_
    (a3_pouTsupport_isCompact (I := I) (M := M) α)
    h_meas
  have hsub : tsupport ρ ⊆ (chartAt H α).source :=
    a3_pouTsupport_subset_chartSource (I := I) (M := M) α
  have h_pou_on : ContinuousOn ρ (tsupport ρ) := by
    rw [hρ_def]
    exact ((chartAtlasPOU I M α).contMDiff.continuous).continuousOn
  have h_sumsq : ContinuousOn
      (fun b : M =>
        ∑ k : Fin (Module.finrank ℝ E),
          ‖chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b‖ ^ 2)
      (chartAt H α).source := by
    refine continuousOn_finsetSum _ (fun k _ => ?_)
    have h_inner : ContinuousOn
        (fun b : M =>
          (⟪chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b,
            chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b⟫_ℝ : ℝ))
        (chartAt H α).source :=
      ContinuousOn.inner_bundle
        (chartTensorRSCovariantDerivative_totalSpace_continuousOn (I := I) (M := M) g r s α S k)
        (chartTensorRSCovariantDerivative_totalSpace_continuousOn (I := I) (M := M) g r s α S k)
    refine h_inner.congr ?_
    intro b _
    exact (real_inner_self_eq_norm_sq _).symm
  have h_sqrt : ContinuousOn
      (fun b : M =>
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b‖ ^ 2))
      (chartAt H α).source :=
    Real.continuous_sqrt.comp_continuousOn h_sumsq
  exact h_pou_on.mul (h_sqrt.mono hsub)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSCovariantDerivative_pouWeightedNorm_aestronglyMeasurable
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSCovariantDerivative_pouWeightedNorm_aestronglyMeasurable target :: scope.openDecls } }

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma chartTensorRSSlotCorrection_norm_sq_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) (k : Fin (Module.finrank ℝ E)) (b : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    ‖- (∑ i : Fin r,
          chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b i)
      + (∑ l : Fin s,
          chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b l)‖ ^ 2 ≤
      (2 * ((r : ℝ) + (s : ℝ))) *
        ((∑ i : Fin r,
            ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b i‖ ^ 2) +
          (∑ l : Fin s,
            ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b l‖ ^ 2)) := by
  classical
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  let : NormedAddCommGroup (TensorRSSpace r s I b) :=
    tensorRSRiemannianNormedAddCommGroup r s b
  set a : Fin r → TensorRSSpace r s I b := fun i =>
    chartTensorRSInputSlotCorrection (I := I) r s g α
      (fun b' => S.toCcTensor.toSection b') (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b i
    with ha_def
  set c : Fin s → TensorRSSpace r s I b := fun l =>
    chartTensorRSOutputSlotCorrection (I := I) r s g α
      (fun b' => S.toCcTensor.toSection b') (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b l
    with hc_def
  have h_a_sum_nn : 0 ≤ ∑ i : Fin r, ‖a i‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_c_sum_nn : 0 ≤ ∑ l : Fin s, ‖c l‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h_split :
      ‖- (∑ i : Fin r, a i) + (∑ l : Fin s, c l)‖ ^ 2 ≤
        2 * (‖∑ i : Fin r, a i‖ ^ 2 + ‖∑ l : Fin s, c l‖ ^ 2) :=
    norm_sq_neg_sum_add_sum_le_two_mul a c
  have h_u_pm : ‖∑ i : Fin r, a i‖ ^ 2 ≤ (r : ℝ) * ∑ i : Fin r, ‖a i‖ ^ 2 := by
    simpa using sum_norm_sq_le_card_mul_sum_norm_sq
      (s := (Finset.univ : Finset (Fin r))) a
  have h_v_pm : ‖∑ l : Fin s, c l‖ ^ 2 ≤ (s : ℝ) * ∑ l : Fin s, ‖c l‖ ^ 2 := by
    simpa using sum_norm_sq_le_card_mul_sum_norm_sq
      (s := (Finset.univ : Finset (Fin s))) c
  have h_r_le : (r : ℝ) ≤ (r : ℝ) + (s : ℝ) := by
    have : (0 : ℝ) ≤ (s : ℝ) := by positivity
    linarith
  have h_s_le : (s : ℝ) ≤ (r : ℝ) + (s : ℝ) := by
    have : (0 : ℝ) ≤ (r : ℝ) := by positivity
    linarith
  calc ‖- (∑ i : Fin r, a i) + (∑ l : Fin s, c l)‖ ^ 2
      ≤ 2 * (‖∑ i : Fin r, a i‖ ^ 2 + ‖∑ l : Fin s, c l‖ ^ 2) := h_split
    _ ≤ 2 * ((r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2)
          + (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2)) := by
        have := add_le_add h_u_pm h_v_pm; linarith
    _ ≤ (2 * ((r : ℝ) + (s : ℝ))) *
          ((∑ i : Fin r, ‖a i‖ ^ 2) + (∑ l : Fin s, ‖c l‖ ^ 2)) := by
        have h1 : (r : ℝ) * (∑ i : Fin r, ‖a i‖ ^ 2) ≤
            ((r : ℝ) + (s : ℝ)) * (∑ i : Fin r, ‖a i‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h_r_le h_a_sum_nn
        have h2 : (s : ℝ) * (∑ l : Fin s, ‖c l‖ ^ 2) ≤
            ((r : ℝ) + (s : ℝ)) * (∑ l : Fin s, ‖c l‖ ^ 2) :=
          mul_le_mul_of_nonneg_right h_s_le h_c_sum_nn
        nlinarith only [h1, h2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSSlotCorrection_norm_sq_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.chartTensorRSSlotCorrection_norm_sq_le target :: scope.openDecls } }

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompleteSpace E] in
theorem exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        _root_.MeasureTheory.eLpNorm (fun b : M => Real.sqrt
            (g.inner b
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b)
              (gradFun (I := I) g
                (tensorChartComponentScalar (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx) b))) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  simpa only using
    Analysis.Parabolic.TensorSpectral.exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
      (I := I) (M := M) g r s α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.HebeyBlock.exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.HebeyBlock.exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm ``Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm

end HebeyBlock
end Sobolev
end Analysis
end DifferentialGeometry

end
