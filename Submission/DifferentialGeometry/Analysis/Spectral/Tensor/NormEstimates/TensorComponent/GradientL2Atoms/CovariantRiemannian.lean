import Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.Chart.Components
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.ChartGeometry.GoodSetMeasure
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelL2BoundFromH1
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentL2BoundUniform
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.CovL2BoundFromH1
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.H1Compl
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.PreHilbert
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.SlotChartSmoothness
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.SlotBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChristoffelCorrection.ChristoffelBound
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.TrivProj.ChartTwistIdentity
import Submission.DifferentialGeometry.Geometry.Connection.ChartTensorNabla.TensorRS.ChartTensorRSCovariantDerivativeAgreement
import Submission.DifferentialGeometry.Analysis.Elliptic.TensorRegularity.CovariantDerivativeBounds.SlotCorrection.Kernel
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.FiberFromModel
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.UniformChartBounds.Tensor.FiberToModel
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorComponent.GradientL2Atoms.CovariantChartSource

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Connection


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem


section CovariantAtomsRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
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

private local instance covariantAtomTensorRSRiemannianNormedAddCommGroup
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantAtomTensorRSRiemannianNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covariantAtomTensorRSRiemannianNormedAddCommGroup target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private lemma covRiem_pouTsupport_isCompact (α : M) :
    IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).isCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covRiem_pouTsupport_isCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covRiem_pouTsupport_isCompact target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma covRiem_pouTsupport_subset_chartSource (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source :=
  chartAtlasPOU_isSubordinate (I := I) (M := M) α

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covRiem_pouTsupport_subset_chartSource
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covRiem_pouTsupport_subset_chartSource target :: scope.openDecls } }

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
private lemma covRiem_mem_baseSet_of_mem_chartSource
    (r s : ℕ) (α : M) {b : M} (hb : b ∈ (chartAt H α).source) :
    b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
  change b ∈ (_root_.FiberBundle.trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
    (_root_.FiberBundle.trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet
  refine ⟨?_, ?_⟩
  all_goals
    change b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hb

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covRiem_mem_baseSet_of_mem_chartSource
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covRiem_mem_baseSet_of_mem_chartSource target :: scope.openDecls } }

attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
theorem exists_eLpNorm_pou_mul_sum_fiber_chart_cov_le_const_mul_h1Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (_Idx : Fin r → Fin (Module.finrank ℝ E))
        (_Jdx : Fin s → Fin (Module.finrank ℝ E)),
        _root_.MeasureTheory.eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  (∑ k : Fin (Module.finrank ℝ E),
                    ‖chartTensorRSCovariantDerivative (I := I) r s g α
                        (fun b' => S.toCcTensor.toSection b')
                        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b‖ ^ 2))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  obtain ⟨Cg2, hCg2_nn, hG2⟩ :=
    exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq
      (I := I) (M := M) g r s α
  have hK_compact :
      IsCompact (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    covRiem_pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub :
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        (chartAt H α).source :=
    covRiem_pouTsupport_subset_chartSource (I := I) (M := M) α
  obtain ⟨Cop, hCop_pos, hCop_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact
      (I := I) (M := M) g r s α hK_compact hK_sub
  have hCop_nn : 0 ≤ Cop := le_of_lt hCop_pos
  refine ⟨Cop * Cg2, mul_nonneg hCop_nn hCg2_nn, ?_⟩
  intro S _Idx _Jdx
  set gF : M → ℝ := fun b : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
      Real.sqrt
        (∑ k : Fin (Module.finrank ℝ E),
          ‖chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b‖ ^ 2)
    with hgF_def
  set gM : M → ℝ := fun b : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
      Real.sqrt
        (∑ k : Fin (Module.finrank ℝ E),
          ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2)
    with hgM_def
  have h_ptwise : ∀ b : M, gF b ≤ Cop * gM b := by
    intro b
    by_cases hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    · have hb_chart : b ∈ (chartAt H α).source := hK_sub hb
      have hb_base : b ∈ (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet :=
        covRiem_mem_baseSet_of_mem_chartSource (I := I) (M := M) r s α hb_chart
      have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
        (chartAtlasPOU I M).nonneg α b
      have h_per_k : ∀ k : Fin (Module.finrank ℝ E),
          ‖chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b‖ ^ 2 ≤
            Cop ^ 2 *
              ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2 := by
        intro k
        set X : TensorRSSpace r s I b :=
          chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b with hX_def
        set v : TensorRSModel r s ℝ E :=
          (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X
          with hv_def
        have h_roundtrip :
            ((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b v :
              TensorRSSpace r s I b) = X := by
          rw [hv_def]
          exact (_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).symmL_continuousLinearMapAt
            (R := ℝ) hb_base X
        have h_op : ‖((_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b v :
              TensorRSSpace r s I b)‖ ≤ Cop * ‖v‖ :=
          hCop_bound b hb v
        rw [h_roundtrip] at h_op
        have hX_nn : 0 ≤ ‖X‖ := norm_nonneg _
        calc
          ‖X‖ ^ 2 = ‖X‖ * ‖X‖ := by rw [sq]
          _ ≤ (Cop * ‖v‖) * (Cop * ‖v‖) :=
            mul_self_le_mul_self hX_nn h_op
          _ = Cop ^ 2 * ‖v‖ ^ 2 := by ring
      have h_sum_le :
          (∑ k : Fin (Module.finrank ℝ E),
            ‖chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b‖ ^ 2) ≤
            Cop ^ 2 *
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun k _ => h_per_k k)
      have h_sumM_nn :
          0 ≤ ∑ k : Fin (Module.finrank ℝ E),
            ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2 :=
        Finset.sum_nonneg (fun k _ => sq_nonneg _)
      have h_sqrt_le :
          Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b‖ ^ 2) ≤
            Cop *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                    (chartTensorRSCovariantDerivative (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2) := by
        have h1 := Real.sqrt_le_sqrt h_sum_le
        rwa [Real.sqrt_mul (sq_nonneg Cop), Real.sqrt_sq hCop_nn] at h1
      have h_mul :=
        mul_le_mul_of_nonneg_left h_sqrt_le hρ_nn
      rw [hgF_def, hgM_def]
      calc ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  ‖chartTensorRSCovariantDerivative (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b‖ ^ 2)
            ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                (Cop *
                  Real.sqrt
                    (∑ k : Fin (Module.finrank ℝ E),
                      ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                            ℝ b
                        (chartTensorRSCovariantDerivative (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) := h_mul
          _ = Cop *
                (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                  Real.sqrt
                    (∑ k : Fin (Module.finrank ℝ E),
                      ‖(_root_.FiberBundle.trivializationAt (TensorRSModel r s ℝ E)
                          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                            ℝ b
                        (chartTensorRSCovariantDerivative (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) := by ring
    · have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
        by_contra hne
        exact hb (subset_tsupport _ hne)
      simp only [hgF_def, hgM_def, hρ_zero, _root_.MulZeroClass.zero_mul, _root_.MulZeroClass.mul_zero, le_refl]
  have hgF_nn : ∀ b : M, 0 ≤ gF b := by
    intro b
    rw [hgF_def]
    exact mul_nonneg ((chartAtlasPOU I M).nonneg α b)
      (Real.sqrt_nonneg _)
  have h_mono :
      eLpNorm gF 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        eLpNorm (Cop • gM) 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine _root_.MeasureTheory.eLpNorm_mono_real (fun b => ?_)
    rw [Real.norm_of_nonneg (hgF_nn b)]
    simpa [Pi.smul_apply, smul_eq_mul] using h_ptwise b
  have h_smul :
      eLpNorm (Cop • gM) 2 (riemannianVolumeMeasure (I := I) (M := M) g) =
        ENNReal.ofReal Cop *
          eLpNorm gM 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [_root_.MeasureTheory.eLpNorm_const_smul Cop gM, Real.enorm_eq_ofReal hCop_nn]
  have hG2' :
      eLpNorm gM 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal Cg2 * (‖S‖₊ : ℝ≥0∞) := by
    rw [hgM_def]; exact hG2 S
  calc _root_.MeasureTheory.eLpNorm gF 2 (riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ _root_.MeasureTheory.eLpNorm (Cop • gM) 2 (riemannianVolumeMeasure (I := I) (M := M) g) := h_mono
    _ = ENNReal.ofReal Cop *
          eLpNorm gM 2 (riemannianVolumeMeasure (I := I) (M := M) g) := h_smul
    _ ≤ ENNReal.ofReal Cop * (ENNReal.ofReal Cg2 * (‖S‖₊ : ℝ≥0∞)) :=
        mul_le_mul_of_nonneg_left hG2' (zero_le)
    _ = ENNReal.ofReal (Cop * Cg2) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul hCop_nn, mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_pou_mul_sum_fiber_chart_cov_le_const_mul_h1Norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_pou_mul_sum_fiber_chart_cov_le_const_mul_h1Norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_pou_mul_sum_fiber_chart_cov_le_const_mul_h1Norm ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.exists_eLpNorm_pou_mul_sum_fiber_chart_cov_le_const_mul_h1Norm

end CovariantAtomsRiemannian

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
