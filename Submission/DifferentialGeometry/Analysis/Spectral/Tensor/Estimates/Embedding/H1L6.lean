import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ComponentL2.TensorSection
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentWkpNormBoundFromH1
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.NormEstimates.TensorComponent.GradientLpNormPerIndex
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.Subcritical
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.L2
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Inner

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic.TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
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

private theorem component_eLpNorm_six
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : MIdxC E r) (Jdx : MIdxC E s),
        eLpNorm (tensorChartComponentScalar (I := I) (M := M)
            g r s S.toCcTensor α Idx Jdx) 6
          (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  let : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  obtain ⟨Cgrad, hCgrad, hgrad⟩ :=
    exists_eLpNorm_sqrt_g_inner_gradFun_tensorChartComponentScalar_le_const_mul_h1Norm
      (I := I) (M := M) g r s α
  obtain ⟨Cw, hCw, hw⟩ :=
    tensorChartComponentScalar_wkpNormChart_le_const_mul_h1Norm
      (I := I) (M := M) g r s α hCgrad hgrad
  obtain ⟨Cs, hCs, hs⟩ :=
    sobolev_closed (I := I) (M := M) g
      (p := (2 : ℝ)) (by norm_num) (by rw [hDim]; norm_num)
  refine ⟨Cs * Cw, mul_nonneg hCs hCw, ?_⟩
  intro S Idx Jdx
  let u : M → ℝ := tensorChartComponentScalar (I := I) (M := M)
    g r s S.toCcTensor α Idx Jdx
  have hu_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ u :=
    tensorChartComponentScalar_contMDiff (I := I) (M := M)
      g r s S.toCcTensor α Idx Jdx
  have hu_mem : MemWkpChart (I := I) (M := M) 1 2 u :=
    tensorChartComponent_memWkpChart_one_two
      (I := I) (M := M) g r s S α Idx Jdx
  have hu_mem' : MemWkpChart (I := I) (M := M) 1
      (ENNReal.ofReal (2 : ℝ)) u := by
    simpa using hu_mem
  have hsix := hs hu_smooth.continuous.measurable hu_mem'
  have hexp : ENNReal.ofReal
      ((Module.finrank ℝ E : ℝ) * 2 /
        ((Module.finrank ℝ E : ℝ) - 2)) = 6 := by
    rw [hDim]
    norm_num
  rw [hexp] at hsix
  calc
    eLpNorm u 6 (riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ENNReal.ofReal Cs * wkpNormChart (I := I) (M := M) 1 2 u := by
      simpa [riemannianVolumeMeasure_def] using hsix
    _ ≤ ENNReal.ofReal Cs *
          (ENNReal.ofReal Cw * (‖S‖₊ : ℝ≥0∞)) :=
      mul_le_mul_of_nonneg_left (hw S Idx Jdx) (zero_le)
    _ = ENNReal.ofReal (Cs * Cw) * (‖S‖₊ : ℝ≥0∞) := by
      rw [ENNReal.ofReal_mul hCs, mul_assoc]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.component_eLpNorm_six
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.component_eLpNorm_six target :: scope.openDecls } }

private theorem sqrt_sum_sq_le_sum_abs {ι : Type*}
    (K : Finset ι) (f : ι → ℝ) :
    Real.sqrt (∑ i ∈ K, (f i) ^ 2) ≤ ∑ i ∈ K, |f i| := by
  classical
  have hsquares : ∑ i ∈ K, (f i) ^ 2 = ∑ i ∈ K, |f i| ^ 2 := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact (sq_abs (f i)).symm
  rw [hsquares]
  have hsum_nn : 0 ≤ ∑ i ∈ K, |f i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (f i))
  calc
    Real.sqrt (∑ i ∈ K, |f i| ^ 2)
        ≤ Real.sqrt ((∑ i ∈ K, |f i|) ^ 2) :=
      Real.sqrt_le_sqrt
        (Finset.sum_sq_le_sq_sum_of_nonneg
          (fun i _ => abs_nonneg (f i)))
    _ = ∑ i ∈ K, |f i| := Real.sqrt_sq hsum_nn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sqrt_sum_sq_le_sum_abs
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.sqrt_sum_sq_le_sum_abs target :: scope.openDecls } }

theorem h1_lp6_fiber_rs
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensorH1 g r s,
      _root_.MeasureTheory.lpNorm (fun x => Real.sqrt
          (riemannianFiberNormSq (I := I) (M := M) g r s x
            (S.toCcTensor.toSection x))) 6
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤ C * ‖S‖ := by
  classical
  let μ : _root_.MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  let K : Finset ((M × MIdxC E r) × MIdxC E s) :=
    ((chartAtlasPOUFinset (I := I) (M := M)).product Finset.univ).product
      Finset.univ
  obtain ⟨Cr, hCr, hrec⟩ := fiber_sq_le_comps (E := E) (I := I) (M := M) g r s
  choose Ca hCa hcomp using fun α : M =>
    component_eLpNorm_six (E := E) (I := I) (M := M) hDim g r s α
  let Csum : ℝ := ∑ q ∈ K, Ca q.1.1
  refine ⟨Real.sqrt Cr * Csum,
    mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun q _ => hCa q.1.1)), ?_⟩
  intro S
  let fiber : M → ℝ := fun x => Real.sqrt
    (riemannianFiberNormSq (I := I) (M := M) g r s x
      (S.toCcTensor.toSection x))
  let comp : ((M × MIdxC E r) × MIdxC E s) → M → ℝ := fun q =>
    tensorChartComponentScalar (I := I) (M := M)
      g r s S.toCcTensor q.1.1 q.1.2 q.2
  have hsum_sq (x : M) :
      ∑ α ∈ chartAtlasPOUFinset (I := I) (M := M),
          ∑ Idx : MIdxC E r, ∑ Jdx : MIdxC E s,
            (tensorChartComponentScalar (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx x) ^ 2 =
        ∑ q ∈ K, (comp q x) ^ 2 := by
    simp [K, comp, Finset.sum_product]
  have hpoint (x : M) : fiber x ≤
      Real.sqrt Cr * ∑ q ∈ K, |comp q x| := by
    have hsquare :
        riemannianFiberNormSq (I := I) (M := M) g r s x
            (S.toCcTensor.toSection x) ≤
          Cr * ∑ q ∈ K, (comp q x) ^ 2 := by
      rw [← hsum_sq x]
      rw [riemannianFiberNormSq_eq_tensorInnerPointwise
        (I := I) (M := M) g r s x (S.toCcTensor.toSection x),
        ← SmoothCcTensor.toFun_apply (I := I) (M := M) S.toCcTensor x]
      exact hrec S.toCcTensor x
    calc
      fiber x ≤ Real.sqrt (Cr * ∑ q ∈ K, (comp q x) ^ 2) :=
        Real.sqrt_le_sqrt hsquare
      _ = Real.sqrt Cr * Real.sqrt (∑ q ∈ K, (comp q x) ^ 2) :=
        Real.sqrt_mul hCr _
      _ ≤ Real.sqrt Cr * ∑ q ∈ K, |comp q x| :=
        mul_le_mul_of_nonneg_left
          (sqrt_sum_sq_le_sum_abs K (fun q => comp q x)) (Real.sqrt_nonneg _)
  have hcomp_meas : ∀ q,
      AEStronglyMeasurable (fun x => |comp q x|) μ := by
    intro q
    have hcont : Continuous (comp q) :=
      (tensorChartComponentScalar_contMDiff (I := I) (M := M)
        g r s S.toCcTensor q.1.1 q.1.2 q.2).continuous
    simpa only [Real.norm_eq_abs] using hcont.aestronglyMeasurable.norm
  have hfiber_eLp : _root_.MeasureTheory.eLpNorm fiber 6 μ ≤
      ENNReal.ofReal (Real.sqrt Cr) *
        eLpNorm (fun x => ∑ q ∈ K, |comp q x|) 6 μ := by
    calc
      _root_.MeasureTheory.eLpNorm fiber 6 μ ≤
          eLpNorm (Real.sqrt Cr • fun x => ∑ q ∈ K, |comp q x|) 6 μ := by
        refine _root_.MeasureTheory.eLpNorm_mono_real (fun x => ?_)
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        simpa only [Pi.smul_apply, smul_eq_mul] using hpoint x
      _ = ENNReal.ofReal (Real.sqrt Cr) *
          eLpNorm (fun x => ∑ q ∈ K, |comp q x|) 6 μ := by
        rw [_root_.MeasureTheory.eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
  have hsum_eLp :
      _root_.MeasureTheory.eLpNorm (fun x => ∑ q ∈ K, |comp q x|) 6 μ ≤
        ∑ q ∈ K, _root_.MeasureTheory.eLpNorm (fun x => |comp q x|) 6 μ := by
    have hfun : (fun x => ∑ q ∈ K, |comp q x|) =
        ∑ q ∈ K, fun x => |comp q x| := by
      funext x
      exact (Finset.sum_apply x K (fun q x => |comp q x|)).symm
    rw [hfun]
    exact _root_.MeasureTheory.eLpNorm_sum_le (fun q _ => hcomp_meas q) (by norm_num)
  have hcomponent_sum :
      ∑ q ∈ K, _root_.MeasureTheory.eLpNorm (fun x => |comp q x|) 6 μ ≤
        ENNReal.ofReal Csum * (‖S‖₊ : ℝ≥0∞) := by
    calc
      ∑ q ∈ K, _root_.MeasureTheory.eLpNorm (fun x => |comp q x|) 6 μ
          = ∑ q ∈ K, _root_.MeasureTheory.eLpNorm (comp q) 6 μ := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        simpa only [Real.norm_eq_abs] using (_root_.MeasureTheory.eLpNorm_norm (comp q))
      _ ≤ ∑ q ∈ K, ENNReal.ofReal (Ca q.1.1) * (‖S‖₊ : ℝ≥0∞) := by
        exact Finset.sum_le_sum (fun q _ => hcomp q.1.1 S q.1.2 q.2)
      _ = ENNReal.ofReal Csum * (‖S‖₊ : ℝ≥0∞) := by
        rw [← Finset.sum_mul]
        change (∑ q ∈ K, ENNReal.ofReal (Ca q.1.1)) * (‖S‖₊ : ℝ≥0∞) =
          ENNReal.ofReal (∑ q ∈ K, Ca q.1.1) * (‖S‖₊ : ℝ≥0∞)
        rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => hCa q.1.1)]
  have hENN : _root_.MeasureTheory.eLpNorm fiber 6 μ ≤
      ENNReal.ofReal (Real.sqrt Cr * Csum) * (‖S‖₊ : ℝ≥0∞) := by
    calc
      _root_.MeasureTheory.eLpNorm fiber 6 μ ≤ ENNReal.ofReal (Real.sqrt Cr) *
          eLpNorm (fun x => ∑ q ∈ K, |comp q x|) 6 μ := hfiber_eLp
      _ ≤ ENNReal.ofReal (Real.sqrt Cr) *
          (∑ q ∈ K, _root_.MeasureTheory.eLpNorm (fun x => |comp q x|) 6 μ) :=
        mul_le_mul_of_nonneg_left hsum_eLp (zero_le)
      _ ≤ ENNReal.ofReal (Real.sqrt Cr) *
          (ENNReal.ofReal Csum * (‖S‖₊ : ℝ≥0∞)) :=
        mul_le_mul_of_nonneg_left hcomponent_sum (zero_le)
      _ = ENNReal.ofReal (Real.sqrt Cr * Csum) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_assoc]
  have hfiber_cont : Continuous fiber := by
    apply Real.continuous_sqrt.comp
    have hinner := SmoothCcTensor.continuous_inner_self
      (I := I) (M := M) S.toCcTensor
    refine hinner.congr (fun x => ?_)
    rw [riemannianFiberNormSq_eq_tensorInnerPointwise
      (I := I) (M := M) g r s x (S.toCcTensor.toSection x),
      ← SmoothCcTensor.toFun_apply (I := I) (M := M) S.toCcTensor x]
  have hrhs_ne_top :
      ENNReal.ofReal (Real.sqrt Cr * Csum) * (‖S‖₊ : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  have hreal := ENNReal.toReal_mono hrhs_ne_top hENN
  rw [MeasureTheory.toReal_eLpNorm hfiber_cont.aestronglyMeasurable,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _)
      (Finset.sum_nonneg (fun q _ => hCa q.1.1))),
    ENNReal.coe_toReal, coe_nnnorm] at hreal
  simpa only [fiber, μ] using hreal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.h1_lp6_fiber_rs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.h1_lp6_fiber_rs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.h1_lp6_fiber_rs ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.h1_lp6_fiber_rs

end DifferentialGeometry.Analysis.Parabolic.TensorSpectral
