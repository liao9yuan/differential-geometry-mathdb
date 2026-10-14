import Submission.DifferentialGeometry.Analysis.Integration.Integral.DistanceCutoff
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Gradient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal _root_.Topology
namespace DifferentialGeometry.Analysis
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Geometry.Riemannian
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [OpensMeasurableSpace M] [SecondCountableTopology M]
  {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]

private theorem measurable_mul_grad_distance_cutoff
    (g : SmoothRiemannianMetric I M) (h : P → SmoothRiemannianMetric I M)
    (hh : Continuous (fun z : P × M =>
      (⟨z.2, (h z.1).inner z.2⟩ : _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))))
    {u : P → M → ℝ} (hu : Continuous u.uncurry)
    {v : P × M → ℝ} (hv : Measurable v) (o : M) (a : ℝ≥0) :
    Measurable (fun z : P × M => (h z.1).inner z.2
      (v z • gradFun (h z.1) (u z.1) z.2)
      (gradFun (h z.1) (fun y => CutoffProfile.evalue
        ((a : ℝ≥0∞) * riemannianEDistOf g o y)) z.2)) := by
  have hc : Continuous (fun z : P × M => CutoffProfile.evalue
      ((a : ℝ≥0∞) * riemannianEDistOf g o z.2)) :=
    CutoffProfile.continuous_evalue.comp
      ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
        ((continuous_riemannianEDist g o).comp continuous_snd))
  have hg := measurable_inner_gradFun_with_param h hh (f := u)
    (h := fun _ y => CutoffProfile.evalue ((a : ℝ≥0∞) * riemannianEDistOf g o y)) hu hc
  have heq : (fun z : P × M => (h z.1).inner z.2
      (v z • gradFun (h z.1) (u z.1) z.2)
      (gradFun (h z.1) (fun y => CutoffProfile.evalue
        ((a : ℝ≥0∞) * riemannianEDistOf g o y)) z.2)) =
      (fun z : P × M => v z * (h z.1).inner z.2
        (gradFun (h z.1) (u z.1) z.2)
        (gradFun (h z.1) (fun y => CutoffProfile.evalue
          ((a : ℝ≥0∞) * riemannianEDistOf g o y)) z.2)) := by
    funext z
    simp only [ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
  rw [heq]
  exact hv.mul hg

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.measurable_mul_grad_distance_cutoff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.measurable_mul_grad_distance_cutoff target :: scope.openDecls } }

theorem integrable_mul_inner_grad_distance_cutoff
    (μ : _root_.MeasureTheory.Measure (P × M)) (a : ℝ≥0)
    (g : SmoothRiemannianMetric I M) (h : P → SmoothRiemannianMetric I M)
    (hh : Continuous (fun z : P × M =>
      (⟨z.2, (h z.1).inner z.2⟩ : _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))))
    (hgh : ∀ᵐ z ∂μ, ∀ x v, g.inner x v v ≤ (h z.1).inner x v v)
    {u : P → M → ℝ} (hu : Continuous u.uncurry) (hu0 : ∀ᵐ z ∂μ, 0 ≤ u z.1 z.2)
    {v : P × M → ℝ} (hv : Measurable v)
    (hw : _root_.MeasureTheory.Integrable (fun z => |v z| * u z.1 z.2) μ)
    (o : M) (C : ℝ≥0)
    (hgrad : ∀ᵐ z ∂μ, Real.sqrt ((h z.1).inner z.2
      (gradFun (h z.1) (u z.1) z.2) (gradFun (h z.1) (u z.1) z.2)) ≤
        C * (1 + (riemannianEDistOf g o z.2).toReal) * u z.1 z.2) :
    _root_.MeasureTheory.Integrable (fun z : P × M => v z * (h z.1).inner z.2
      (gradFun (h z.1) (u z.1) z.2)
      (gradFun (h z.1) (fun y => CutoffProfile.evalue
        ((a : ℝ≥0∞) * riemannianEDistOf g o y)) z.2)) μ := by
  let V : ∀ z : P × M, TangentSpace I z.2 := fun z => v z • gradFun (h z.1) (u z.1) z.2
  have hV : ∀ᵐ z ∂μ, Real.sqrt ((h z.1).inner z.2 (V z) (V z)) ≤
      C * (1 + (riemannianEDistOf g o z.2).toReal) * (|v z| * u z.1 z.2) := by
    filter_upwards [hgrad] with z hz
    rw [sqrt_inner_smul]
    calc
      _ ≤ |v z| * (C * (1 + (riemannianEDistOf g o z.2).toReal) * u z.1 z.2) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = _ := by ring
  have hi := integrable_inner_grad_distance_cutoff μ a g (fun z => h z.1) hgh o Prod.snd V C hw
    (hu0.mono fun z hz => mul_nonneg (abs_nonneg _) hz) hV
    (measurable_mul_grad_distance_cutoff g h hh hu hv o a).aestronglyMeasurable
  simpa only [V, ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul] using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integrable_mul_inner_grad_distance_cutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integrable_mul_inner_grad_distance_cutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integrable_mul_inner_grad_distance_cutoff ``Submission.DifferentialGeometry.Analysis.integrable_mul_inner_grad_distance_cutoff

theorem tendsto_integral_abs_mul_inner_grad_distance_cutoff
    (μ : _root_.MeasureTheory.Measure (P × M)) {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a : ι → ℝ≥0) (ha : _root_.Filter.Tendsto a l (𝓝 0))
    (g : SmoothRiemannianMetric I M) (h : P → SmoothRiemannianMetric I M)
    (hh : Continuous (fun z : P × M =>
      (⟨z.2, (h z.1).inner z.2⟩ : _root_.Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))))
    (hgh : ∀ᵐ z ∂μ, ∀ x v, g.inner x v v ≤ (h z.1).inner x v v)
    {u : P → M → ℝ} (hu : Continuous u.uncurry) (hu0 : ∀ᵐ z ∂μ, 0 ≤ u z.1 z.2)
    {v : P × M → ℝ} (hv : Measurable v)
    (hw : _root_.MeasureTheory.Integrable (fun z => |v z| * u z.1 z.2) μ)
    (o : M) (C : ℝ≥0)
    (hgrad : ∀ᵐ z ∂μ, Real.sqrt ((h z.1).inner z.2
      (gradFun (h z.1) (u z.1) z.2) (gradFun (h z.1) (u z.1) z.2)) ≤
        C * (1 + (riemannianEDistOf g o z.2).toReal) * u z.1 z.2) :
    _root_.Filter.Tendsto (fun i => ∫ z : P × M, |v z * (h z.1).inner z.2
      (gradFun (h z.1) (u z.1) z.2)
      (gradFun (h z.1) (fun y => CutoffProfile.evalue
        ((a i : ℝ≥0∞) * riemannianEDistOf g o y)) z.2)| ∂μ) l (𝓝 0) := by
  let V : ∀ z : P × M, TangentSpace I z.2 := fun z => v z • gradFun (h z.1) (u z.1) z.2
  have hV : ∀ᵐ z ∂μ, Real.sqrt ((h z.1).inner z.2 (V z) (V z)) ≤
      C * (1 + (riemannianEDistOf g o z.2).toReal) * (|v z| * u z.1 z.2) := by
    filter_upwards [hgrad] with z hz
    rw [sqrt_inner_smul]
    calc
      _ ≤ |v z| * (C * (1 + (riemannianEDistOf g o z.2).toReal) * u z.1 z.2) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = _ := by ring
  have ht := tendsto_integral_abs_inner_grad_distance_cutoff μ a ha g (fun z => h z.1)
    hgh o Prod.snd V C hw (hu0.mono fun z hz => mul_nonneg (abs_nonneg _) hz) hV
    (Eventually.of_forall fun i =>
      (measurable_mul_grad_distance_cutoff g h hh hu hv o (a i)).aestronglyMeasurable)
  simpa only [V, ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul] using ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.tendsto_integral_abs_mul_inner_grad_distance_cutoff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.tendsto_integral_abs_mul_inner_grad_distance_cutoff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.tendsto_integral_abs_mul_inner_grad_distance_cutoff ``Submission.DifferentialGeometry.Analysis.tendsto_integral_abs_mul_inner_grad_distance_cutoff

end DifferentialGeometry.Analysis
