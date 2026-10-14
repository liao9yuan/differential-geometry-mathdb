import Submission.DifferentialGeometry.Analysis.Sobolev.MoserTameProduct
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.FiberNorm.FrameSum
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Bridge.Cross
import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.FiberNorm.SliceBound
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.GradientField
import Submission.DifferentialGeometry.Geometry.Curvature.RoughLaplacian.Commutator.HomFieldJetDecomposition
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Identities.TensorThirdOrder
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Variational.CovDerivPointwise
import Submission.DifferentialGeometry.Bundle.Section
import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.CovariantTensor.Mixed

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology
open scoped _root_.ENNReal _root_.NNReal _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Tensor

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Tensor.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Tensor.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Tensor.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Tensor.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Tensor.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

section SecondOrderInterpInfra


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] in
theorem continuous_riemannianFiberNormSq_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Integral.L2.SmoothCcTensor g r s) :
    Continuous (fun x => riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) := by
  have hc := Integral.L2.SmoothCcTensor.continuous_inner_self (I := I) (M := M) S
  refine hc.congr (fun x => ?_)
  rw [riemannianFiberNormSq_eq_tensorInnerPointwise (I := I) (M := M) g r s x (S.toSection x),
    ← Integral.L2.SmoothCcTensor.toFun_apply (I := I) (M := M) S x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.continuous_riemannianFiberNormSq_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.continuous_riemannianFiberNormSq_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.continuous_riemannianFiberNormSq_section ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.continuous_riemannianFiberNormSq_section


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [I.Boundaryless] in
private theorem memLp_riemannianFiberNormSq_rpow
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : Integral.L2.SmoothCcTensor g r s) (a : ℝ) (ha : 0 ≤ a) (p : ℝ≥0∞) :
    MeasureTheory.MemLp
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) ^ a) p
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) := by
  have : MeasureTheory.IsFiniteMeasure
    (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hcont : Continuous
      (fun x => (riemannianFiberNormSq (I := I) (M := M) g r s x (S.toSection x)) ^ a) :=
    (continuous_riemannianFiberNormSq_section (I := I) (M := M) g r s S).rpow_const
      (fun _ => Or.inr ha)
  exact hcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.memLp_riemannianFiberNormSq_rpow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Tensor.memLp_riemannianFiberNormSq_rpow target :: scope.openDecls } }


omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [I.Boundaryless] in
theorem real_holder_three_nonneg
    (g : SmoothRiemannianMetric I M) (f₁ f₂ f₃ : M → ℝ)
    (hf₁c : Continuous f₁) (hf₂c : Continuous f₂) (hf₃c : Continuous f₃)
    (hf₁0 : ∀ x, 0 ≤ f₁ x) (hf₂0 : ∀ x, 0 ≤ f₂ x) (hf₃0 : ∀ x, 0 ≤ f₃ x)
    {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hABC : α⁻¹ + β⁻¹ + γ⁻¹ = 1) :
    ∫ x, f₁ x * f₂ x * f₃ x ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g) ≤
      (∫ x, f₁ x ^ α ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g)) ^
        (1 / α) *
        ((∫ x, f₂ x ^ β ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g))
          ^ (1 / β) *
          (∫ x, f₃ x ^ γ ∂(DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g))
            ^ (1 / γ)) := by
  classical
  set μ : MeasureTheory.Measure M :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I M g with hμ
  have : MeasureTheory.IsFiniteMeasure μ :=
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set α' : ℝ := (β⁻¹ + γ⁻¹)⁻¹ with hα'def
  have hβγpos : 0 < β⁻¹ + γ⁻¹ := by positivity
  have hα'pos : 0 < α' := by rw [hα'def]; positivity
  have hα'inv : α'⁻¹ = β⁻¹ + γ⁻¹ := by rw [hα'def, inv_inv]
  have hγinv_pos : (0 : ℝ) < γ⁻¹ := by positivity
  have hβinv_pos : (0 : ℝ) < β⁻¹ := by positivity
  have hconj1 : α.HolderConjugate α' := by
    refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
    · have hαinv_lt : α⁻¹ < 1 := by
        have hαeq : α⁻¹ = 1 - (β⁻¹ + γ⁻¹) := by linarith [hABC]
        rw [hαeq]; linarith [hβγpos]
      have hαinv_pos : (0 : ℝ) < α⁻¹ := by positivity
      rw [← inv_inv α]
      exact one_lt_inv_iff₀.mpr ⟨hαinv_pos, hαinv_lt⟩
    · rw [hα'inv]; linarith [hABC]
  have hf23_0 : ∀ x, 0 ≤ f₂ x * f₃ x := fun x => mul_nonneg (hf₂0 x) (hf₃0 x)
  have hf1_mem : MeasureTheory.MemLp f₁ (ENNReal.ofReal α) μ :=
    hf₁c.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf23_mem : MeasureTheory.MemLp (fun x => f₂ x * f₃ x) (ENNReal.ofReal α') μ :=
    (hf₂c.mul hf₃c).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hstep1 := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj1
    (f := f₁) (g := fun x => f₂ x * f₃ x)
    (MeasureTheory.ae_of_all _ hf₁0) (MeasureTheory.ae_of_all _ hf23_0) hf1_mem hf23_mem
  have hβα' : 0 < β / α' := by positivity
  have hγα' : 0 < γ / α' := by positivity
  have hf2α'_mem : MeasureTheory.MemLp (fun x => f₂ x ^ α') (ENNReal.ofReal (β / α')) μ :=
    ((hf₂c.rpow_const (fun _ => Or.inr hα'pos.le)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hf3α'_mem : MeasureTheory.MemLp (fun x => f₃ x ^ α') (ENNReal.ofReal (γ / α')) μ :=
    ((hf₃c.rpow_const (fun _ => Or.inr hα'pos.le)).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
  have hα'ne : α' ≠ 0 := ne_of_gt hα'pos
  have hconj2 : (β / α').HolderConjugate (γ / α') := by
    refine Real.holderConjugate_iff.mpr ⟨?_, ?_⟩
    · rw [one_lt_div hα'pos]
      have hlt : β⁻¹ < α'⁻¹ := by rw [hα'inv]; linarith [hγinv_pos]
      exact (inv_lt_inv₀ hβ hα'pos).mp hlt
    · have hsplit : α' / β + α' / γ = α' * (β⁻¹ + γ⁻¹) := by
        rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_add]
      rw [inv_div, inv_div, hsplit, ← hα'inv, mul_inv_cancel₀ hα'ne]
  have hstep2 := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hconj2
    (f := fun x => f₂ x ^ α') (g := fun x => f₃ x ^ α')
    (MeasureTheory.ae_of_all _ (fun x => Real.rpow_nonneg (hf₂0 x) _))
    (MeasureTheory.ae_of_all _ (fun x => Real.rpow_nonneg (hf₃0 x) _)) hf2α'_mem hf3α'_mem
  have hprod_rpow : ∀ x, (f₂ x * f₃ x) ^ α' = f₂ x ^ α' * f₃ x ^ α' :=
    fun x => Real.mul_rpow (hf₂0 x) (hf₃0 x)
  have hmulcancel : ∀ t : ℝ, α' * (t / α') = t := by
    intro t; rw [mul_comm, div_mul_cancel₀ t hα'ne]
  have hpow2 : ∀ x, (f₂ x ^ α') ^ (β / α') = f₂ x ^ β := by
    intro x
    rw [← Real.rpow_mul (hf₂0 x), hmulcancel]
  have hpow3 : ∀ x, (f₃ x ^ α') ^ (γ / α') = f₃ x ^ γ := by
    intro x
    rw [← Real.rpow_mul (hf₃0 x), hmulcancel]
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpow2),
      MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hpow3)] at hstep2
  set Iβ : ℝ := ∫ x, f₂ x ^ β ∂μ with hIβ
  set Iγ : ℝ := ∫ x, f₃ x ^ γ ∂μ with hIγ
  have hIβ_nn : 0 ≤ Iβ := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hf₂0 x) _)
  have hIγ_nn : 0 ≤ Iγ := MeasureTheory.integral_nonneg (fun x => Real.rpow_nonneg (hf₃0 x) _)
  have hI23 : (∫ x, (f₂ x * f₃ x) ^ α' ∂μ) = ∫ x, f₂ x ^ α' * f₃ x ^ α' ∂μ :=
    MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hprod_rpow)
  have hmid : (∫ x, (f₂ x * f₃ x) ^ α' ∂μ) ^ (1 / α') ≤ Iβ ^ (1 / β) * Iγ ^ (1 / γ) := by
    rw [hI23]
    have hbase_nn : 0 ≤ ∫ x, f₂ x ^ α' * f₃ x ^ α' ∂μ :=
      MeasureTheory.integral_nonneg (fun x =>
        mul_nonneg (Real.rpow_nonneg (hf₂0 x) _) (Real.rpow_nonneg (hf₃0 x) _))
    have hα'inv_pos : 0 < 1 / α' := by positivity
    calc (∫ x, f₂ x ^ α' * f₃ x ^ α' ∂μ) ^ (1 / α')
        ≤ (Iβ ^ (1 / (β / α')) * Iγ ^ (1 / (γ / α'))) ^ (1 / α') :=
          Real.rpow_le_rpow hbase_nn hstep2 (le_of_lt hα'inv_pos)
      _ = Iβ ^ (1 / β) * Iγ ^ (1 / γ) := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_mul hIβ_nn, ← Real.rpow_mul hIγ_nn]
          have he2 : (1 / (β / α')) * (1 / α') = 1 / β := by
            rw [one_div_div]
            field_simp
          have he3 : (1 / (γ / α')) * (1 / α') = 1 / γ := by
            rw [one_div_div]
            field_simp
          rw [he2, he3]
  calc ∫ x, f₁ x * f₂ x * f₃ x ∂μ
      = ∫ x, f₁ x * (f₂ x * f₃ x) ∂μ := by
        refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ (fun x => ?_))
        ring
    _ ≤ (∫ x, f₁ x ^ α ∂μ) ^ (1 / α) * (∫ x, (f₂ x * f₃ x) ^ α' ∂μ) ^ (1 / α') := hstep1
    _ ≤ (∫ x, f₁ x ^ α ∂μ) ^ (1 / α) * (Iβ ^ (1 / β) * Iγ ^ (1 / γ)) := by
        apply mul_le_mul_of_nonneg_left hmid
        exact Real.rpow_nonneg (MeasureTheory.integral_nonneg
          (fun x => Real.rpow_nonneg (hf₁0 x) _)) _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Tensor.real_holder_three_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Tensor.real_holder_three_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Tensor.real_holder_three_nonneg ``Submission.DifferentialGeometry.Analysis.Sobolev.Tensor.real_holder_three_nonneg

end SecondOrderInterpInfra

end DifferentialGeometry.Analysis.Sobolev.Tensor

end
