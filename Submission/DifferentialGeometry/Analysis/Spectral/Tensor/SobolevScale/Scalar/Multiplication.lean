import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.OperatorField.CompositionJets
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.Application

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section
noncomputable section

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open scoped _root_.ContDiff _root_.Manifold _root_.Topology _root_.BigOperators

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

theorem scalar_product_hs_bound (g : SmoothRiemannianMetric I M) (n : ℕ)
    (hn : Module.finrank ℝ E / 2 + 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S T : SmoothCcTensor g 0 0,
      ‖ccTensorToHs (I := I) (M := M) g 0 (n : ℝ)
        (ccOperatorFieldComp (I := I) (M := M) g 0 0 0 S T)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 0 (n : ℝ) S‖ *
          ‖ccTensorToHs (I := I) (M := M) g 0 (n : ℝ) T‖ := by
  obtain ⟨K, hK, hKle⟩ := operatorFieldComposition_jet_mul (I := I) (M := M) g 0 0 0
  obtain ⟨Cin, hCin, hCinle⟩ := hsJet_le (I := I) (M := M) g 0 n
  obtain ⟨Cout, hCout, hCoutle⟩ := hs_le_jet (I := I) (M := M) g 0 n
  refine ⟨Cout * (n + 1) * Real.sqrt (K n) * Cin ^ 2, by positivity, ?_⟩
  intro S T
  let N (U : SmoothCcTensor g 0 0) : ℝ := ‖ccTensorToHs (I := I) (M := M) g 0 (n : ℝ) U‖
  let J (U : SmoothCcTensor g 0 0) : ℝ :=
    ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g 0 0 j U‖ ^ 2
  have hJ (U : SmoothCcTensor g 0 0) : J U ≤ (Cin * N U) ^ 2 := by
    exact (Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => norm_nonneg _)) (hCinle U) 2)
  have hprod : J (ccOperatorFieldComp (I := I) (M := M) g 0 0 0 S T) ≤
      (Real.sqrt (K n) * Cin ^ 2 * N S * N T) ^ 2 := by
    calc
      J (ccOperatorFieldComp (I := I) (M := M) g 0 0 0 S T)
          ≤ K n * J S * J T := hKle n hn S T
      _ ≤ K n * (Cin * N S) ^ 2 * (Cin * N T) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hJ S) (hK n)) (hJ T)
          (Finset.sum_nonneg (fun j _ => sq_nonneg _))
          (mul_nonneg (hK n) (sq_nonneg _))
      _ = (Real.sqrt (K n) * Cin ^ 2 * N S * N T) ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt (hK n)]
        ring
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      ‖iteratedCovGrad (I := I) g 0 0 j
        (ccOperatorFieldComp (I := I) (M := M) g 0 0 0 S T)‖ ≤
        Real.sqrt (K n) * Cin ^ 2 * N S * N T := by
    apply (sq_le_sq₀ (norm_nonneg _) (by dsimp [N]; positivity)).mp
    exact (Finset.single_le_sum
      (f := fun k => ‖iteratedCovGrad (I := I) g 0 0 k
        (ccOperatorFieldComp (I := I) (M := M) g 0 0 0 S T)‖ ^ 2)
      (fun k _ => sq_nonneg _) hj).trans hprod
  have hsum : (∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g 0 0 j
        (ccOperatorFieldComp (I := I) (M := M) g 0 0 0 S T)‖) ≤
        (n + 1) * (Real.sqrt (K n) * Cin ^ 2 * N S * N T) := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one] using Finset.sum_le_sum hterm
  calc
    ‖ccTensorToHs (I := I) (M := M) g 0 (n : ℝ)
        (ccOperatorFieldComp (I := I) (M := M) g 0 0 0 S T)‖
        ≤ Cout * ∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g 0 0 j
            (ccOperatorFieldComp (I := I) (M := M) g 0 0 0 S T)‖ := hCoutle _
    _ ≤ Cout * ((n + 1) * (Real.sqrt (K n) * Cin ^ 2 * N S * N T)) :=
      mul_le_mul_of_nonneg_left hsum hCout
    _ = Cout * (n + 1) * Real.sqrt (K n) * Cin ^ 2 * N S * N T := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalar_product_hs_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalar_product_hs_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalar_product_hs_bound ``Submission.DifferentialGeometry.Analysis.Spectral.scalar_product_hs_bound

end DifferentialGeometry.Analysis.Spectral
end
end

section
noncomputable section

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.Integral.L2
open scoped _root_.ContDiff _root_.Manifold _root_.Topology

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

private def scalarCcMultiplication (g : SmoothRiemannianMetric I M) (n : ℕ) :
    SmoothCcTensor g 0 0 →ₗ[ℝ]
      (TensorHs (I := I) (M := M) g 0 0 (n : ℝ) →L[ℝ]
        TensorHs (I := I) (M := M) g 0 0 (n : ℝ)) where
  toFun := appHs (I := I) (M := M) g 0 0 n
  map_add' S T := by
    apply ContinuousLinearMap.ext
    intro u
    exact appHs_add (I := I) (M := M) g 0 0 n S T u
  map_smul' a S := by
    apply ContinuousLinearMap.ext
    intro u
    exact appHs_smul (I := I) (M := M) g 0 0 n a S u

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.scalarCcMultiplication
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.scalarCcMultiplication target :: scope.openDecls } }

private theorem scalarCcMultiplication_bound (g : SmoothRiemannianMetric I M) (n : ℕ)
    (hn : Module.finrank ℝ E / 2 + 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : SmoothCcTensor g 0 0,
      ‖scalarCcMultiplication (I := I) (M := M) g n S‖ ≤
        C * ‖ccToHsLin (I := I) (M := M) g 0 (n : ℝ) S‖ := by
  obtain ⟨C, hC, hprod⟩ := scalar_product_hs_bound (I := I) (M := M) g n hn
  refine ⟨C, hC, fun S => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro u
  refine (ccToHsLin_dense (I := I) (M := M) g 0 (by positivity : (0 : ℝ) ≤ n)).induction_on u
    (isClosed_le (Continuous.norm (scalarCcMultiplication (I := I) (M := M) g n S).continuous)
      (continuous_const.mul continuous_norm)) ?_
  intro T
  change ‖appHs (I := I) (M := M) g 0 0 n S (ccTensorToHs (I := I) (M := M) g 0 (n : ℝ) T)‖ ≤ _
  rw [appHs_apply_ccTensorToHs,
    ← operatorFieldComposition_zero_eq_operatorFieldApply]
  exact hprod S T

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.scalarCcMultiplication_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.scalarCcMultiplication_bound target :: scope.openDecls } }

private theorem exists_scalarHsMul (g : SmoothRiemannianMetric I M) (n : ℕ)
    (hn : Module.finrank ℝ E / 2 + 1 ≤ n) :
    ∃ m : TensorHs (I := I) (M := M) g 0 0 (n : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 0 (n : ℝ) →L[ℝ]
        TensorHs (I := I) (M := M) g 0 0 (n : ℝ),
      ∀ S : SmoothCcTensor g 0 0,
        m (ccTensorToHs (I := I) (M := M) g 0 (n : ℝ) S) =
          appHs (I := I) (M := M) g 0 0 n S := by
  refine ⟨(scalarCcMultiplication (I := I) (M := M) g n).extendOfNorm
    (ccToHsLin (I := I) (M := M) g 0 (n : ℝ)), fun S => ?_⟩
  obtain ⟨C, _, hC⟩ := scalarCcMultiplication_bound (I := I) (M := M) g n hn
  exact LinearMap.extendOfNorm_eq
    (ccToHsLin_dense (I := I) (M := M) g 0 (by positivity : (0 : ℝ) ≤ n)) ⟨C, hC⟩ S

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.exists_scalarHsMul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.exists_scalarHsMul target :: scope.openDecls } }

def scalarHsMul (g : SmoothRiemannianMetric I M) (n : ℕ)
    (hn : Module.finrank ℝ E / 2 + 1 ≤ n) :
    TensorHs (I := I) (M := M) g 0 0 (n : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 0 (n : ℝ) →L[ℝ]
        TensorHs (I := I) (M := M) g 0 0 (n : ℝ) :=
  (exists_scalarHsMul (I := I) (M := M) g n hn).choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarHsMul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarHsMul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarHsMul ``Submission.DifferentialGeometry.Analysis.Spectral.scalarHsMul

theorem scalarHsMul_apply_ccTensorToHs_left (g : SmoothRiemannianMetric I M) (n : ℕ)
    (hn : Module.finrank ℝ E / 2 + 1 ≤ n) (S : SmoothCcTensor g 0 0) :
    scalarHsMul (I := I) (M := M) g n hn
      (ccTensorToHs (I := I) (M := M) g 0 (n : ℝ) S) =
        appHs (I := I) (M := M) g 0 0 n S :=
  (exists_scalarHsMul (I := I) (M := M) g n hn).choose_spec S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarHsMul_apply_ccTensorToHs_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarHsMul_apply_ccTensorToHs_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarHsMul_apply_ccTensorToHs_left ``Submission.DifferentialGeometry.Analysis.Spectral.scalarHsMul_apply_ccTensorToHs_left

theorem scalarHsMul_apply_ccTensorToHs (g : SmoothRiemannianMetric I M) (n : ℕ)
    (hn : Module.finrank ℝ E / 2 + 1 ≤ n) (S T : SmoothCcTensor g 0 0) :
    scalarHsMul (I := I) (M := M) g n hn
      (ccTensorToHs (I := I) (M := M) g 0 (n : ℝ) S)
      (ccTensorToHs (I := I) (M := M) g 0 (n : ℝ) T) =
        ccTensorToHs (I := I) (M := M) g 0 (n : ℝ)
          (ccOperatorFieldComp (I := I) (M := M) g 0 0 0 S T) := by
  rw [scalarHsMul_apply_ccTensorToHs_left, appHs_apply_ccTensorToHs,
    operatorFieldComposition_zero_eq_operatorFieldApply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarHsMul_apply_ccTensorToHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarHsMul_apply_ccTensorToHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarHsMul_apply_ccTensorToHs ``Submission.DifferentialGeometry.Analysis.Spectral.scalarHsMul_apply_ccTensorToHs

end DifferentialGeometry.Analysis.Spectral
end
end
