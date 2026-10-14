import Submission.DifferentialGeometry.Analysis.Integration.L2.Pairing.Algebra

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Integral
namespace L2

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Integral.L2.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }


theorem tensorL2Inner_sq_le_mul
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E)
    (hSS : MemL2 (I := I) (M := M) g r s S)
    (hTT : MemL2 (I := I) (M := M) g r s T)
    (hST : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    (tensorL2Inner (I := I) (M := M) g r s S T) ^ 2 ≤
      tensorL2Inner (I := I) (M := M) g r s S S *
        tensorL2Inner (I := I) (M := M) g r s T T := by
  set a := tensorL2Inner (I := I) (M := M) g r s S S with ha_def
  set b := tensorL2Inner (I := I) (M := M) g r s S T with hb_def
  set c := tensorL2Inner (I := I) (M := M) g r s T T with hc_def
  have ha_nn : 0 ≤ a := tensorL2Inner_nonneg (I := I) (M := M) g r s S
  have hc_nn : 0 ≤ c := tensorL2Inner_nonneg (I := I) (M := M) g r s T
  have hquad : ∀ t : ℝ, 0 ≤ a + 2 * (t * b) + t ^ 2 * c := by
    intro t
    have hpoint : ∀ x : M,
        tensorInnerPointwise (I := I) (M := M) g r s x
            ((S + t • T) x) ((S + t • T) x) =
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
            2 * (t *
              tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)) +
            t ^ 2 *
              tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x) := by
      intro x
      have hsymm := tensorInnerPointwise_symm (I := I) (M := M) g r s x (T x) (S x)
      change tensorInnerPointwise (I := I) (M := M) g r s x (S x + t • T x) (S x + t • T x) =
        _
      rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
          tensorInnerPointwise_add_right, tensorInnerPointwise_smul_left,
          tensorInnerPointwise_smul_right, tensorInnerPointwise_smul_left,
          tensorInnerPointwise_smul_right]
      rw [hsymm]
      ring
    have h_nn_point : ∀ x : M,
        0 ≤ tensorInnerPointwise (I := I) (M := M) g r s x
            ((S + t • T) x) ((S + t • T) x) := fun x =>
      tensorInnerPointwise_nonneg (I := I) (M := M) g r s x ((S + t • T) x)
    have h_cross_const_mul : MeasureTheory.Integrable
        (fun x => 2 * (t *
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)))
        (riemannianVolumeMeasure (I := I) (M := M) g) := by
      have : MeasureTheory.Integrable
          (fun x => t *
            tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
          (riemannianVolumeMeasure (I := I) (M := M) g) := hST.const_mul t
      exact this.const_mul 2
    have h_diag_T : MeasureTheory.Integrable
        (fun x => t ^ 2 *
          tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      hTT.integrable_inner_self.const_mul (t ^ 2)
    have h_int_eq :
        ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x
            ((S + t • T) x) ((S + t • T) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
          a + 2 * (t * b) + t ^ 2 * c := by
      have hcongr :
          (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
              ((S + t • T) x) ((S + t • T) x)) =
            (fun x =>
              tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
                2 * (t *
                  tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)) +
                t ^ 2 *
                  tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x)) :=
        funext hpoint
      rw [hcongr]
      have hadd_outer :=
        MeasureTheory.integral_add
          (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          (f := fun x =>
            tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
              2 * (t * tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)))
          (g := fun x =>
            t ^ 2 * tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x))
          (hSS.integrable_inner_self.add h_cross_const_mul) h_diag_T
      rw [hadd_outer]
      have hadd_mid :=
        MeasureTheory.integral_add
          (μ := riemannianVolumeMeasure (I := I) (M := M) g)
          (f := fun x =>
            tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x))
          (g := fun x =>
            2 * (t * tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)))
          hSS.integrable_inner_self h_cross_const_mul
      rw [hadd_mid]
      have hb_const :
          ∫ x, 2 * (t *
              tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
            2 * (t *
              ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      have hc_const :
          ∫ x, t ^ 2 *
              tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
            t ^ 2 *
              ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
        MeasureTheory.integral_const_mul (t ^ 2) _
      rw [hb_const, hc_const]
      change _ = tensorL2Inner (I := I) (M := M) g r s S S +
        2 * (t * tensorL2Inner (I := I) (M := M) g r s S T) +
        t ^ 2 * tensorL2Inner (I := I) (M := M) g r s T T
      unfold tensorL2Inner
      rfl
    have h_int_nn :
        0 ≤ ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x
            ((S + t • T) x) ((S + t • T) x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      MeasureTheory.integral_nonneg (fun x => h_nn_point x)
    rw [h_int_eq] at h_int_nn
    exact h_int_nn
  rcases (lt_or_eq_of_le hc_nn) with hc_pos | hc_zero
  · have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    have h := hquad (-b / c)
    have hsimp : a + 2 * (-b / c * b) + (-b / c) ^ 2 * c = a - b ^ 2 / c := by
      field_simp
      ring
    rw [hsimp] at h
    have hmul : 0 * c ≤ (a - b ^ 2 / c) * c :=
      mul_le_mul_of_nonneg_right h (le_of_lt hc_pos)
    rw [_root_.MulZeroClass.zero_mul] at hmul
    have hrhs : (a - b ^ 2 / c) * c = a * c - b ^ 2 := by
      field_simp
    rw [hrhs] at hmul
    linarith
  · have hc_eq : c = 0 := hc_zero.symm
    have hquad' : ∀ t : ℝ, 0 ≤ a + 2 * (t * b) := by
      intro t
      have h := hquad t
      rw [hc_eq, _root_.MulZeroClass.mul_zero, add_zero] at h
      exact h
    have hb_zero : b = 0 := by
      by_contra hbne
      rcases lt_or_gt_of_ne hbne with hb_neg | hb_pos
      · have hneg2b : -(2 * b) > 0 := by linarith
        set t₀ := (a + 1) / (-(2 * b)) with ht₀_def
        have ht₀_eq : 2 * (t₀ * b) = -(a + 1) := by
          rw [ht₀_def]
          field_simp
        have h := hquad' t₀
        rw [ht₀_eq] at h
        linarith
      · have h2b : 2 * b > 0 := by linarith
        set t₀ := -(a + 1) / (2 * b) with ht₀_def
        have ht₀_eq : 2 * (t₀ * b) = -(a + 1) := by
          rw [ht₀_def]
          field_simp
        have h := hquad' t₀
        rw [ht₀_eq] at h
        linarith
    rw [hb_zero, hc_eq, _root_.MulZeroClass.mul_zero]
    simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorL2Inner_sq_le_mul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorL2Inner_sq_le_mul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorL2Inner_sq_le_mul ``Submission.DifferentialGeometry.Integral.L2.tensorL2Inner_sq_le_mul


theorem abs_tensorL2Inner_le
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E)
    (hSS : MemL2 (I := I) (M := M) g r s S)
    (hTT : MemL2 (I := I) (M := M) g r s T)
    (hST : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    |tensorL2Inner (I := I) (M := M) g r s S T| ≤
      tensorL2Norm (I := I) (M := M) g r s S *
        tensorL2Norm (I := I) (M := M) g r s T := by
  unfold tensorL2Norm
  have hSS_nn : 0 ≤ tensorL2Inner (I := I) (M := M) g r s S S :=
    tensorL2Inner_nonneg (I := I) (M := M) g r s S
  have hTT_nn : 0 ≤ tensorL2Inner (I := I) (M := M) g r s T T :=
    tensorL2Inner_nonneg (I := I) (M := M) g r s T
  have hcs := tensorL2Inner_sq_le_mul (I := I) (M := M) g r s S T hSS hTT hST
  have habs_sq :
      |tensorL2Inner (I := I) (M := M) g r s S T| =
        Real.sqrt
          ((tensorL2Inner (I := I) (M := M) g r s S T) ^ 2) :=
    (Real.sqrt_sq_eq_abs _).symm
  rw [habs_sq]
  have h1 : Real.sqrt ((tensorL2Inner (I := I) (M := M) g r s S T) ^ 2) ≤
      Real.sqrt (tensorL2Inner (I := I) (M := M) g r s S S *
        tensorL2Inner (I := I) (M := M) g r s T T) :=
    Real.sqrt_le_sqrt hcs
  have h2 : Real.sqrt (tensorL2Inner (I := I) (M := M) g r s S S *
      tensorL2Inner (I := I) (M := M) g r s T T) =
      Real.sqrt (tensorL2Inner (I := I) (M := M) g r s S S) *
        Real.sqrt (tensorL2Inner (I := I) (M := M) g r s T T) :=
    Real.sqrt_mul hSS_nn _
  rw [h2] at h1
  exact h1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.abs_tensorL2Inner_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.abs_tensorL2Inner_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.abs_tensorL2Inner_le ``Submission.DifferentialGeometry.Integral.L2.abs_tensorL2Inner_le


theorem tensorL2Norm_add_le
    [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : M → TensorRSModel r s ℝ E)
    (hS : MemL2 (I := I) (M := M) g r s S)
    (hT : MemL2 (I := I) (M := M) g r s T)
    (hST : MeasureTheory.Integrable (fun x =>
      tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
      (riemannianVolumeMeasure (I := I) (M := M) g)) :
    tensorL2Norm (I := I) (M := M) g r s (S + T) ≤
      tensorL2Norm (I := I) (M := M) g r s S +
        tensorL2Norm (I := I) (M := M) g r s T := by
  set a := tensorL2Inner (I := I) (M := M) g r s S S with ha_def
  set b := tensorL2Inner (I := I) (M := M) g r s S T with hb_def
  set c := tensorL2Inner (I := I) (M := M) g r s T T with hc_def
  have ha_nn : 0 ≤ a := tensorL2Inner_nonneg (I := I) (M := M) g r s S
  have hc_nn : 0 ≤ c := tensorL2Inner_nonneg (I := I) (M := M) g r s T
  have hA_nn : 0 ≤ Real.sqrt a := Real.sqrt_nonneg _
  have hC_nn : 0 ≤ Real.sqrt c := Real.sqrt_nonneg _
  have h_sumSq :
      tensorL2Inner (I := I) (M := M) g r s (S + T) (S + T) =
        a + 2 * b + c := by
    have hpoint : ∀ x : M,
        tensorInnerPointwise (I := I) (M := M) g r s x
            ((S + T) x) ((S + T) x) =
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
            (tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
              tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)) +
            tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x) := by
      intro x
      have hsymm := tensorInnerPointwise_symm (I := I) (M := M) g r s x (T x) (S x)
      change tensorInnerPointwise (I := I) (M := M) g r s x (S x + T x) (S x + T x) =
        _
      rw [tensorInnerPointwise_add_left, tensorInnerPointwise_add_right,
          tensorInnerPointwise_add_right, hsymm]
      ring
    have h_two_cross : MeasureTheory.Integrable
        (fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
            tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
        (riemannianVolumeMeasure (I := I) (M := M) g) :=
      hST.add hST
    unfold tensorL2Inner
    have hcongr :
        (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
            ((S + T) x) ((S + T) x)) =
          (fun x =>
            tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
              (tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
                tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)) +
              tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x)) :=
      funext hpoint
    rw [hcongr]
    have hadd_outer :=
      MeasureTheory.integral_add
        (μ := riemannianVolumeMeasure (I := I) (M := M) g)
        (f := fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x) +
            (tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
              tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x)))
        (g := fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (T x) (T x))
        (hS.integrable_inner_self.add h_two_cross)
        hT.integrable_inner_self
    rw [hadd_outer]
    have hadd_mid :=
      MeasureTheory.integral_add
        (μ := riemannianVolumeMeasure (I := I) (M := M) g)
        (f := fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (S x))
        (g := fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x) +
            tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
        hS.integrable_inner_self h_two_cross
    rw [hadd_mid]
    have hadd_inner :=
      MeasureTheory.integral_add
        (μ := riemannianVolumeMeasure (I := I) (M := M) g)
        (f := fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
        (g := fun x =>
          tensorInnerPointwise (I := I) (M := M) g r s x (S x) (T x))
        hST hST
    rw [hadd_inner]
    change _ = tensorL2Inner (I := I) (M := M) g r s S S +
        2 * tensorL2Inner (I := I) (M := M) g r s S T +
        tensorL2Inner (I := I) (M := M) g r s T T
    unfold tensorL2Inner
    ring
  have h_abs_le : |b| ≤ Real.sqrt a * Real.sqrt c := by
    have habs := abs_tensorL2Inner_le (I := I) (M := M) g r s S T hS hT hST
    have hSnorm : tensorL2Norm (I := I) (M := M) g r s S = Real.sqrt a := rfl
    have hTnorm : tensorL2Norm (I := I) (M := M) g r s T = Real.sqrt c := rfl
    rw [hSnorm, hTnorm] at habs
    exact habs
  have h_b_le : b ≤ Real.sqrt a * Real.sqrt c :=
    le_of_abs_le h_abs_le
  have h_sumSq_le : a + 2 * b + c ≤ (Real.sqrt a + Real.sqrt c) ^ 2 := by
    have hsq_a : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha_nn
    have hsq_c : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc_nn
    nlinarith [h_b_le, hA_nn, hC_nn, hsq_a, hsq_c]
  unfold tensorL2Norm
  rw [h_sumSq]
  have hAC_nn : 0 ≤ Real.sqrt a + Real.sqrt c := add_nonneg hA_nn hC_nn
  have hSqAC : Real.sqrt ((Real.sqrt a + Real.sqrt c) ^ 2) =
      Real.sqrt a + Real.sqrt c :=
    Real.sqrt_sq hAC_nn
  calc Real.sqrt (a + 2 * b + c)
      ≤ Real.sqrt ((Real.sqrt a + Real.sqrt c) ^ 2) :=
        Real.sqrt_le_sqrt h_sumSq_le
    _ = Real.sqrt a + Real.sqrt c := hSqAC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.L2.tensorL2Norm_add_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.L2.tensorL2Norm_add_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.L2.tensorL2Norm_add_le ``Submission.DifferentialGeometry.Integral.L2.tensorL2Norm_add_le

end L2
end Integral
end DifferentialGeometry

end
