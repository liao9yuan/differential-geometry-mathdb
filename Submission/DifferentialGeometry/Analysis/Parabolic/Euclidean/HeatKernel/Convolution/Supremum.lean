import Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.Convolution.Lp
import Mathlib.Topology.ContinuousMap.Bounded.Normed

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Real
open scoped _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Euclidean

section SupKernel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def supKernel (η : V → ℝ) (u : BoundedContinuousFunction V F) (x : V) : F :=
  ∫ y, η y • u (x - y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel

omit [CompleteSpace F] in
theorem supKernel_int {η : V → ℝ} (hη : _root_.MeasureTheory.Integrable η)
    (u : BoundedContinuousFunction V F) (x : V) :
    Integrable (fun y : V => η y • u (x - y)) := by
  refine (hη.norm.mul_const ‖u‖).mono' ?_ ?_
  · exact hη.aestronglyMeasurable.smul
      ((u.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · filter_upwards with y
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm (x - y)) (norm_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_int then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_int"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_int ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_int

omit [CompleteSpace F] in
theorem supKernel_norm {η : V → ℝ} (hη : _root_.MeasureTheory.Integrable η)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖supKernel η u x‖ ≤ (∫ y, ‖η y‖) * ‖u‖ := by
  unfold supKernel
  calc
    ‖∫ y, η y • u (x - y)‖
        ≤ ∫ y, ‖η y‖ * ‖u‖ :=
      _root_.MeasureTheory.norm_integral_le_of_norm_le (hη.norm.mul_const ‖u‖)
        (Filter.Eventually.of_forall fun y => by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (u.norm_coe_le_norm (x - y))
            (norm_nonneg _))
    _ = (∫ y, ‖η y‖) * ‖u‖ := by rw [_root_.MeasureTheory.integral_mul_const]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_norm

omit [CompleteSpace F] in
theorem supKernel_sub {η : V → ℝ} (hη : _root_.MeasureTheory.Integrable η)
    (u v : BoundedContinuousFunction V F) (x : V) :
    supKernel η (u - v) x = supKernel η u x - supKernel η v x := by
  unfold supKernel
  rw [← _root_.MeasureTheory.integral_sub (supKernel_int hη u x) (supKernel_int hη v x)]
  apply _root_.MeasureTheory.integral_congr_ae
  filter_upwards with y
  simp only [BoundedContinuousFunction.sub_apply, smul_sub]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_sub

omit [CompleteSpace F] in
theorem supKernel_contract {η : V → ℝ} (hη : _root_.MeasureTheory.Integrable η)
    (hη0 : ∀ y, 0 ≤ η y) (hη1 : ∫ y, η y = 1)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖supKernel η u x‖ ≤ ‖u‖ := by
  refine (supKernel_norm hη u x).trans_eq ?_
  have habs : (fun y : V => ‖η y‖) = η := by
    funext y
    simp [Real.norm_eq_abs, abs_of_nonneg (hη0 y)]
  rw [habs, hη1, one_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_contract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_contract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_contract ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.supKernel_contract

end SupKernel

section HeatSup

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def heatSup (t : ℝ) (u : BoundedContinuousFunction V F) (x : V) : F :=
  supKernel (heatKernel t) u x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup

omit [CompleteSpace F] in
theorem heatSup_contract {t : ℝ} (ht : 0 < t)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatSup t u x‖ ≤ ‖u‖ := by
  exact supKernel_contract (heatKernel_int ht) (heatKernel_nonneg ht)
    (integral_heatKernel ht) u x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_contract then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_contract"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_contract ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatSup_contract

def heatD1Sup (t : ℝ) (v : V) (u : BoundedContinuousFunction V F) (x : V) : F :=
  supKernel (heatD1 t v) u x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Sup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Sup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Sup ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Sup

def heatD2Sup (t : ℝ) (v w : V) (u : BoundedContinuousFunction V F) (x : V) : F :=
  supKernel (heatD2 t v w) u x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Sup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Sup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Sup ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Sup

omit [CompleteSpace F] in
theorem heatD1Sup_sub {t : ℝ} (ht : 0 < t) (v : V)
    (u₁ u₂ : BoundedContinuousFunction V F) (x : V) :
    heatD1Sup t v (u₁ - u₂) x =
      heatD1Sup t v u₁ x - heatD1Sup t v u₂ x := by
  exact supKernel_sub (heatD1_int ht v) u₁ u₂ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Sup_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Sup_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Sup_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Sup_sub

omit [CompleteSpace F] in
theorem heatD2Sup_sub {t : ℝ} (ht : 0 < t) (v w : V)
    (u₁ u₂ : BoundedContinuousFunction V F) (x : V) :
    heatD2Sup t v w (u₁ - u₂) x =
      heatD2Sup t v w u₁ x - heatD2Sup t v w u₂ x := by
  exact supKernel_sub (heatD2_int ht v w) u₁ u₂ x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Sup_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Sup_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Sup_sub ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Sup_sub

omit [CompleteSpace F] in
theorem heatD1Sup_norm {t : ℝ} (ht : 0 < t) (v : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatD1Sup t v u x‖ ≤
      (‖v‖ * (heatScale t)⁻¹ * heatC1 V) * ‖u‖ := by
  refine (supKernel_norm (heatD1_int ht v) u x).trans ?_
  exact mul_le_mul_of_nonneg_right (integral_norm_D1 ht v) (norm_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Sup_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Sup_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Sup_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD1Sup_norm

omit [CompleteSpace F] in
theorem heatD2Sup_norm {t : ℝ} (ht : 0 < t) (v w : V)
    (u : BoundedContinuousFunction V F) (x : V) :
    ‖heatD2Sup t v w u x‖ ≤
      (‖v‖ * ‖w‖ * t⁻¹ * heatC2 V) * ‖u‖ := by
  refine (supKernel_norm (heatD2_int ht v w) u x).trans ?_
  exact mul_le_mul_of_nonneg_right (integral_norm_D2 ht v w) (norm_nonneg _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Sup_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Sup_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Sup_norm ``Submission.DifferentialGeometry.Analysis.Parabolic.Euclidean.heatD2Sup_norm

end HeatSup

end Euclidean
end Parabolic
end Analysis
end DifferentialGeometry

end
