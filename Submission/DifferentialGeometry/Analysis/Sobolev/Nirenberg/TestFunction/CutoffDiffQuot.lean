import Submission.DifferentialGeometry.Analysis.Sobolev.Tools.DifferenceQuotient.WeakDerivative

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise _root_.BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem fderiv_cutoff_sq_apply {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (j : Fin d) (x : E) :
    (fderiv ℝ (fun y : E => (η y)^2) x) (EuclideanSpace.single j 1) =
      2 * η x * (fderiv ℝ η x) (EuclideanSpace.single j 1) := by
  have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
  rw [fderiv_fun_pow 2 (hη_diff x), smul_apply]
  have h_pow : (η x) ^ ((2 : ℕ) - 1) = η x := by norm_num
  rw [h_pow]
  have h_two : ((2 : ℕ) • η x) = 2 * η x := by
    rw [two_smul]
    ring
  rw [h_two, smul_eq_mul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.fderiv_cutoff_sq_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.fderiv_cutoff_sq_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.fderiv_cutoff_sq_apply ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.fderiv_cutoff_sq_apply

omit [NeZero d] in
theorem hasWeakPartialDeriv_cutoff_sq_mul_diffQuot
    (k j : Fin d) (h : ℝ) {η u g_j : E → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hu_localInt :
      _root_.MeasureTheory.LocallyIntegrable u ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ))
    (hg_j_localInt :
      _root_.MeasureTheory.LocallyIntegrable g_j ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ))
    (hwp : DeGiorgi.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    DeGiorgi.HasWeakPartialDeriv (d := d) j
      (fun y => (η y)^2 * diffQuot k h g_j y +
        ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
          diffQuot k h u y)
      (fun y => (η y)^2 * diffQuot k h u y) Set.univ := by
  have h_wp_dq :
      DeGiorgi.HasWeakPartialDeriv (d := d) j
        (diffQuot k h g_j) (diffQuot k h u) Set.univ :=
    hasWeakPartialDeriv_diffQuot (d := d) k j h hu_localInt hg_j_localInt hwp
  have h_dq_u_localInt :
      _root_.MeasureTheory.LocallyIntegrable (diffQuot k h u)
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ) := by
    rw [Measure.restrict_univ] at hu_localInt ⊢
    exact locallyIntegrable_diffQuot (d := d) k h hu_localInt
  have h_dq_g_localInt :
      _root_.MeasureTheory.LocallyIntegrable (diffQuot k h g_j)
        ((_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E).restrict Set.univ) := by
    rw [Measure.restrict_univ] at hg_j_localInt ⊢
    exact locallyIntegrable_diffQuot (d := d) k h hg_j_localInt
  exact DeGiorgi.HasWeakPartialDeriv.mul_smooth (Ω := Set.univ) isOpen_univ
    h_wp_dq (hη.pow 2) h_dq_u_localInt h_dq_g_localInt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasWeakPartialDeriv_cutoff_sq_mul_diffQuot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasWeakPartialDeriv_cutoff_sq_mul_diffQuot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasWeakPartialDeriv_cutoff_sq_mul_diffQuot ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction.hasWeakPartialDeriv_cutoff_sq_mul_diffQuot

end DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction
