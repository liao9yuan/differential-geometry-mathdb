import Mathlib.Geometry.Manifold.Riemannian.PathELength

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Set _root_.MeasureTheory
open scoped _root_.Manifold _root_.ContDiff _root_.ENNReal

namespace Manifold
open _root_.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [∀ x : M, ENorm (TangentSpace I x)]
  [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]

open _root_.Manifold in
theorem riemannianEDist_le_of_curve_speed_bound
    {γ : ℝ → M} {a b : ℝ} {C : ℝ≥0∞} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (_root_.Set.Icc a b))
    (hC : ∀ t ∈ _root_.Set.Ioo a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ ≤ C) :
    riemannianEDist I (γ a) (γ b) ≤ C * ENNReal.ofReal (b - a) := by
  apply (_root_.Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab).trans
  rw [_root_.Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  calc
    _ ≤ ∫⁻ _t in _root_.Set.Ioo a b, C := _root_.MeasureTheory.setLIntegral_mono' measurableSet_Ioo hC
    _ = _ := by rw [_root_.MeasureTheory.setLIntegral_const, Real.volume_Ioo]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Manifold.riemannianEDist_le_of_curve_speed_bound then
    throwError "Refusing to shadow existing declaration Manifold.riemannianEDist_le_of_curve_speed_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `Manifold.riemannianEDist_le_of_curve_speed_bound ``Submission.Manifold.riemannianEDist_le_of_curve_speed_bound

end Manifold
