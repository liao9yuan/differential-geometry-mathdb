import Submission.DifferentialGeometry.Analysis.Integration.PolarAnnulus
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.MeasureTheory.Group.Measure

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set _root_.MeasureTheory

namespace DifferentialGeometry.Analysis

theorem integral_annulus_eq_circleMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (c : ℂ) {r R : ℝ} (hr : 0 < r) :
    (∫ z in {z : ℂ | _root_.Dist.dist z c ∈ _root_.Set.Icc r R}, f z) =
      ∫ p in _root_.Set.Icc (r, -Real.pi) (R, Real.pi), p.1 • f (circleMap c p.1 p.2) := by
  calc
    _ = ∫ z in {z : ℂ | ‖z‖ ∈ _root_.Set.Icc r R}, f (c + z) := by
      have h := (_root_.MeasureTheory.measurePreserving_add_left (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure ℂ) c).setIntegral_preimage_emb
        (MeasurableEquiv.addLeft c).measurableEmbedding f {z : ℂ | _root_.Dist.dist z c ∈ _root_.Set.Icc r R}
      simpa only [_root_.Set.preimage_ofPred_eq, dist_eq_norm, add_sub_cancel_left] using h.symm
    _ = ∫ p in _root_.Set.Icc (r, -Real.pi) (R, Real.pi),
        p.1 • f (c + Complex.polarCoord.symm p) := integral_annulus_eq_polar _ hr
    _ = _ := by
      apply _root_.MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      intro p hp
      simp [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.integral_annulus_eq_circleMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.integral_annulus_eq_circleMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.integral_annulus_eq_circleMap ``Submission.DifferentialGeometry.Analysis.integral_annulus_eq_circleMap

end DifferentialGeometry.Analysis

end
