import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives
import Submission.DifferentialGeometry.Analysis.Integration.Integral.LocalIntegrationByParts

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem hasWeakPartialDeriv_of_contDiffOn
    {Ω : Set E} (hΩ : IsOpen Ω) {f : E → ℝ}
    (hf : ContDiffOn ℝ 1 f Ω) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) f Ω := by
  intro φ hφ hφc hφs
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_contDiffOn hΩ hf
    (hφ.of_le (by simp)) hφc hφs (EuclideanSpace.single i 1)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_contDiffOn ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.hasWeakPartialDeriv_of_contDiffOn

end DifferentialGeometry.Analysis.Sobolev.Euclidean
