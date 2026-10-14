import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.WeakDerivatives
import Mathlib.Analysis.Distribution.Distribution

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem integrable_mul_fderiv_apply_of_memLp
    {Ω : Set E} {w : E → ℝ} (hw : _root_.MeasureTheory.MemLp w 2 (volume.restrict Ω))
    {φ : E → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (i : Fin d) :
    _root_.MeasureTheory.Integrable (fun x => w x * (fderiv ℝ φ x) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
  have hdφ : _root_.MeasureTheory.MemLp (fun x : E => (fderiv ℝ φ x) (EuclideanSpace.single i 1)) 2
      (volume.restrict Ω) :=
    (((hφ.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const).memLp_of_hasCompactSupport
        (hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))).restrict _
  exact MemLp.integrable_mul hw hdφ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.integrable_mul_fderiv_apply_of_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.integrable_mul_fderiv_apply_of_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.integrable_mul_fderiv_apply_of_memLp ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.integrable_mul_fderiv_apply_of_memLp

noncomputable def weakPartialDistribution
    (Ω : TopologicalSpace.Opens E) (w : E → ℝ) (i : Fin d) :
    Distribution Ω ℝ ⊤ :=
  let T : Distribution Ω ℝ ⊤ :=
    ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℝ) ℝ
      {S : Set (TestFunction Ω ℝ ⊤) | IsCompact S}
      (TestFunction.integralAgainstBilinCLM (n := ⊤) (ContinuousLinearMap.lsmul ℝ ℝ)
        (volume.restrict (Ω : Set E)) w)
  Distribution.lineDerivCLM (k := ⊤) (n := ⊤) (EuclideanSpace.single i 1) T

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.weakPartialDistribution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.weakPartialDistribution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.weakPartialDistribution ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.weakPartialDistribution

omit [NeZero d] in
@[simp] theorem weakPartialDistribution_apply_of_memLp
    {Ω : TopologicalSpace.Opens E} {w : E → ℝ}
    (hw : _root_.MeasureTheory.MemLp w 2 (volume.restrict (Ω : Set E))) (i : Fin d)
    (φ : TestFunction Ω ℝ ⊤) :
    weakPartialDistribution Ω w i φ =
      -∫ x in Ω, w x * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
  have hwloc : _root_.MeasureTheory.LocallyIntegrable w (volume.restrict (Ω : Set E)) :=
    hw.locallyIntegrable (by norm_num)
  have hwon : _root_.MeasureTheory.LocallyIntegrableOn w (Ω : Set E)
      (volume.restrict (Ω : Set E)) := hwloc.locallyIntegrableOn _
  rw [weakPartialDistribution, Distribution.lineDerivCLM_apply]
  simp only [ContinuousLinearMap.toUniformConvergenceCLM_apply]
  rw [TestFunction.integralAgainstBilinCLM_eq_integral hwon]
  have hφd : Differentiable ℝ (φ : E → ℝ) := φ.contDiff.differentiable (by simp)
  simp only [TestFunction.lineDerivCLM_apply, top_add, le_refl, if_true,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  congr 1
  refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change lineDeriv ℝ (φ : E → ℝ) x (EuclideanSpace.single i 1) * w x =
    w x * (fderiv ℝ (φ : E → ℝ) x) (EuclideanSpace.single i 1)
  rw [hφd.differentiableAt.lineDeriv_eq_fderiv]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.weakPartialDistribution_apply_of_memLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.weakPartialDistribution_apply_of_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.weakPartialDistribution_apply_of_memLp ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.weakPartialDistribution_apply_of_memLp

end DifferentialGeometry.Analysis.Sobolev.Euclidean
