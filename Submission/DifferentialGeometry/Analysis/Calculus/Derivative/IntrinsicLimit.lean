import Submission.DifferentialGeometry.Analysis.Convex.SemiconcaveDerivativeLimit
import Submission.DifferentialGeometry.Analysis.Calculus.Derivative.Curve

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.Analysis.Calculus

open _root_.Filter _root_.Set
open scoped _root_.Manifold _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem tendsto_mvfderiv_along_of_concaveOn_sub
    {ι : Type*} {L : Filter ι} {D : Set ℝ}
    {F : ι → M → ℝ} {f : M → ℝ} {q : ℝ → ℝ}
    {beta : ℝ → M} {t : ℝ} (ht : t ∈ interior D)
    (hbeta : MDifferentiableAt 𝓘(ℝ, ℝ) I beta t)
    (hconcave : ∀ᶠ i in L, ConcaveOn ℝ D (fun r ↦ F i (beta r) - q r))
    (hF : ∀ᶠ i in L, MDifferentiableAt I 𝓘(ℝ, ℝ) (F i) (beta t))
    (hlim : ∀ r ∈ D, _root_.Filter.Tendsto (fun i ↦ F i (beta r)) L (𝓝 (f (beta r))))
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (beta t))
    (hq : DifferentiableAt ℝ q t) :
    Tendsto (fun i ↦ mvfderiv (I := I) (F i) (beta t)
        (mfderiv 𝓘(ℝ, ℝ) I beta t (realTangentOne t))) L
      (𝓝 (mvfderiv (I := I) f (beta t)
        (mfderiv 𝓘(ℝ, ℝ) I beta t (realTangentOne t)))) := by
  have hFcurve : ∀ᶠ i in L, DifferentiableAt ℝ (fun r ↦ F i (beta r)) t := by
    filter_upwards [hF] with i hi
    exact (hasDerivAt_comp_mfderiv_along I (F i) beta t hi hbeta).differentiableAt
  have hfcurve : DifferentiableAt ℝ (fun r ↦ f (beta r)) t :=
    (hasDerivAt_comp_mfderiv_along I f beta t hf hbeta).differentiableAt
  have h := DifferentialGeometry.Analysis.tendsto_deriv_of_concaveOn_sub
    ht hconcave hFcurve hlim hfcurve hq
  have heq : (fun i ↦ deriv (fun r ↦ F i (beta r)) t) =ᶠ[L]
      (fun i ↦ mvfderiv (I := I) (F i) (beta t)
        (mfderiv 𝓘(ℝ, ℝ) I beta t (realTangentOne t))) := by
    filter_upwards [hF] with i hi
    exact deriv_comp_mfderiv_along I (F i) beta t hi hbeta
  have hlimit : deriv (fun r ↦ f (beta r)) t =
      mvfderiv (I := I) f (beta t)
        (mfderiv 𝓘(ℝ, ℝ) I beta t (realTangentOne t)) :=
    deriv_comp_mfderiv_along I f beta t hf hbeta
  rw [hlimit] at h
  exact h.congr' heq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Calculus.tendsto_mvfderiv_along_of_concaveOn_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Calculus.tendsto_mvfderiv_along_of_concaveOn_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Calculus.tendsto_mvfderiv_along_of_concaveOn_sub ``Submission.DifferentialGeometry.Analysis.Calculus.tendsto_mvfderiv_along_of_concaveOn_sub

end DifferentialGeometry.Analysis.Calculus
