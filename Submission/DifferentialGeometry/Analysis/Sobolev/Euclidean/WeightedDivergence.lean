import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.DivergenceForm
import Submission.DifferentialGeometry.Analysis.Sobolev.WeakDerivativeWeight

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_lp_weak_deriv_of_weighted_divergence
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [MeasurableSpace Z] [OpensMeasurableSpace Z]
    {μ : _root_.MeasureTheory.Measure Z} [_root_.MeasureTheory.IsLocallyFiniteMeasure μ] {W : Set Z} {Ω : Set E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hW : IsOpen W) (hΩ : IsOpen Ω) (v : Z)
    {U S ρ : Z × E → ℝ}
    (hU : _root_.MeasureTheory.MemLp U p (μ.prod (volume.restrict Ω)))
    (hS : _root_.MeasureTheory.MemLp S p (μ.prod (volume.restrict Ω)))
    (V : Fin d → _root_.MeasureTheory.Lp ℝ p (μ.prod (volume.restrict Ω)))
    (DV : Fin d → Fin d → _root_.MeasureTheory.Lp ℝ p (μ.prod (volume.restrict Ω)))
    {A : Fin d → Fin d → Z × E → ℝ}
    (hA : ∀ i j, _root_.MeasureTheory.MemLp (A i j) ∞ (μ.prod (volume.restrict Ω)))
    (hDA : ∀ i j, _root_.MeasureTheory.MemLp
      (fun q => fderiv ℝ (fun x => A i j (q.1, x)) q.2 (EuclideanSpace.single j 1))
      ∞ (μ.prod (volume.restrict Ω)))
    (hAsmooth : ∀ i j, ∀ᵐ t ∂μ, ContDiffOn ℝ (⊤ : ℕ∞) (fun x => A i j (t, x)) Ω)
    (hDV : ∀ i j, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv j
      (fun x => DV i j (t, x)) (fun x => V i (t, x)) Ω)
    (hρ : ContDiffOn ℝ (⊤ : ℕ∞) ρ (W ×ˢ Ω)) (hρne : ∀ q ∈ W ×ˢ Ω, ρ q ≠ 0)
    (hinv : _root_.MeasureTheory.MemLp (fun q => (ρ q)⁻¹) ∞ (μ.prod (volume.restrict Ω)))
    (hlog : _root_.MeasureTheory.MemLp (fun q => (ρ q)⁻¹ * fderiv ℝ ρ q (v, 0)) ∞
      (μ.prod (volume.restrict Ω)))
    (hweak : ∀ φ : Z × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ W ×ˢ Ω →
      (∫ q, ρ q * U q * fderiv ℝ φ q (v, 0) ∂μ.prod (volume.restrict Ω)) =
        (∑ i, ∑ j, ∫ q, A i j q * V i q * fderiv ℝ φ q (0, EuclideanSpace.single j 1)
          ∂μ.prod (volume.restrict Ω)) - ∫ q, S q * φ q ∂μ.prod (volume.restrict Ω)) :
    ∃ R : _root_.MeasureTheory.Lp ℝ p (μ.prod (volume.restrict Ω)),
      (R =ᵐ[μ.prod (volume.restrict Ω)] fun q =>
        (ρ q)⁻¹ * ((∑ i, ∑ j, (A i j q * DV i j q +
          fderiv ℝ (fun x => A i j (q.1, x)) q.2 (EuclideanSpace.single j 1) * V i q)) + S q) -
          ((ρ q)⁻¹ * fderiv ℝ ρ q (v, 0)) * U q) ∧
      ∀ φ : Z × E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ W ×ˢ Ω →
        (∫ q, U q * fderiv ℝ φ q (v, 0) ∂μ.prod (volume.restrict Ω)) =
          -∫ q, R q * φ q ∂μ.prod (volume.restrict Ω) := by
  obtain ⟨F, hF, hFweak⟩ := exists_lp_divergence_of_weakPartials hp hΩ V DV hA hDA hAsmooth hDV
  have hweighted (φ : Z × E → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ W ×ˢ Ω) :
      (∫ q, ρ q * U q * fderiv ℝ φ q (v, 0) ∂μ.prod (volume.restrict Ω)) =
        -∫ q, (F q + S q) * φ q ∂μ.prod (volume.restrict Ω) := by
    have hf := hFweak φ hφ hφc (hφs.trans (_root_.Set.prod_mono (_root_.Set.subset_univ _) Subset.rfl))
    have hw := hweak φ hφ hφc hφs
    have hFI : _root_.MeasureTheory.Integrable (fun q => F q * φ q) (μ.prod (volume.restrict Ω)) := ((Lp.memLp F).locallyIntegrable hp).integrable_smul_right_of_hasCompactSupport
      hφ.continuous hφc
    have hSI : _root_.MeasureTheory.Integrable (fun q => S q * φ q) (μ.prod (volume.restrict Ω)) := (hS.locallyIntegrable hp).integrable_smul_right_of_hasCompactSupport
      hφ.continuous hφc
    simp_rw [add_mul]
    rw [_root_.MeasureTheory.integral_add hFI hSI]
    linarith
  obtain ⟨R, hR, hRweak⟩ := exists_lp_weak_deriv_of_weighted_identity (hW.prod hΩ) hp (v, 0)
    hU ((Lp.memLp F).add hS) hρ hρne hinv hlog hweighted
  refine ⟨R, ?_, hRweak⟩
  filter_upwards [hR, hF] with q hRq hFq
  rw [hRq, Pi.add_apply, hFq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_weak_deriv_of_weighted_divergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_weak_deriv_of_weighted_divergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_weak_deriv_of_weighted_divergence ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_lp_weak_deriv_of_weighted_divergence

end DifferentialGeometry.Analysis.Sobolev.Euclidean
