import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalCoefficientRegularity
import Submission.DifferentialGeometry.Analysis.Sobolev.WeakDerivativeWeight
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Characterization.CanonicalConnection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Manifold _root_.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Analysis.Parabolic

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem integral_fixed_density_eq_of_weighted_identity
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g)
    (q : SmoothRiemannianMetric I M) (α : M)
    {J : Set ℝ} (hJ : IsOpen J) (hJD : J ⊆ D.regular)
    {Ω : Set EuStd} (hΩ : IsOpen Ω) (hΩs : Ω ⊆ chartTargetEuclid (I := I) α)
    {ν : _root_.MeasureTheory.Measure (ℝ × EuStd)} {U F : ℝ × EuStd → ℝ}
    (hU : _root_.MeasureTheory.LocallyIntegrable (fun p => densityOnEuclid (I := I) q α p.2 * U p) ν)
    (hF : _root_.MeasureTheory.LocallyIntegrable F ν) (L : ((ℝ × EuStd) → ℝ) → ℝ)
    (hweak : ∀ φ : ℝ × EuStd → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ J ×ˢ Ω →
      (∫ p, densityOnEuclid (I := I) (g p.1) α p.2 * U p * fderiv ℝ φ p (1, 0) ∂ν) =
        L φ - ∫ p, F p * φ p ∂ν)
    {φ : ℝ × EuStd → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ J ×ˢ Ω) :
    let σ := fun p : ℝ × EuStd => densityOnEuclid (I := I) q α p.2
    let r := fun p : ℝ × EuStd => densityOnEuclid (I := I) (g p.1) α p.2 / σ p
    (∫ p, σ p * U p * fderiv ℝ φ p (1, 0) ∂ν) = L (fun p => φ p / r p) -
      ∫ p, ((r p)⁻¹ * F p - ((r p)⁻¹ * fderiv ℝ r p (1, 0)) * (σ p * U p)) * φ p ∂ν := by
  intro σ r
  let G : MetricConnectionFamilyOn (I := I) (M := M) D :=
    { metric := g
      connection := fun t => leviCivitaConnectionOfMetric (g t)
      metricCompatible := fun t => leviCivitaConnectionOfMetric_isMetricCompatible (g t) }
  have hρ := (densityOnEuclid_family_contDiffOn (G := G) hG hJD α).mono
    (_root_.Set.prod_mono Subset.rfl hΩs)
  have hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ (J ×ˢ Ω) :=
    (densityOnEuclid_contDiffOn q α).comp contDiff_snd.contDiffOn (fun p hp => hΩs hp.2)
  have hσne (p : ℝ × EuStd) (hp : p ∈ J ×ˢ Ω) : σ p ≠ 0 :=
    (densityOnEuclid_pos q α (hΩs hp.2)).ne'
  have hr : ContDiffOn ℝ (⊤ : ℕ∞) r (J ×ˢ Ω) := hρ.div hσ hσne
  have hrne (p : ℝ × EuStd) (hp : p ∈ J ×ˢ Ω) : r p ≠ 0 :=
    div_ne_zero (densityOnEuclid_pos (g p.1) α (hΩs hp.2)).ne' (hσne p hp)
  apply Sobolev.integral_fderiv_eq_of_weighted_identity
    (hJ.prod hΩ) (1, 0) hU hF hr hrne L
  · intro ψ hψ hψc hψs
    have heq : (∫ p, r p * (σ p * U p) * fderiv ℝ ψ p (1, 0) ∂ν) =
        ∫ p, densityOnEuclid (I := I) (g p.1) α p.2 * U p * fderiv ℝ ψ p (1, 0) ∂ν := by
      apply _root_.MeasureTheory.integral_congr_ae
      filter_upwards [] with p
      by_cases hp : p ∈ J ×ˢ Ω
      · dsimp only [r]
        field_simp [hσne p hp]
      · have hd : fderiv ℝ ψ p = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hp (hψs h))
        simp only [hd, zero_apply, _root_.MulZeroClass.mul_zero]
    rw [heq]
    exact hweak ψ hψ hψc hψs
  · exact hφ
  · exact hφc
  · exact hφs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.integral_fixed_density_eq_of_weighted_identity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.integral_fixed_density_eq_of_weighted_identity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.integral_fixed_density_eq_of_weighted_identity ``Submission.DifferentialGeometry.Analysis.Parabolic.integral_fixed_density_eq_of_weighted_identity

end DifferentialGeometry.Analysis.Parabolic
