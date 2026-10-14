import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.IntegrationByParts.WeightedFlux
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.ReloweringFlux

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Geometry.Connection _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

theorem forward_uniqueness_integral_cutoff_divergence_le
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ)) (t : ℝ)
    {B₂ BP Background ε : ℝ} (hε : 0 < ε)
    (hB₂ : ∀ x ∈ tsupport (χ : M → ℝ),
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ B₂)
    (hBP : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 4
      (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t) (metricCov (I := I) (g₂ t))
        (metricCov_smooth (I := I) (g₂ t)) x) ≤ BP)
    (hBackground : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 2
      (metricTensorField (I := I) (g₂ t) x) ≤ Background) :
    let S := forwardUniquenessSfield (I := I) g₁ g₂ t
    let U := forwardUniquenessUflux (I := I) g₁ g₂ t
    let A := metricNabla0S (I := I) (g₁ t) S
    let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 4 x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
    let C_U := 32 * (Module.finrank ℝ E : ℝ) ^ 5 * B₂ +
      8 * (Module.finrank ℝ E : ℝ) ^ 10 * (BP * Background)
    let μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t)
    2 * (∫ x, χ x ^ 2 * inner0S (I := I) (g₁ t) x 4
      (covDiv0SField (I := I) (g₁ t) U x) (S x) ∂μ) ≤
      ε * (∫ x, χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) ∂μ) +
      (ε⁻¹ + 2) * C_U * (∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ) +
      2 * (∫ x, normSq0S (I := I) (g₁ t) x 5 (B x) ∂μ) := by
  dsimp only
  refine integral_sq_weighted_covDiv0SField_le_of_hasCompactSupport (I := I) (g₁ t) χ hχ
    (forwardUniquenessSfield (I := I) g₁ g₂ t) (forwardUniquenessUflux (I := I) g₁ g₂ t)
    (dens_continuous (I := I) g₁ g₂ t) hε ?_
  intro x hx
  have hB₂0 : 0 ≤ B₂ := (normSq0S_nonneg (I := I) (g₁ t) x 4 _).trans (hB₂ x hx)
  have hBP0 : 0 ≤ BP := (normSq0S_nonneg (I := I) (g₁ t) x 4 _).trans (hBP x hx)
  have hBackground0 : 0 ≤ Background :=
    (normSq0S_nonneg (I := I) (g₁ t) x 2 _).trans (hBackground x hx)
  have hBP' : normSq0S (I := I) (g₁ t) x 4
      ((forwardUniquenessTf (I := I) g₁ t - forwardUniquenessSfield (I := I) g₁ g₂ t) x) ≤ BP := by
    rw [forwardUniquenessP_eq]
    exact hBP x hx
  exact fluxSlabLe (I := I) g₁ g₂ (forwardUniquenessTf (I := I) g₂)
    (fun z => forwardUniquenessTf (I := I) g₁ z - forwardUniquenessSfield (I := I) g₁ g₂ z)
    t x hB₂0 hBP0 hBackground0 (hB₂ x hx) hBP' (hBackground x hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_integral_cutoff_divergence_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_integral_cutoff_divergence_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_integral_cutoff_divergence_le ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_integral_cutoff_divergence_le

theorem forward_uniqueness_integral_corrected_cutoff_divergence_le
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    (χ : C^∞⟮I, M; ℝ⟯) (hχ : HasCompactSupport (χ : M → ℝ)) (t : ℝ)
    {C BH B₀ B₁ B₂ BP Background ε : ℝ} (hε : 0 < ε) (hC : 1 ≤ C)
    (hEquiv : ∀ x ∈ tsupport (χ : M → ℝ), ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hBH : ∀ x ∈ tsupport (χ : M → ℝ), metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ BH)
    (hB₀ : ∀ x ∈ tsupport (χ : M → ℝ),
      normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ B₀)
    (hB₁ : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₂ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ B₁)
    (hB₂ : ∀ x ∈ tsupport (χ : M → ℝ),
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ B₂)
    (hBP : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 4
      (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t) (metricCov (I := I) (g₂ t))
        (metricCov_smooth (I := I) (g₂ t)) x) ≤ BP)
    (hBackground : ∀ x ∈ tsupport (χ : M → ℝ), normSq0S (I := I) (g₁ t) x 2
      (metricTensorField (I := I) (g₂ t) x) ≤ Background) :
    let n : ℝ := Module.finrank ℝ E
    let S := forwardUniquenessSfield (I := I) g₁ g₂ t
    let U := forwardUniquenessUflux (I := I) g₁ g₂ t -
      forwardUniquenessReloweringFlux (I := I) g₁ g₂ t
    let A := metricNabla0S (I := I) (g₁ t) S
    let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 4 x
      ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
        (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
      (unitZeroSec (I := I) (M := M) x)
    let C_U := 32 * n ^ 5 * B₂ + 8 * n ^ 10 * (BP * Background)
    let C_V := 4 * n ^ 15 * C ^ 7 * B₁ +
      (16 * n ^ 18 * C ^ 8 + 32 * n ^ 19 * C ^ 6) * B₀ * BH
    let μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t)
    2 * (∫ x, χ x ^ 2 * inner0S (I := I) (g₁ t) x 4
      (covDiv0SField (I := I) (g₁ t) U x) (S x) ∂μ) ≤
      ε * (∫ x, χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) ∂μ) +
      (ε⁻¹ + 2) * (2 * C_U + 2 * C_V) *
        (∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ) +
      2 * (∫ x, normSq0S (I := I) (g₁ t) x 5 (B x) ∂μ) := by
  dsimp only
  refine integral_sq_weighted_covDiv0SField_le_of_hasCompactSupport (I := I) (g₁ t) χ hχ
    (forwardUniquenessSfield (I := I) g₁ g₂ t)
    (forwardUniquenessUflux (I := I) g₁ g₂ t - forwardUniquenessReloweringFlux (I := I) g₁ g₂ t)
    (dens_continuous (I := I) g₁ g₂ t) hε ?_
  intro x hx
  exact forward_uniqueness_corrected_flux_norm_sq_le (I := I) g₁ g₂ t x hC (hEquiv x hx)
    (hBH x hx) (hB₀ x hx) (hB₁ x hx) (hB₂ x hx) (hBP x hx) (hBackground x hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_integral_corrected_cutoff_divergence_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_integral_corrected_cutoff_divergence_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_integral_corrected_cutoff_divergence_le ``Submission.DifferentialGeometry.PDE.RicciFlow.forward_uniqueness_integral_corrected_cutoff_divergence_le

end DifferentialGeometry.PDE.RicciFlow
