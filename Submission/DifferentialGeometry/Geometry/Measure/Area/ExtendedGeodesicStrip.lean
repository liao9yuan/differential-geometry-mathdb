import Submission.DifferentialGeometry.Geometry.Measure.Area.GeodesicStripLipschitz
import Submission.DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Strip
import Submission.DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission



noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.DifferentialGeometry _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Topology _root_.Submission.DifferentialGeometry.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal _root_.NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]



def extendedGeodesicStrip (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ₀ γ₁ : ℝ → M) : ℂ → M :=
  geodesicStrip g γ₀ γ₁ ∘ stripClamp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.extendedGeodesicStrip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.extendedGeodesicStrip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.extendedGeodesicStrip ``Submission.DifferentialGeometry.Geometry.extendedGeodesicStrip

theorem extendedGeodesicStrip_eq (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : ℝ → M) {z : ℂ} (hz : z ∈ unitStrip) :
    extendedGeodesicStrip g γ₀ γ₁ z = geodesicStrip g γ₀ γ₁ z := by
  simp only [extendedGeodesicStrip, Function.comp_apply, stripClamp_eq_self hz]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.extendedGeodesicStrip_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.extendedGeodesicStrip_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.extendedGeodesicStrip_eq ``Submission.DifferentialGeometry.Geometry.extendedGeodesicStrip_eq

theorem extendedGeodesicStrip_density_eq (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ₀ γ₁ : ℝ → M) {z : ℂ} (hz : z.re ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    riemannianAreaDensity g (extendedGeodesicStrip g γ₀ γ₁) z =
      riemannianAreaDensity g (geodesicStrip g γ₀ γ₁) z := by
  apply riemannianAreaDensity_congr
  filter_upwards [stripClamp_eventually_eq_id hz] with w hw
  exact congrArg (geodesicStrip g γ₀ γ₁) hw

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.extendedGeodesicStrip_density_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.extendedGeodesicStrip_density_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.extendedGeodesicStrip_density_eq ``Submission.DifferentialGeometry.Geometry.extendedGeodesicStrip_density_eq



theorem exists_extendedGeodesicStrip_lipschitz_radius [Nonempty M] [PreconnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ∀ (γ₀ γ₁ : ℝ → M) (L₀ L₁ : ℝ≥0),
      (∀ s t, riemannianEDistOf g (γ₀ s) (γ₀ t) ≤ (L₀ : ℝ≥0∞) * _root_.EDist.edist s t) →
      (∀ s t, riemannianEDistOf g (γ₁ s) (γ₁ t) ≤ (L₁ : ℝ≥0∞) * _root_.EDist.edist s t) →
      (∀ t, riemannianEDistOf g (γ₀ t) (γ₁ t) ≤ (ρ : ℝ≥0∞)) →
      ∃ K : ℝ≥0, ∀ z w : ℂ,
        riemannianEDistOf g (extendedGeodesicStrip g γ₀ γ₁ z) (extendedGeodesicStrip g γ₀ γ₁ w) ≤
          (K : ℝ≥0∞) * _root_.EDist.edist z w := by
  obtain ⟨ρ, hρ, hstrip⟩ := exists_geodesicStrip_lipschitz_radius g
  obtain ⟨C, hC⟩ := exists_lipschitz_stripClamp
  refine ⟨ρ, hρ, fun γ₀ γ₁ L₀ L₁ h₀ h₁ hnear => ?_⟩
  obtain ⟨K, hK⟩ := hstrip γ₀ γ₁ L₀ L₁ h₀ h₁ hnear
  refine ⟨K * C, fun z w => ?_⟩
  apply (hK (stripClamp z) (stripClamp_mem z) (stripClamp w) (stripClamp_mem w)).trans
  have h : (K : ℝ≥0∞) * _root_.EDist.edist (stripClamp z) (stripClamp w) ≤
      (K : ℝ≥0∞) * ((C : ℝ≥0∞) * _root_.EDist.edist z w) := by
    gcongr
    exact hC z w
  simpa only [ENNReal.coe_mul, mul_assoc] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.exists_extendedGeodesicStrip_lipschitz_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.exists_extendedGeodesicStrip_lipschitz_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.exists_extendedGeodesicStrip_lipschitz_radius ``Submission.DifferentialGeometry.Geometry.exists_extendedGeodesicStrip_lipschitz_radius



theorem integrable_extendedGeodesicStrip_density
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ₀ γ₁ : ℝ → M} {K : ℝ≥0}
    (hK : ∀ z w : ℂ,
      riemannianEDistOf g (extendedGeodesicStrip g γ₀ γ₁ z) (extendedGeodesicStrip g γ₀ γ₁ w) ≤
        (K : ℝ≥0∞) * _root_.EDist.edist z w) :
    IntegrableOn (riemannianAreaDensity g (extendedGeodesicStrip g γ₀ γ₁)) unitSquare := by
  have : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict unitSquare) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_unitSquare.measure_lt_top (μ := _root_.MeasureTheory.MeasureSpace.volume))⟩
  exact integrableOn_riemannianAreaDensity_of_lipschitz g hK unitSquare

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.integrable_extendedGeodesicStrip_density then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.integrable_extendedGeodesicStrip_density"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.integrable_extendedGeodesicStrip_density ``Submission.DifferentialGeometry.Geometry.integrable_extendedGeodesicStrip_density

end DifferentialGeometry.Geometry
