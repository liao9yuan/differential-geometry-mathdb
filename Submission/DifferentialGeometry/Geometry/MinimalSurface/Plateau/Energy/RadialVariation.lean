import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Reparametrization
import Submission.DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Directional
import Submission.DifferentialGeometry.Analysis.Integration.Integral.AffineReciprocal
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Analysis
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.NNReal _root_.ENNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def radialDiskEnergyFirstVariation (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : closedDisk → M) (ψ : ℝ → ℝ) : ℝ :=
  ∫ z in Metric.closedBall (0 : ℂ) 1, deriv ψ (Complex.arg z / (2 * Real.pi)) *
    (diskMapDirectionalEnergyDensity g (diskExtension u) (fun z => radialDirection z) z -
      diskMapDirectionalEnergyDensity g (diskExtension u)
        (fun z => Complex.I * (radialDirection z : ℂ)) z) / 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.radialDiskEnergyFirstVariation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.radialDiskEnergyFirstVariation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.radialDiskEnergyFirstVariation ``Submission.DifferentialGeometry.Geometry.radialDiskEnergyFirstVariation

theorem diskMapEnergyDensity_eq_radial_add_tangential
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z : ℂ) :
    diskMapEnergyDensity g U z =
      (diskMapDirectionalEnergyDensity g U (fun z => radialDirection z) z +
        diskMapDirectionalEnergyDensity g U (fun z => Complex.I * (radialDirection z : ℂ)) z) / 2 := by
  let Q := (g.inner (U z)).bilinearComp (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
  exact congrArg (fun x : ℝ => x / 2)
    (bilinear_trace_unit_rotation Q (Circle.norm_coe (radialDirection z))).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.diskMapEnergyDensity_eq_radial_add_tangential then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.diskMapEnergyDensity_eq_radial_add_tangential"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.diskMapEnergyDensity_eq_radial_add_tangential ``Submission.DifferentialGeometry.Geometry.diskMapEnergyDensity_eq_radial_add_tangential

variable [FiniteDimensional ℝ E] [T3Space M]

theorem abs_riemannianDiskEnergy_inverse_radial_sub_le
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {u : closedDisk → M} {Cu C K L : ℝ≥0}
    (hu : ∀ x y, riemannianEDistOf g (u x) (u y) ≤ (Cu : ℝ≥0∞) * _root_.EDist.edist x y)
    {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) (hψLip : LipschitzWith C ψ)
    {t : ℝ} (ht : |t| * (C : ℝ) ≤ 1 / 2)
    (δ : loopCircle ≃ₜ loopCircle)
    (hδ : ∀ s : ℝ, δ (s : loopCircle) = ((s + t * ψ s : ℝ) : loopCircle))
    (hF : LipschitzWith K (geometricCircleHomeomorph δ))
    (hG : LipschitzWith L (geometricCircleHomeomorph δ).symm) :
    let φ := radialDiskHomeomorph (geometricCircleHomeomorph δ) hF hG
    |riemannianDiskEnergy g (u ∘ φ.symm) - riemannianDiskEnergy g u -
        t * radialDiskEnergyFirstVariation g u ψ| ≤
      2 * (C : ℝ) ^ 2 * t ^ 2 * riemannianDiskEnergy g u := by
  let U := diskExtension u
  let A := diskMapDirectionalEnergyDensity g U (fun z => radialDirection z)
  let B := diskMapDirectionalEnergyDensity g U (fun z => Complex.I * (radialDirection z : ℂ))
  let a := fun z : ℂ => deriv ψ (Complex.arg z / (2 * Real.pi))
  let μ := volume.restrict (Metric.closedBall (0 : ℂ) 1)
  have haC (z : ℂ) : |a z| ≤ C := by
    exact norm_deriv_le_of_lipschitz hψLip
  have hta (z : ℂ) : |t * a z| ≤ 1 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (haC z) (abs_nonneg t)).trans ht
  have hderiv (s : ℝ) : deriv (fun s => s + t * ψ s) s = 1 + t * deriv ψ s := by
    exact ((hasDerivAt_id s).add ((hψ s).hasDerivAt.const_mul t)).deriv
  have hdiff : Differentiable ℝ (fun s => s + t * ψ s) :=
    differentiable_id.add (hψ.const_mul t)
  have hpos (s : ℝ) : 0 < deriv (fun s => s + t * ψ s) s := by
    rw [hderiv]
    have hd : |deriv ψ s| ≤ (C : ℝ) := norm_deriv_le_of_lipschitz hψLip
    have hb : |t * deriv ψ s| ≤ 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hd (abs_nonneg t)).trans ht
    linarith [(abs_le.mp hb).1]
  have hApos (z : ℂ) : 0 ≤ A z := metric_inner_self_nonneg g _ _
  have hBpos (z : ℂ) : 0 ≤ B z := metric_inner_self_nonneg g _ _
  have hU := diskExtension_riemannian_lipschitz g hu
  have hmA : Measurable A := measurable_diskMapDirectionalEnergyDensity g
    (continuous_of_riemannian_lipschitz g hU) measurable_coe_radialDirection
  have hmB : Measurable B := measurable_diskMapDirectionalEnergyDensity g
    (continuous_of_riemannian_lipschitz g hU) (measurable_coe_radialDirection.const_mul Complex.I)
  have hsum (z : ℂ) : A z + B z = 2 * diskMapEnergyDensity g U z := by
    have h := diskMapEnergyDensity_eq_radial_add_tangential g U z
    change diskMapEnergyDensity g U z = (A z + B z) / 2 at h
    linarith
  have htotal : _root_.MeasureTheory.Integrable (fun z => 2 * diskMapEnergyDensity g U z) μ :=
    (integrable_diskMapEnergyDensity g hu).const_mul 2
  have hA : _root_.MeasureTheory.Integrable A μ := htotal.mono' hmA.aestronglyMeasurable (by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hApos z), ← hsum]
    linarith [hBpos z])
  have hB : _root_.MeasureTheory.Integrable B μ := htotal.mono' hmB.aestronglyMeasurable (by
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (hBpos z), ← hsum]
    linarith [hApos z])
  have ha : _root_.MeasureTheory.AEStronglyMeasurable a μ :=
    ((measurable_deriv ψ).comp (Complex.measurable_arg.div_const (2 * Real.pi))).aestronglyMeasurable
  have hbound := abs_integral_affine_reciprocal_taylor_remainder_le_sum hA hB ha
    (Eventually.of_forall hApos) (Eventually.of_forall hBpos)
    (Eventually.of_forall hta) (Eventually.of_forall haC)
  have henergy : (∫ z, (A z + B z) / 2 ∂μ) = riemannianDiskEnergy g u := by
    apply _root_.MeasureTheory.integral_congr_ae
    exact Eventually.of_forall (fun z => (diskMapEnergyDensity_eq_radial_add_tangential g U z).symm)
  have hsumint : (∫ z, A z + B z ∂μ) = 2 * riemannianDiskEnergy g u := by
    simp_rw [hsum]
    exact _root_.MeasureTheory.integral_const_mul _ _
  have hvar := riemannianDiskEnergy_inverse_radial_reparametrize g hu δ hδ hdiff hpos hF hG
  simp_rw [hderiv] at hvar
  change _ = ∫ z, ((1 + t * a z) * A z + (1 + t * a z)⁻¹ * B z) / 2 ∂μ at hvar
  rw [henergy, hsumint] at hbound
  dsimp only
  rw [hvar]
  have hstress : radialDiskEnergyFirstVariation g u ψ =
      ∫ z, a z * (A z - B z) / 2 ∂μ := rfl
  rw [hstress]
  calc
    _ ≤ (C : ℝ) ^ 2 * t ^ 2 * (2 * riemannianDiskEnergy g u) := hbound
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.abs_riemannianDiskEnergy_inverse_radial_sub_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.abs_riemannianDiskEnergy_inverse_radial_sub_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.abs_riemannianDiskEnergy_inverse_radial_sub_le ``Submission.DifferentialGeometry.Geometry.abs_riemannianDiskEnergy_inverse_radial_sub_le

end DifferentialGeometry.Geometry
