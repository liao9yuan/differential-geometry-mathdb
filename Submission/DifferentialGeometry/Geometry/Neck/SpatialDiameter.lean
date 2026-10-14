import Submission.DifferentialGeometry.Geometry.Neck.Spatial
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarDiameter
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]

theorem exists_uniform_spatial_neck_core_diameter :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : SmoothRiemannianMetric I3 M) (eps : ℝ) (x : M)
      (nk : SpatialNeck g eps x),
      ∀ v ∈ nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10),
        ∀ w ∈ nk.map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (-10 : ℝ) 10),
          metricDistance g v w ≤ C / Real.sqrt (metricScalarAt g x) := by
  obtain ⟨D, hD, hband⟩ := exists_uniform_collar_band_diameter_of_axis (M := M)
  refine ⟨D + 40, by linarith, ?_⟩
  intro g eps x nk v hv w hw
  have hslab : (_root_.Set.univ : Set (Sphere 2)) ×ˢ _root_.Set.Icc (-10 : ℝ) 10 ⊆
      univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹ := by
    have hi : (10 : ℝ) < eps⁻¹ := (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr
      (by linarith [nk.eps_small])
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have haxis (p : Sphere 2) (z : ℝ) (hz : z ∈ _root_.Set.Icc (-10 : ℝ) 10) :
      riemannianEDistOf (scaleMetric (metricScalarAt g x) nk.Q_pos g)
        (nk.map (p, z)) (nk.map (p, 0)) ≤ ENNReal.ofReal (20 : ℝ) := by
    have hax := collar_axial_edist_le nk.cylinder _ nk.map nk.comparison rfl
      nk.eps_pos.le (by simp) nk.domain hslab p hz
    have hsqrt : Real.sqrt (1 + eps) ≤ 2 := by
      apply (Real.sqrt_le_iff).2
      constructor
      · norm_num
      · linarith [nk.eps_small]
    have habs : |z| ≤ 10 := abs_le.mpr hz
    exact hax.trans (ENNReal.ofReal_le_ofReal (by
      nlinarith [Real.sqrt_nonneg (1 + eps), abs_nonneg z]))
  have hbound := hband nk.cylinder (fun _ => nk.cylinder.metric 0)
    (fun _ => scaleMetric (metricScalarAt g x) nk.Q_pos g) nk.map
    (_root_.Set.univ ×ˢ _root_.Set.Ioo (-eps⁻¹) eps⁻¹) {0} (⌈eps⁻¹⌉₊) eps 20
    nk.comparison rfl nk.eps_pos.le (by linarith [nk.eps_small])
    (by simp) nk.domain hslab (by norm_num) haxis v hv w hw
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [edistOf_scale, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (by linarith : 0 ≤ D + 2 * 20)] at hreal
  apply (le_div_iff₀ (Real.sqrt_pos.mpr nk.Q_pos)).mpr
  change (riemannianEDistOf g v w).toReal * Real.sqrt (metricScalarAt g x) ≤ D + 40
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_spatial_neck_core_diameter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_spatial_neck_core_diameter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_spatial_neck_core_diameter ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_uniform_spatial_neck_core_diameter

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
