import Submission.DifferentialGeometry.Geometry.Comparison.Splitting.MetricApproximateLineLimit
import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle
import Mathlib.Topology.Instances.NNReal.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set _root_.Metric
open scoped _root_.Topology _root_.NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem exists_isometric_rays_of_approximate_rays_comparisonAngle_lower
    (f : ℕ → Fin 2 × ℝ≥0 → X) (p : X) (theta : ℝ)
    (hzero : ∀ i j, f i (j, 0) = p)
    (hdist : ∀ j : Fin 2, ∀ s t : ℝ≥0,
      _root_.Filter.Tendsto (fun i => _root_.Dist.dist (f i (j, s)) (f i (j, t))) _root_.Filter.atTop (𝓝 (_root_.Dist.dist s t)))
    (hangle : ∀ r : ℝ≥0, 0 < r → ∀ᶠ i in _root_.Filter.atTop,
      theta ≤ comparisonAngle r r (_root_.Dist.dist (f i (0, r)) (f i (1, r)))) :
    ∃ g : Fin 2 × ℝ≥0 → X,
      MapClusterPt g _root_.Filter.atTop f ∧
      (∀ j : Fin 2, Isometry (fun r => g (j, r))) ∧
      (∀ j : Fin 2, g (j, 0) = p) ∧
      ∀ r : ℝ≥0, 0 < r → theta ≤ comparisonAngle r r (_root_.Dist.dist (g (0, r)) (g (1, r))) := by
  have hbounded : ∀ z : Fin 2 × ℝ≥0, ∃ R : ℝ, ∀ i, _root_.Dist.dist (f i z) p ≤ R := by
    intro z
    have ht : _root_.Filter.Tendsto (fun i => _root_.Dist.dist (f i z) p) _root_.Filter.atTop (𝓝 (_root_.Dist.dist z.2 0)) := by
      simpa only [hzero] using hdist z.1 z.2 0
    obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto _ ht).subset_closedBall 0
    refine ⟨R, fun i => ?_⟩
    have h := hR (_root_.Set.mem_range_self i)
    change _root_.Dist.dist (_root_.Dist.dist (f i z) p) 0 ≤ R at h
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using h
  choose R hR using hbounded
  let B : Fin 2 × ℝ≥0 → Set X := fun z => _root_.Metric.closedBall p (R z)
  have hcompact : IsCompact (Set.pi _root_.Set.univ B) := isCompact_univ_pi (fun _ => _root_.ProperSpace.isCompact_closedBall _ _)
  obtain ⟨g, _, hg⟩ := hcompact.exists_mapClusterPt (f := _root_.Filter.atTop) (u := f) (by
    apply Filter.le_principal_iff.mpr
    change ∀ᶠ i in _root_.Filter.atTop, f i ∈ Set.pi _root_.Set.univ B
    exact Eventually.of_forall (fun i z _ => hR z i))
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · intro j
    apply Isometry.of_dist_eq
    intro s t
    have hgc := hg.continuousAt_comp
      ((continuous_apply (j, s)).dist (continuous_apply (j, t))).continuousAt
    exact eq_of_nhds_neBot (hgc.clusterPt.mono (hdist j s t))
  · intro j
    have hgc := hg.continuousAt_comp (continuous_apply (j, 0)).continuousAt
    exact isClosed_singleton.mem_of_mapClusterPt hgc (Eventually.of_forall (fun i => hzero i j))
  · intro r hr
    have hcont : Continuous (fun a : Fin 2 × ℝ≥0 → X =>
        comparisonAngle r r (_root_.Dist.dist (a (0, r)) (a (1, r)))) := by
      unfold comparisonAngle
      exact Real.continuous_arccos.comp
        ((continuous_const.sub (((continuous_apply (0, r)).dist
          (continuous_apply (1, r))).pow 2)).div_const _)
    have hgc := hg.continuousAt_comp hcont.continuousAt
    exact isClosed_Ici.mem_of_mapClusterPt hgc (hangle r hr)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Comparison.Toponogov.exists_isometric_rays_of_approximate_rays_comparisonAngle_lower then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Comparison.Toponogov.exists_isometric_rays_of_approximate_rays_comparisonAngle_lower"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Comparison.Toponogov.exists_isometric_rays_of_approximate_rays_comparisonAngle_lower ``Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.exists_isometric_rays_of_approximate_rays_comparisonAngle_lower

end DifferentialGeometry.Geometry.Comparison.Toponogov
