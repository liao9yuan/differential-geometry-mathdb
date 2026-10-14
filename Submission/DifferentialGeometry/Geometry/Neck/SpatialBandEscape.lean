import Submission.DifferentialGeometry.Geometry.Neck.SpatialUnitBandReturn
import Mathlib.Order.Filter.AtTopBot.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold _root_.Filter
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem tendsto_spatial_neck_midpoint_cocompact_of_avoids_earlier_band
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    [T2Space M] (g : SmoothRiemannianMetric I3 M) {eps : ℝ}
    (heps : eps ≤ 1 / 156000) (p : ℕ → M) (neck : ∀ n, SpatialNeck g eps (p n))
    (havoid : ∀ i j : ℕ, i < j →
      (neck j).map ((neck j).center, 3 / 2) ∉
        (neck i).map '' (_root_.Set.univ ×ˢ _root_.Set.Icc (1 : ℝ) 2)) :
    Tendsto (fun n => (neck n).map ((neck n).center, 3 / 2)) _root_.Filter.atTop (_root_.Filter.cocompact M) := by
  classical
  apply hasBasis_cocompact.tendsto_right_iff.mpr
  intro K hK
  by_contra h
  have hfreq : ∃ᶠ n in _root_.Filter.atTop, (neck n).map ((neck n).center, 3 / 2) ∈ K := by
    simpa only [_root_.Filter.not_eventually, _root_.Set.mem_compl_iff, _root_.Classical.not_not] using h
  obtain ⟨s, hs, hmem⟩ := _root_.Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨i, j, hij, hj⟩ := exists_spatial_neck_unit_band_return_in_compact g hK heps
    (fun n => p (s n)) (fun n => neck (s n)) hmem
  exact havoid (s i) (s j) (hs hij) hj

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_spatial_neck_midpoint_cocompact_of_avoids_earlier_band then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_spatial_neck_midpoint_cocompact_of_avoids_earlier_band"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_spatial_neck_midpoint_cocompact_of_avoids_earlier_band ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.tendsto_spatial_neck_midpoint_cocompact_of_avoids_earlier_band

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
