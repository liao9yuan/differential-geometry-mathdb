import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import Submission.DifferentialGeometry.Geometry.Metric.Distance.Boundary
import Submission.DifferentialGeometry.Geometry.Comparison.Distance.Continuity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {eps t : ℝ} {x : M} {U : Set M}

theorem LocalCap.tube_map_mem_core_iff
    (cap : LocalCap S eps x t U) {z : Sphere 2} {a : ℝ} (ha : a ∈ _root_.Set.Icc (0 : ℝ) 1) :
    cap.tube_map (z, a) ∈ cap.core.carrier ↔ a = 0 := by
  have hsource : (z, a) ∈ cap.tube_map.source := cap.tube_domain ⟨mem_univ z, ha⟩
  have htube : cap.tube_map (z, a) ∈ cap.tube :=
    cap.tube_eq ▸ ⟨(z, a), ⟨mem_univ z, ha⟩, rfl⟩
  constructor
  · intro hcore
    have hboundary : cap.tube_map (z, a) ∈ frontier cap.core.carrier :=
      cap.overlap_eq ▸ ⟨hcore, htube⟩
    rw [← cap.inner_boundary] at hboundary
    obtain ⟨⟨w, b⟩, hb, heq⟩ := hboundary
    have hb0 : b = 0 := hb.2
    have hsource' : (w, b) ∈ cap.tube_map.source :=
      cap.tube_domain ⟨mem_univ w, by
        simpa only [hb0] using (show (0 : ℝ) ∈ _root_.Set.Icc 0 1 from ⟨le_rfl, zero_le_one⟩)⟩
    have heq' : (w, b) = (z, a) := by
      calc
        (w, b) = cap.tube_map.symm (cap.tube_map (w, b)) :=
          (cap.tube_map.left_inv' hsource').symm
        _ = cap.tube_map.symm (cap.tube_map (z, a)) := congrArg cap.tube_map.symm heq
        _ = (z, a) := cap.tube_map.left_inv' hsource
    exact (congrArg Prod.snd heq').symm.trans hb0
  · rintro rfl
    have hboundary : cap.tube_map (z, 0) ∈ frontier cap.core.carrier :=
      cap.inner_boundary ▸ ⟨(z, 0), ⟨mem_univ z, rfl⟩, rfl⟩
    rw [← cap.overlap_eq] at hboundary
    exact hboundary.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.tube_map_mem_core_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.tube_map_mem_core_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.tube_map_mem_core_iff ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.tube_map_mem_core_iff

variable [T2Space M] [PreconnectedSpace M]

theorem LocalCap.lt_metricDistance_of_pos_tube_coordinate
    (cap : LocalCap S eps x t U) (g : SmoothRiemannianMetric I3 M) {r : ℝ}
    (hdepth : ∀ y ∈ frontier cap.core.carrier, r ≤ metricDistance g x y)
    {z : Sphere 2} {a : ℝ} (ha : a ∈ _root_.Set.Ioc (0 : ℝ) 1) :
    r < metricDistance g x (cap.tube_map (z, a)) := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  let _ : RegularSpace M := inferInstance
  have hball : riemannianClosedBallOf g x r ⊆ cap.core.carrier :=
    Geometry.Metric.riemannianEDistOf_closedBall_subset_of_le_frontier_distance g
      cap.core.compact.isClosed cap.center_inside ENNReal.ofReal_ne_top (by
        intro y hy
        exact (ENNReal.ofReal_le_iff_le_toReal (riemannianEDistOf_ne_top g x y)).mpr
          (hdepth y hy))
  have hnot : cap.tube_map (z, a) ∉ cap.core.carrier := by
    rw [cap.tube_map_mem_core_iff ⟨ha.1.le, ha.2⟩]
    exact ha.1.ne'
  apply lt_of_not_ge
  intro hle
  have hr : 0 ≤ r := ENNReal.toReal_nonneg.trans hle
  exact hnot (hball ((ENNReal.le_ofReal_iff_toReal_le
    (riemannianEDistOf_ne_top g x (cap.tube_map (z, a))) hr).mpr hle))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.lt_metricDistance_of_pos_tube_coordinate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.lt_metricDistance_of_pos_tube_coordinate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.lt_metricDistance_of_pos_tube_coordinate ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.lt_metricDistance_of_pos_tube_coordinate

theorem LocalCap.exists_uniform_depth_on_tube_strip
    (cap : LocalCap S eps x t U) (g : SmoothRiemannianMetric I3 M) {r : ℝ}
    (hdepth : ∀ y ∈ frontier cap.core.carrier, r ≤ metricDistance g x y)
    {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ r' : ℝ, r < r' ∧ ∀ y ∈ cap.tube_map '' (_root_.Set.univ ×ˢ _root_.Set.Icc a 1),
      r' ≤ metricDistance g x y := by
  have hsource : _root_.Set.univ ×ˢ _root_.Set.Icc a 1 ⊆ cap.tube_map.source := by
    intro z hz
    exact cap.tube_domain ⟨hz.1, ha.le.trans hz.2.1, hz.2.2⟩
  have hcompact : IsCompact (cap.tube_map '' (_root_.Set.univ ×ˢ _root_.Set.Icc a 1)) :=
    (isCompact_univ.prod _root_.CompactIccSpace.isCompact_Icc).image_of_continuousOn
      (cap.tube_map.contMDiffOn_toFun.continuousOn.mono hsource)
  let z : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hnonempty : (cap.tube_map '' (_root_.Set.univ ×ˢ _root_.Set.Icc a 1)).Nonempty :=
    ⟨cap.tube_map (z, a), (z, a), ⟨mem_univ z, le_rfl, ha1⟩, rfl⟩
  have hcontinuous : Continuous (fun y => metricDistance g x y) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top g x y)).comp
      (continuous_riemannianEDist g x).continuousAt
  obtain ⟨y, hy, hmin⟩ := hcompact.exists_isMinOn hnonempty hcontinuous.continuousOn
  refine ⟨metricDistance g x y, ?_, hmin⟩
  obtain ⟨⟨w, b⟩, hb, rfl⟩ := hy
  exact cap.lt_metricDistance_of_pos_tube_coordinate g hdepth ⟨ha.trans_le hb.2.1, hb.2.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.exists_uniform_depth_on_tube_strip then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.exists_uniform_depth_on_tube_strip"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.exists_uniform_depth_on_tube_strip ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.LocalCap.exists_uniform_depth_on_tube_strip

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
