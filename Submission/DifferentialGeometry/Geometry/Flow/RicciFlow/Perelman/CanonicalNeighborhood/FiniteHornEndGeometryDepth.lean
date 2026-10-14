import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornDeepMinimizers
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ConeConvergence

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set _root_.Submission.Set _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Submission.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem exists_finiteHorn_end_geometry_depth :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (W : Type u) [MetricSpace W] [ChartedSpace ThreeSpace W]
      [IsManifold I3 ∞ W] [SigmaCompactSpace W], ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth →
      (∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
        ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) →
        hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
        Nonempty (RayApproximation H a b lo hi)) ∧
      Nonempty (EndAngles H) ∧
      ∀ angles : EndAngles H, ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
        ∀ s t : ℝ, s ∈ _root_.Set.Ioc 0 (_root_.Min.min a.length d) → t ∈ _root_.Set.Ioc 0 (_root_.Min.min b.length d) →
          endComparisonAngle a b s t ≤ angles.angle a b := by
  obtain ⟨H₀, hH₀, hsave⟩ := exists_no_endpoint_shortcut_depth_uniform_in_manifold.{u}
  refine ⟨H₀, hH₀, ?_⟩
  intro W _ _ _ _ g H hdepth
  have hno := hsave W g H hdepth
  obtain ⟨d, hd, hm⟩ := finiteHorn_end_angle_monotone_of_endRay_dist_lt_sum g H hno
  refine ⟨?_, finite_horn_end_angle_of_monotone H d hd hm, ?_⟩
  · obtain ⟨r, hr, happ⟩ := finiteHorn_ray_approximation_in_subend_of_endRay_dist_lt_sum g H hno 0
    refine ⟨r, hr, ?_⟩
    intro a b lo hi hlo hia hib hir
    obtain ⟨A, _⟩ := happ a b lo hi hlo hia hib hir
    exact ⟨A⟩
  · intro angles
    exact exists_d_endComparisonAngle_le_angle H hd hm angles

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_finiteHorn_end_geometry_depth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_finiteHorn_end_geometry_depth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_finiteHorn_end_geometry_depth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_finiteHorn_end_geometry_depth

def hornEndGeometryDepth : ℝ :=
  Classical.choose exists_finiteHorn_end_geometry_depth.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth

theorem hornEndGeometryDepth_pos : 0 < hornEndGeometryDepth.{u} :=
  (Classical.choose_spec exists_finiteHorn_end_geometry_depth.{u}).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth_pos

theorem hornEndGeometryDepth_spec
    (W : Type u) [MetricSpace W] [ChartedSpace ThreeSpace W]
    [IsManifold I3 ∞ W] [SigmaCompactSpace W]
    (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (hdepth : hornEndGeometryDepth.{u} ≤ H.collar_depth) :
    (∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
      ∀ lo hi : Fin 2 → ℝ, (∀ k, 0 < lo k) →
      hi 0 ≤ a.length → hi 1 ≤ b.length → (∀ k, hi k ≤ d) →
      Nonempty (RayApproximation H a b lo hi)) ∧
    Nonempty (EndAngles H) ∧
    ∀ angles : EndAngles H, ∃ d : ℝ, 0 < d ∧ ∀ a b : EndRay H.endpoint,
      ∀ s t : ℝ, s ∈ _root_.Set.Ioc 0 (_root_.Min.min a.length d) → t ∈ _root_.Set.Ioc 0 (_root_.Min.min b.length d) →
        endComparisonAngle a b s t ≤ angles.angle a b :=
  (Classical.choose_spec exists_finiteHorn_end_geometry_depth.{u}).2 W g H hdepth

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth_spec ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth_spec

noncomputable def hornDepthThreshold : ℝ := _root_.Max.max hornEndGeometryDepth.{u} 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornDepthThreshold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornDepthThreshold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornDepthThreshold ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornDepthThreshold

theorem hornEndGeometryDepth_le_hornDepthThreshold :
    hornEndGeometryDepth.{u} ≤ hornDepthThreshold.{u} := le_max_left _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth_le_hornDepthThreshold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth_le_hornDepthThreshold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth_le_hornDepthThreshold ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornEndGeometryDepth_le_hornDepthThreshold

theorem one_le_hornDepthThreshold : (1 : ℝ) ≤ hornDepthThreshold.{u} := le_max_right _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.one_le_hornDepthThreshold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.one_le_hornDepthThreshold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.one_le_hornDepthThreshold ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.one_le_hornDepthThreshold

theorem hornDepthThreshold_pos : 0 < hornDepthThreshold.{u} :=
  zero_lt_one.trans_le one_le_hornDepthThreshold.{u}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornDepthThreshold_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornDepthThreshold_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornDepthThreshold_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.hornDepthThreshold_pos

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
